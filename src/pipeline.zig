const std = @import("std");
const cst_mod = @import("cst.zig");
const ast_mod = @import("ast.zig");
const tir_mod = @import("tir.zig");
const lower = @import("lower.zig");
const lower_tir = @import("lower_tir.zig");
const checker = @import("checker.zig");
const lexer_mod = @import("lexer.zig");
const Lexer = lexer_mod.Tokenizer;
const Loc = lexer_mod.Token.Loc;
const Parser = @import("parser.zig").Parser;
const types = @import("types.zig");
const comp = @import("comptime.zig");
const mlir_codegen = @import("mlir_codegen.zig");
const mlir = @import("mlir_bindings.zig");
const compile = @import("compile.zig");
const module_graph = @import("module_graph.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;

const PreludeSpec = module_graph.ModuleGraph.PreludeSpec;

pub const Result = struct {
    cst: ?cst_mod.CST = null,
    ast: ?ast_mod.Ast = null,
    tir: ?tir_mod.TIR = null,
    mlir_module: ?mlir.Module = null,
    gen: ?mlir_codegen.MlirCodegen = null,
    type_info: ?*types.TypeInfo = null,
    module_id: usize = 0,
};

pub const Pipeline = struct {
    allocator: std.mem.Allocator,
    context: *compile.Context,
    next_module_id: usize = 1,
    mlir_ctx: ?mlir.Context = null,

    const Mode = enum {
        lex,
        parse,
        ast,
        check,
        tir,
        mlir,
        passes,
        llvm_ir,
        llvm_passes,
        jit,
        compile,
        run,

        repl,
    };

    pub fn init(allocator: std.mem.Allocator, context: *compile.Context) Pipeline {
        return .{ .allocator = allocator, .context = context };
    }

    pub fn ensureMlirContext(self: *Pipeline) *mlir.Context {
        if (self.mlir_ctx) |*ctx| return ctx;
        self.mlir_ctx = compile.initMLIR(self.allocator);
        return &self.mlir_ctx.?;
    }

    pub const ComptimeBinding = union(enum) {
        type_param: struct { name: ast_mod.StrId, ty: types.TypeId },
        value_param: struct { name: ast_mod.StrId, ty: types.TypeId, value: comp.ComptimeValue },
    };

    pub fn evalComptimeExpr(
        self: *Pipeline,
        chk: *checker.Checker,
        ast_unit: *const ast_mod.Ast,
        expr: ast_mod.ExprId,
        result_ty: types.TypeId,
        bindings: []const ComptimeBinding,
    ) !comp.ComptimeValue {
        return lower_tir.evalComptimeExpr(
            self.allocator,
            self.context,
            self,
            chk.type_info,
            chk.type_info.module_id,
            chk,
            ast_unit,
            expr,
            result_ty,
            bindings,
        );
    }

    // Run with import resolution: loads imported modules and appends their codegen into one MLIR module
    pub fn runWithImports(
        self: *Pipeline,
        filename_or_src: []const u8,
        link_args: []const []const u8,
        mode: Mode,
    ) anyerror!Result {
        const runner_ctx: *anyopaque = @ptrCast(self);
        self.context.module_graph.enterPipeline(runner_ctx, runModuleForGraph);
        defer self.context.module_graph.leavePipeline(runner_ctx);
        const is_entry = self.context.module_graph.runner_depth == 1;
        const type_info = try self.allocator.create(types.TypeInfo);
        type_info.* = types.TypeInfo.init(self.allocator, &self.context.type_store);
        var type_info_cleanup = true;
        defer if (type_info_cleanup) {
            type_info.deinit();
            self.context.gpa.destroy(type_info);
        };
        const module_id = self.next_module_id;
        self.next_module_id += 1;
        type_info.setModule(module_id);

        const filename = if (mode == .repl) "temp.sr" else filename_or_src;
        const file_id = try self.context.source_manager.add(filename);
        const source_path = self.context.source_manager.get(file_id) orelse filename;
        const source = if (mode == .repl)
            filename_or_src
        else
            try self.context.source_manager.read(file_id);
        defer self.allocator.free(source);
        const source0 = try self.allocator.dupeZ(u8, source);

        var lexer = Lexer.init(source0, file_id, .semi);
        if (mode == .lex) {
            while (true) {
                const token = lexer.next();
                if (token.tag == .eof) break;
                const lexeme = source0[token.loc.start..token.loc.end];
                std.debug.print("{}({},{}) `{s}`\n", .{ token.tag, token.loc.start, token.loc.end, lexeme });
            }
            type_info_cleanup = false;
            return .{ .type_info = type_info, .module_id = module_id };
        }

        var parser = Parser.init(self.allocator, source0, file_id, self.context);
        const cst_program = try parser.parse();

        var buffer: [4096]u8 = undefined;
        var writer = std.fs.File.stdout().writer(&buffer);

        if (self.context.diags.anyErrors()) {
            try self.context.diags.emitStyled(self.context, &writer.interface, true);
            return error.ParseFailed;
        }
        if (mode == .parse) {
            type_info_cleanup = false;
            return .{ .cst = cst_program, .type_info = type_info, .module_id = module_id };
        }

        var lower_pass = lower.Lower.init(self.allocator, &cst_program, self.context);
        var ast = try lower_pass.run();
        ast.module_id = module_id;
        type_info.setModule(module_id);
        if (self.context.diags.anyErrors()) {
            try self.context.diags.emitStyled(self.context, &writer.interface, true);
            return error.LoweringFailed;
        }
        const package_issue = try self.verifyPackageDeclaration(&ast, file_id, source_path, is_entry);
        if (package_issue) {
            try self.context.diags.emitStyled(self.context, &writer.interface, true);
            return error.PackageValidationFailed;
        }

        var canonical_path_opt = try canonicalizePath(self.allocator, source_path);
        defer if (canonical_path_opt) |p| self.allocator.free(p);
        const module_path = canonical_path_opt orelse source_path;
        const base_dir = moduleBaseDir(module_path);

        var prelude_specs = std.ArrayList(PreludeSpec).init(self.allocator);
        defer prelude_specs.deinit();
        try self.context.module_graph.collectPreludeSpecsForModule(module_path, &prelude_specs);
        try self.injectPreludeImports(&ast, file_id, base_dir, prelude_specs.items);

        if (mode == .ast) {
            type_info_cleanup = false;
            return .{ .cst = cst_program, .ast = ast, .type_info = type_info, .module_id = module_id };
        }

        var chk = checker.Checker.init(self.allocator, &ast, self.context, self, type_info);
        chk.import_base_dir = base_dir;
        defer chk.deinit();
        try chk.run();
        if (self.context.diags.anyErrors()) {
            try self.context.diags.emitStyled(self.context, &writer.interface, true);
            std.debug.print("TypeCheckFailed for {s}\n", .{filename});
            return error.TypeCheckFailed;
        }
        if (mode == .check) {
            type_info_cleanup = false;
            return .{ .cst = cst_program, .ast = ast, .type_info = type_info, .module_id = module_id };
        }

        var tir_lowerer = lower_tir.LowerTir.init(self.allocator, self.context, self, type_info, module_id, &chk);
        defer tir_lowerer.deinit();
        var alias_info_map = std.StringHashMap(lower_tir.LowerTir.ModuleAliasInfo).init(self.allocator);
        defer {
            var it = alias_info_map.iterator();
            while (it.next()) |kv| {
                self.allocator.free(kv.value_ptr.prefix);
                self.allocator.free(kv.value_ptr.import_path);
            }
            alias_info_map.deinit();
        }
        try computeModulePrefixes(self.allocator, &ast, &alias_info_map);
        var iter = alias_info_map.iterator();
        while (iter.next()) |kv| {
            try tir_lowerer.setModuleAlias(kv.key_ptr.*, kv.value_ptr.*);
        }

        const root_mod = try tir_lowerer.run(&ast);

        if (self.context.diags.anyErrors()) {
            try self.context.diags.emitStyled(self.context, &writer.interface, true);
            return error.TirLoweringFailed;
        }
        if (mode == .tir) {
            type_info_cleanup = false;
            return .{ .cst = cst_program, .ast = ast, .tir = root_mod, .type_info = type_info, .module_id = module_id };
        }

        // Print Types
        // type_info.print();

        const mlir_ctx_ptr = self.ensureMlirContext();
        var gen = mlir_codegen.MlirCodegen.init(self.allocator, self.context, mlir_ctx_ptr.*);
        gen.resetDebugCaches();

        var dependencies = std.ArrayList(*module_graph.ModuleEntry).init(self.allocator);
        defer dependencies.deinit();

        tir_lowerer.import_base_dir = base_dir;
        try self.context.module_graph.loadDependencies(
            base_dir,
            module_path,
            &ast,
            .tir,
            &dependencies,
        );

        for (dependencies.items) |dep| {
            const original_debug_flag = mlir_codegen.enable_debug_info;
            mlir_codegen.enable_debug_info = false;
            const imported_ast = dep.astRef();
            _ = try gen.emitModule(dep.tirRef(), self.context, imported_ast.exprs.locs, dep.typeInfo());
            mlir_codegen.enable_debug_info = original_debug_flag;
            if (self.context.diags.anyErrors()) {
                return error.MlirCodegenFailed;
            }
        }

        var mlir_module = gen.emitModule(&root_mod, self.context, ast.exprs.locs, type_info) catch |err| {
            switch (err) {
                error.CompilationFailed => {
                    try self.context.diags.emitStyled(self.context, &writer.interface, true);
                    return error.MlirCodegenFailed;
                },
                else => return err,
            }
        };

        // var buf = std.array_list.Managed(u8).init(self.allocator);
        // defer buf.deinit();
        // var had_error = false;
        // var sink = mlir_codegen.PrintBuffer{ .list = &buf, .had_error = &had_error };
        // mlir_module.getOperation().print(mlir_codegen.printCallback, &sink);
        // if (!had_error) {
        //     const path = "temp.mlir";
        //     try std.fs.cwd().writeFile(.{ .data = sink.list.items, .sub_path = path });
        // }

        // verify module
        if (!mlir_module.getOperation().verify()) {
            const msg = gen.diagnostic_data.msg orelse "";
            try self.context.diags.addError(
                .{ .file_id = file_id, .start = 0, .end = 0 },
                .mlir_verification_failed,
                .{msg},
            );
        }
        if (self.context.diags.anyErrors()) {
            try self.context.diags.emitStyled(self.context, &writer.interface, true);
            return error.MlirCodegenFailed;
        }
        if (mode == .mlir) {
            std.debug.print("Generated MLIR module:\n", .{});
            var op = mlir_module.getOperation();
            op.dump();
            type_info_cleanup = false;
            return .{ .cst = cst_program, .ast = ast, .tir = root_mod, .mlir_module = mlir_module, .gen = gen, .type_info = type_info, .module_id = module_id };
        }

        try compile.run_passes(&gen.mlir_ctx, &mlir_module);
        if (self.context.diags.anyErrors()) {
            try self.context.diags.emitStyled(self.context, &writer.interface, true);
            return error.MlirPassesFailed;
        }
        if (mode == .passes) {
            std.debug.print("Transformed MLIR module:\n", .{});
            var op = mlir_module.getOperation();
            op.dump();
            type_info_cleanup = false;
            return .{ .cst = cst_program, .ast = ast, .tir = root_mod, .mlir_module = mlir_module, .gen = gen, .type_info = type_info, .module_id = module_id };
        }

        try compile.convert_to_llvm_ir(mlir_module.handle, true, link_args, switch (mode) {
            .llvm_ir => .llvm_ir,
            .llvm_passes => .llvm_passes,
            else => .compile,
        });
        if (self.context.diags.anyErrors()) {
            try self.context.diags.emitStyled(self.context, &writer.interface, true);
            return error.LLVMIRFailed;
        }
        if (mode == .llvm_ir or mode == .llvm_passes) {
            type_info_cleanup = false;
            return .{ .cst = cst_program, .ast = ast, .tir = root_mod, .mlir_module = mlir_module, .gen = gen, .type_info = type_info, .module_id = module_id };
        }
        if (mode == .compile) {
            type_info_cleanup = false;
            return .{ .cst = cst_program, .ast = ast, .tir = root_mod, .mlir_module = mlir_module, .gen = gen, .type_info = type_info, .module_id = module_id };
        }

        if (mode == .jit) {
            compile.runJit(mlir_module.handle);
            if (self.context.diags.anyErrors()) {
                try self.context.diags.emitStyled(self.context, &writer.interface, true);
                return error.JITFailed;
            }
            type_info_cleanup = false;
            return .{ .cst = cst_program, .ast = ast, .tir = root_mod, .mlir_module = mlir_module, .gen = gen, .type_info = type_info, .module_id = module_id };
        }
        // run
        compile.run();
        type_info_cleanup = false;
        return .{ .ast = ast, .tir = root_mod, .mlir_module = mlir_module, .gen = gen, .cst = cst_program, .type_info = type_info, .module_id = module_id };
    }

    fn runModuleArtifacts(
        self: *Pipeline,
        path: []const u8,
        mode: module_graph.LoadMode,
    ) anyerror!module_graph.ModuleGraph.Artifacts {
        const result = try self.runWithImports(path, &.{}, toPipelineMode(mode));
        return .{
            .cst = result.cst,
            .ast = result.ast,
            .tir = result.tir,
            .type_info = result.type_info,
            .module_id = result.module_id,
        };
    }
};

const PreludeAliasInfo = struct {
    alias_sid: ast_mod.StrId,
    decl_id: ast_mod.DeclId,
};

fn injectPreludeImports(
    self: *Pipeline,
    ast: *ast_mod.Ast,
    file_id: u32,
    base_dir: []const u8,
    specs: []const PreludeSpec,
) !void {
    if (specs.len == 0) return;

    var new_decl_ids = std.ArrayList(ast_mod.DeclId).init(self.allocator);
    defer new_decl_ids.deinit();

    var seen_exports = std.StringHashMap(void).init(self.allocator);
    defer {
        var it = seen_exports.keyIterator();
        while (it.next()) |name_ptr| self.allocator.free(name_ptr.*);
        seen_exports.deinit();
    }

    for (specs, 0..) |spec, idx| {
        const alias = try createPreludeAlias(self, ast, file_id, spec.path, idx);
        try new_decl_ids.append(alias.decl_id);
        try appendPreludeReexports(self, ast, file_id, base_dir, spec, alias, &seen_exports, &new_decl_ids);
    }

    const existing = ast.exprs.decl_pool.slice(ast.unit.decls);
    try new_decl_ids.appendSlice(existing);

    const range = ast.exprs.decl_pool.pushMany(ast.gpa, new_decl_ids.items);
    ast.unit.decls = range;
}

fn createPreludeAlias(
    self: *Pipeline,
    ast: *ast_mod.Ast,
    file_id: u32,
    import_path: []const u8,
    index: usize,
) !PreludeAliasInfo {
    const loc_id = ast.exprs.locs.add(ast.gpa, Loc.init(file_id, 0, 0));
    const alias_name = try std.fmt.allocPrint(self.allocator, "{s}_{d}", .{ module_graph.prelude_alias_prefix, index });
    defer self.allocator.free(alias_name);
    const alias_sid = ast.exprs.strs.intern(alias_name);
    const pattern_id = ast.pats.add(.Binding, .{ .name = alias_sid, .by_ref = false, .is_mut = false, .loc = loc_id });
    const path_sid = ast.exprs.strs.intern(import_path);
    const literal_id = ast.exprs.add(.Literal, .{ .kind = .string, .data = .{ .string = path_sid }, .loc = loc_id });
    const import_expr = ast.exprs.add(.Import, .{ .expr = literal_id, .loc = loc_id });
    const decl_id = ast.exprs.addDeclRow(.{
        .pattern = ast_mod.OptPatternId.some(pattern_id),
        .value = import_expr,
        .ty = ast_mod.OptExprId.none(),
        .method_path = ast_mod.OptRangeMethodPathSeg.none(),
        .flags = .{ .is_const = true },
        .loc = loc_id,
    });
    return .{ .alias_sid = alias_sid, .decl_id = decl_id };
}

fn appendPreludeReexports(
    self: *Pipeline,
    ast: *ast_mod.Ast,
    file_id: u32,
    base_dir: []const u8,
    spec: PreludeSpec,
    alias: PreludeAliasInfo,
    seen: *std.StringHashMap(void),
    out: *std.ArrayList(ast_mod.DeclId),
) !void {
    switch (spec.reexport) {
        .none => return,
        .all => {
            const entry = try self.context.module_graph.ensureModule(base_dir, spec.path, .tir);
            var it = entry.syms.keyIterator();
            while (it.next()) |name_ptr| {
                const name = name_ptr.*;
                try appendPreludeReexportDecl(self, ast, file_id, alias.alias_sid, name, seen, out);
            }
        },
        .symbols => |names| {
            for (names) |name| {
                try appendPreludeReexportDecl(self, ast, file_id, alias.alias_sid, name, seen, out);
            }
        },
    }
}

fn appendPreludeReexportDecl(
    self: *Pipeline,
    ast: *ast_mod.Ast,
    file_id: u32,
    alias_sid: ast_mod.StrId,
    symbol_name: []const u8,
    seen: *std.StringHashMap(void),
    out: *std.ArrayList(ast_mod.DeclId),
) !void {
    if (symbol_name.len == 0) return;
    if (std.mem.startsWith(u8, symbol_name, module_graph.prelude_alias_prefix)) return;

    const gop = try seen.getOrPut(symbol_name);
    if (gop.found_existing) return;
    gop.key_ptr.* = try self.allocator.dupe(u8, symbol_name);

    const loc_id = ast.exprs.locs.add(ast.gpa, Loc.init(file_id, 0, 0));
    const symbol_sid = ast.exprs.strs.intern(symbol_name);
    const pattern_id = ast.pats.add(.Binding, .{ .name = symbol_sid, .by_ref = false, .is_mut = false, .loc = loc_id });
    const alias_ident = ast.exprs.add(.Ident, .{ .name = alias_sid, .loc = loc_id });
    const field_expr = ast.exprs.add(.FieldAccess, .{
        .parent = alias_ident,
        .field = symbol_sid,
        .is_tuple = false,
        .loc = loc_id,
    });
    const decl_id = ast.exprs.addDeclRow(.{
        .pattern = ast_mod.OptPatternId.some(pattern_id),
        .value = field_expr,
        .ty = ast_mod.OptExprId.none(),
        .method_path = ast_mod.OptRangeMethodPathSeg.none(),
        .flags = .{ .is_const = true },
        .loc = loc_id,
    });
    try out.append(decl_id);
}

fn computePrefix(gpa: std.mem.Allocator, imp: []const u8) ![]const u8 {
    var buf: std.ArrayList(u8) = .empty;
    errdefer buf.deinit(gpa);
    try buf.appendSlice(gpa, "m$");
    for (imp) |c| {
        const keep = (c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z') or (c >= '0' and c <= '9');
        try buf.append(gpa, if (keep) c else '_');
    }
    return try buf.toOwnedSlice(gpa);
}

fn moduleBaseDir(path: []const u8) []const u8 {
    if (path.len == 0) return ".";
    if (std.mem.lastIndexOfScalar(u8, path, '/')) |idx| {
        if (idx == 0) return path[0..1];
        return path[0..idx];
    }
    if (std.mem.lastIndexOfScalar(u8, path, '\\')) |idx| {
        if (idx == 0) return path[0..1];
        return path[0..idx];
    }
    return ".";
}

fn runModuleForGraph(
    ctx: *anyopaque,
    path: []const u8,
    mode: module_graph.LoadMode,
) anyerror!module_graph.ModuleGraph.Artifacts {
    const pipeline: *Pipeline = @ptrCast(@alignCast(ctx));
    return pipeline.runModuleArtifacts(path, mode);
}

fn packageLocOrDefault(ast: *const ast_mod.Ast, file_id: u32) Loc {
    if (!ast.unit.package_loc.isNone()) {
        const loc_id = ast.unit.package_loc.unwrap();
        return ast.exprs.locs.get(loc_id);
    }
    return Loc.init(file_id, 0, 0);
}

fn namesEqual(a: []const u8, b: []const u8) bool {
    return std.mem.eql(u8, a, b);
}

fn canonicalizePath(
    allocator: std.mem.Allocator,
    path: []const u8,
) !?[]u8 {
    return std.fs.cwd().realpathAlloc(allocator, path) catch |err| switch (err) {
        error.FileNotFound, error.AccessDenied => return null,
        else => return err,
    };
}

fn declareName(ast: *const ast_mod.Ast) ?[]const u8 {
    if (ast.unit.package_name.isNone()) return null;
    const sid = ast.unit.package_name.unwrap();
    return ast.exprs.strs.get(sid);
}

fn verifyPackageDeclaration(
    self: *Pipeline,
    ast: *const ast_mod.Ast,
    file_id: u32,
    source_path: []const u8,
    is_entry: bool,
) !bool {
    var had_error = false;
    const declared_name = declareName(ast);
    const pkg_loc = packageLocOrDefault(ast, file_id);

    if (is_entry) {
        if (declared_name) |decl| {
            if (!namesEqual(decl, "main")) {
                try self.context.diags.addError(pkg_loc, .entry_package_not_main, .{decl});
                return true;
            }
        } else {
            try self.context.diags.addError(pkg_loc, .entry_package_missing, .{});
            return true;
        }
    }

    var canonical_path_opt = try canonicalizePath(self.allocator, source_path);
    defer if (canonical_path_opt) |p| self.allocator.free(p);

    const lookup_path = canonical_path_opt orelse source_path;
    if (self.context.module_graph.findModuleByPath(lookup_path)) |match| {
        const expected = self.context.module_graph.config.discovery.expectedPackageName(match.key);
        if (declared_name) |decl| {
            if (!namesEqual(decl, expected)) {
                if (!is_entry or !namesEqual(decl, "main")) {
                    try self.context.diags.addError(pkg_loc, .package_mismatch, .{ expected, decl });
                    had_error = true;
                }
            }
        } else {
            try self.context.diags.addError(pkg_loc, .package_missing_declaration, .{ expected });
            had_error = true;
        }
    }

    return had_error;
}

fn toPipelineMode(mode: module_graph.LoadMode) Pipeline.Mode {
    return switch (mode) {
        .lex => .lex,
        .parse => .parse,
        .ast => .ast,
        .check => .check,
        .tir => .tir,
    };
}

fn computeModulePrefixes(
    gpa: std.mem.Allocator,
    a: *const ast_mod.Ast,
    out: *std.StringHashMap(lower_tir.LowerTir.ModuleAliasInfo),
) !void {
    const decls = a.exprs.decl_pool.slice(a.unit.decls);
    for (decls) |did| {
        const d = a.exprs.Decl.get(did);
        if (a.exprs.index.kinds.items[d.value.toRaw()] != .Import) continue;
        if (d.pattern.isNone()) continue;
        const pid = d.pattern.unwrap();
        const pk = a.pats.index.kinds.items[pid.toRaw()];
        if (pk != .Binding) continue;
        const bind = a.pats.get(.Binding, pid);
        const irr = a.exprs.get(.Import, d.value);
        if (a.exprs.index.kinds.items[irr.expr.toRaw()] != .Literal) continue;
        const lit = a.exprs.get(.Literal, irr.expr);
        if (lit.kind != .string) continue;
        const sid = switch (lit.data) {
            .string => |str_id| str_id,
            else => continue,
        };
        const imp = a.exprs.strs.get(sid);
        const pref = try computePrefix(gpa, imp);
        const path = try gpa.dupe(u8, imp);
        const key = try gpa.dupe(u8, a.exprs.strs.get(bind.name));
        const gop = try out.getOrPut(key);
        if (gop.found_existing) {
            gpa.free(key);
            gpa.free(gop.value_ptr.prefix);
            gpa.free(gop.value_ptr.import_path);
        }
        gop.value_ptr.* = .{
            .prefix = pref,
            .import_path = path,
        };
    }
}
