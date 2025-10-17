const std = @import("std");
const cst_mod = @import("cst.zig");
const ast_mod = @import("ast.zig");
const tir_mod = @import("tir.zig");
const lower = @import("lower.zig");
const lower_tir = @import("lower_tir.zig");
const checker = @import("checker.zig");
const Lexer = @import("lexer.zig").Tokenizer;
const Parser = @import("parser.zig").Parser;
const types = @import("types.zig");
const comp = @import("comptime.zig");
const mlir_codegen = @import("mlir_codegen.zig");
const mlir = @import("mlir_bindings.zig");
const compile = @import("compile.zig");
const module_graph = @import("module_graph.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;

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

    const prelude = [_][]const u8{
        "std/prelude.sr",
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
        self.context.resolver.enterPipeline(runner_ctx, runModuleForGraph);
        defer self.context.resolver.leavePipeline(runner_ctx);
        const type_info = try self.allocator.create(types.TypeInfo);
        type_info.* = types.TypeInfo.init(self.allocator, &self.context.type_store);
        var type_info_cleanup = true;
        defer if (type_info_cleanup) {
            type_info.deinit();
            self.allocator.destroy(type_info);
        };
        const module_id = self.next_module_id;
        self.next_module_id += 1;
        type_info.setModule(module_id);

        const filename = if (mode == .repl) "temp.sr" else filename_or_src;
        const file_id = try self.context.source_manager.add(filename);
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
        if (mode == .ast) {
            type_info_cleanup = false;
            return .{ .cst = cst_program, .ast = ast, .type_info = type_info, .module_id = module_id };
        }

        var chk = checker.Checker.init(self.allocator, &ast, self.context, self, type_info);
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

        // Resolve imports recursively and append their codegen (reuse resolver)
        try self.resolveImports(&ast, &gen, &self.context.resolver);

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

    fn resolveImports(
        self: *Pipeline,
        ast: *ast_mod.Ast,
        gen: *mlir_codegen.MlirCodegen,
        resolver: anytype,
    ) !void {
        // Resolve imports recursively and append their codegen (reuse resolver)
        var imports: std.ArrayList([]const u8) = .empty;
        for (prelude) |p| try imports.append(self.allocator, try self.allocator.dupe(u8, p));
        defer {
            for (imports.items) |s| self.allocator.free(s);
            imports.deinit(self.allocator);
        }
        try resolver.collectImportsFromAst(ast, &imports);
        var seen = std.StringHashMap(bool).init(self.allocator);
        defer seen.deinit();
        for (imports.items) |imp| {
            if ((try seen.getOrPut(imp)).found_existing) continue;
            const me = try resolver.ensureModule(".", imp, .tir);
            // Apply name mangling to imported module functions (and their internal calls)
            const pref = try computePrefix(self.allocator, imp);
            defer self.allocator.free(pref);
            const imported_tir = me.tirRef();
            try mangleTIR(self.allocator, imported_tir, imported_tir.instrs.strs, pref);
            // append TIR into same generator (emit into same module)
            const original_debug_flag = mlir_codegen.enable_debug_info;
            mlir_codegen.enable_debug_info = false;
            const imported_ast = me.astRef();
            _ = try gen.emitModule(imported_tir, self.context, imported_ast.exprs.locs, me.typeInfo());
            mlir_codegen.enable_debug_info = original_debug_flag;
            if (self.context.diags.anyErrors()) {
                return error.MlirCodegenFailed;
            }
        }
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

fn runModuleForGraph(
    ctx: *anyopaque,
    path: []const u8,
    mode: module_graph.LoadMode,
) anyerror!module_graph.ModuleGraph.Artifacts {
    const pipeline: *Pipeline = @ptrCast(@alignCast(ctx));
    return pipeline.runModuleArtifacts(path, mode);
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

fn mangleTIR(gpa: std.mem.Allocator, t: *tir_mod.TIR, strs: *cst_mod.StringInterner, prefix: []const u8) !void {
    // Map of old function name -> new name
    var rename = std.AutoHashMap(cst_mod.StrId, cst_mod.StrId).init(gpa);
    defer rename.deinit();
    // Gather functions and rename
    const funcs = t.funcs.func_pool.data.items;
    for (funcs) |fid| {
        const row = t.funcs.Function.get(fid);
        const old_name = row.name;
        const name_s = strs.get(old_name);
        const new_s = try std.fmt.allocPrint(gpa, "{s}_{s}", .{ prefix, name_s });
        defer gpa.free(new_s);
        const new_id = strs.intern(new_s);
        var new_row = row;
        new_row.name = new_id;
        t.funcs.Function.list.set(fid.toRaw(), new_row);
        try rename.put(old_name, new_id);
    }
    // Update call sites
    const blocks = t.funcs.block_pool.data.items;
    for (blocks) |bid| {
        const b = t.funcs.Block.get(bid);
        const instrs = t.instrs.instr_pool.slice(b.instrs);
        for (instrs) |iid| {
            const kind = t.instrs.index.kinds.items[iid.toRaw()];
            if (kind == .Call) {
                const row = t.instrs.get(.Call, iid);
                if (rename.get(row.callee)) |new_id| {
                    var new_row = row;
                    new_row.callee = new_id;
                    const idx = t.instrs.index.rows.items[iid.toRaw()];
                    t.instrs.Call.list.set(idx, new_row);
                }
            }
        }
    }
}
