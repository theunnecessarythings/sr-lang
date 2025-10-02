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
const mlir_codegen = @import("mlir_codegen.zig");
const mlir = @import("mlir_bindings.zig");
const compile = @import("compile.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;
const ImportResolver = @import("import_resolver.zig").ImportResolver;
const ModuleEntry = @import("import_resolver.zig").ModuleEntry;

pub const Result = struct {
    cst: ?cst_mod.CST = null,
    ast: ?ast_mod.Ast = null,
    tir: ?tir_mod.TIR = null,
    mlir_module: ?mlir.Module = null,
    gen: ?mlir_codegen.MlirCodegen = null,
    type_info: ?*types.TypeInfo = null,
};

pub const Pipeline = struct {
    allocator: std.mem.Allocator,
    context: *compile.Context,

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
        exec,
        run,

        repl,
    };

    pub fn init(allocator: std.mem.Allocator, context: *compile.Context) Pipeline {
        return .{ .allocator = allocator, .context = context };
    }

    // Run with import resolution: loads imported modules and appends their codegen into one MLIR module
    pub fn runWithImports(
        self: *Pipeline,
        filename_or_src: []const u8,
        link_args: []const []const u8,
        mode: Mode,
    ) anyerror!Result {
        const type_info = try self.allocator.create(types.TypeInfo);
        type_info.* = types.TypeInfo.init(self.allocator, &self.context.type_store);

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
            return .{ .type_info = type_info };
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
            return .{ .cst = cst_program, .type_info = type_info };
        }

        var lower_pass = lower.Lower.init(self.allocator, &cst_program, self.context);
        var ast = try lower_pass.run();
        if (self.context.diags.anyErrors()) {
            try self.context.diags.emitStyled(self.context, &writer.interface, true);
            return error.LoweringFailed;
        }
        if (mode == .ast) {
            return .{ .cst = cst_program, .ast = ast, .type_info = type_info };
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
            return .{ .cst = cst_program, .ast = ast, .type_info = type_info };
        }

        var tir_lowerer = lower_tir.LowerTir.init(self.allocator, self.context, self, type_info);
        defer tir_lowerer.deinit();
        var name_to_prefix = std.StringHashMap([]const u8).init(self.allocator);
        defer {
            var it = name_to_prefix.valueIterator();
            while (it.next()) |p| self.allocator.free(p.*);
            name_to_prefix.deinit();
        }
        try computeModulePrefixes(self.allocator, &ast, &name_to_prefix);
        var iter = name_to_prefix.iterator();
        while (iter.next()) |kv| {
            try tir_lowerer.setModulePrefix(kv.key_ptr.*, kv.value_ptr.*);
        }

        const root_mod = try tir_lowerer.run(&ast);

        if (self.context.diags.anyErrors()) {
            try self.context.diags.emitStyled(self.context, &writer.interface, true);
            return error.TirLoweringFailed;
        }
        if (mode == .tir) {
            return .{ .cst = cst_program, .ast = ast, .tir = root_mod, .type_info = type_info };
        }

        const mlir_ctx = compile.initMLIR(self.allocator);
        var gen = mlir_codegen.MlirCodegen.init(self.allocator, self.context, mlir_ctx);

        // Resolve imports recursively and append their codegen (reuse resolver)
        try self.resolveImports(&ast, &gen, &name_to_prefix, &self.context.resolver);

        var mlir_module = try gen.emitModule(&root_mod, self.context);
        // verify module
        if (!mlir_module.getOperation().verify()) {
            mlir_module.getOperation().dump();
            try self.context.diags.addError(.{ .file_id = file_id, .start = 0, .end = 0 }, .mlir_verification_failed, .{});
        }
        if (self.context.diags.anyErrors()) {
            try self.context.diags.emitStyled(self.context, &writer.interface, true);
            return error.MlirCodegenFailed;
        }
        if (mode == .mlir) {
            std.debug.print("Generated MLIR module:\n", .{});
            var op = mlir_module.getOperation();
            op.dump();
            return .{ .cst = cst_program, .ast = ast, .tir = root_mod, .mlir_module = mlir_module, .gen = gen, .type_info = type_info };
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
            return .{ .cst = cst_program, .ast = ast, .tir = root_mod, .mlir_module = mlir_module, .gen = gen, .type_info = type_info };
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
            return .{ .cst = cst_program, .ast = ast, .tir = root_mod, .mlir_module = mlir_module, .gen = gen, .type_info = type_info };
        }

        if (mode == .jit) {
            compile.runJit(mlir_module.handle);
            if (self.context.diags.anyErrors()) {
                try self.context.diags.emitStyled(self.context, &writer.interface, true);
                return error.JITFailed;
            }
            return .{ .cst = cst_program, .ast = ast, .tir = root_mod, .mlir_module = mlir_module, .gen = gen, .type_info = type_info };
        }
        // run
        compile.run();
        return .{ .ast = ast, .tir = root_mod, .mlir_module = mlir_module, .gen = gen, .cst = cst_program, .type_info = type_info };
    }

    fn resolveImports(
        self: *Pipeline,
        ast: *ast_mod.Ast,
        gen: *mlir_codegen.MlirCodegen,
        name_to_prefix: *std.StringHashMap([]const u8),
        resolver: *ImportResolver,
    ) !void {
        // Resolve imports recursively and append their codegen (reuse resolver)
        var imports: std.ArrayList([]const u8) = .empty;
        defer {
            for (imports.items) |s| self.allocator.free(s);
            imports.deinit(self.allocator);
        }
        try resolver.collectImportsFromAst(ast, &imports);
        var seen = std.StringHashMap(bool).init(self.allocator);
        defer seen.deinit();
        for (imports.items) |imp| {
            if ((try seen.getOrPut(imp)).found_existing) continue;
            const me = try resolver.resolve(".", imp, self);
            // Apply name mangling to imported module functions (and their internal calls)
            const pref = name_to_prefix.get(imp) orelse computePrefix(self.allocator, imp) catch @panic("OOM");
            try mangleTIR(self.allocator, &me.tir, me.tir.instrs.strs, pref);
            // append TIR into same generator (emit into same module)
            _ = try gen.emitModule(&me.tir, self.context);
            if (self.context.diags.anyErrors()) {
                return error.MlirCodegenFailed;
            }
        }
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

fn computeModulePrefixes(gpa: std.mem.Allocator, a: *const ast_mod.Ast, out: *std.StringHashMap([]const u8)) !void {
    const decls = a.exprs.decl_pool.slice(a.unit.decls);
    for (decls) |did| {
        const d = a.exprs.Decl.get(did.toRaw());
        if (a.exprs.index.kinds.items[d.value.toRaw()] != .Import) continue;
        if (d.pattern.isNone()) continue;
        const pid = d.pattern.unwrap();
        const pk = a.pats.index.kinds.items[pid.toRaw()];
        if (pk != .Binding) continue;
        const bind = a.pats.get(.Binding, pid);
        const irr = a.exprs.get(.Import, d.value);
        if (a.exprs.index.kinds.items[irr.expr.toRaw()] != .Literal) continue;
        const lit = a.exprs.get(.Literal, irr.expr);
        // literal must be string
        // Older AST carries kind; guard if available
        const s_full = a.exprs.strs.get(lit.value.unwrap());
        const imp = if (s_full.len >= 2 and s_full[0] == '"' and s_full[s_full.len - 1] == '"') s_full[1 .. s_full.len - 1] else s_full;
        const pref = try computePrefix(gpa, imp);
        const key = try gpa.dupe(u8, a.exprs.strs.get(bind.name));
        const gop = try out.getOrPut(key);
        if (gop.found_existing) {
            gpa.free(key);
            gpa.free(gop.value_ptr.*);
        }
        gop.value_ptr.* = pref;
    }
}

fn mangleTIR(gpa: std.mem.Allocator, t: *tir_mod.TIR, strs: *cst_mod.StringInterner, prefix: []const u8) !void {
    // Map of old function name -> new name
    var rename = std.AutoHashMap(cst_mod.StrId, cst_mod.StrId).init(gpa);
    defer rename.deinit();
    // Gather functions and rename
    const funcs = t.funcs.func_pool.data.items;
    for (funcs) |fid| {
        const row = t.funcs.Function.get(fid.toRaw());
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
        const b = t.funcs.Block.get(bid.toRaw());
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
