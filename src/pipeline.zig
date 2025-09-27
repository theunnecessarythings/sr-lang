const std = @import("std");
const cst = @import("cst.zig");
const ast = @import("ast.zig");
const tir = @import("tir.zig");
const lower = @import("lower.zig");
const lower_tir = @import("lower_tir.zig");
const checker = @import("checker.zig");
const types = @import("types.zig");
const mlir_codegen = @import("mlir_codegen.zig");
const mlir = @import("mlir_bindings.zig");
const compile = @import("compile.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;
const ImportResolver = @import("import_resolver.zig").ImportResolver;
const ModuleEntry = @import("import_resolver.zig").ModuleEntry;

pub const Result = struct {
    hir: ast.Ast,
    type_info: *types.TypeInfo,
    module: tir.TIR,
    mlir_module: mlir.Module,
    gen: mlir_codegen.MlirCodegen,
};

pub const Pipeline = struct {
    allocator: std.mem.Allocator,
    diags: *Diagnostics,

    pub fn init(allocator: std.mem.Allocator, diags: *Diagnostics) Pipeline {
        return .{ .allocator = allocator, .diags = diags };
    }

    // Run with import resolution: loads imported modules and appends their codegen into one MLIR module
    pub fn runWithImports(
        self: *Pipeline,
        program: *cst.CST,
        base_dir: []const u8,
        link_args: []const []const u8,
    ) !Result {
        var lower_pass = lower.Lower.init(self.allocator, program, self.diags);
        var hir = try lower_pass.run();

        // Set up a resolver up front so checker can use it for module typing
        var resolver = ImportResolver.init(self.allocator, self.diags);
        defer resolver.deinit();

        var chk = checker.Checker.init(self.allocator, self.diags, &hir);
        defer chk.deinit();
        chk.setImportResolver(&resolver, base_dir);
        const type_info = try self.allocator.create(types.TypeInfo);
        type_info.* = try chk.runWithTypes();

        // Debug: print AST unit to verify statement order/content
        {
            var buf_ast: [1024]u8 = undefined;
            var errw_ast = std.fs.File.stderr().writer(&buf_ast);
            var w_ast = &errw_ast.interface;
            var ap = ast.AstPrinter.init(w_ast, &hir.exprs, &hir.stmts, &hir.pats);
            _ = w_ast.write("(debug) Root AST\n") catch {};
            ap.printUnit(&hir.unit) catch {};
        }

        var tir_lowerer = lower_tir.LowerTir.init(self.allocator, type_info, program.interner);
        // Compute module name -> prefix from root AST for mangling and install into lowerer
        var name_to_prefix = std.StringHashMap([]const u8).init(self.allocator);
        defer {
            var it = name_to_prefix.valueIterator();
            while (it.next()) |p| self.allocator.free(p.*);
            name_to_prefix.deinit();
        }
        try computeModulePrefixes(self.allocator, &hir, &name_to_prefix);
        var iter = name_to_prefix.iterator();
        while (iter.next()) |kv| {
            try tir_lowerer.setModulePrefix(kv.key_ptr.*, kv.value_ptr.*);
        }
        tir_lowerer.setImportResolver(&resolver, base_dir);
        const root_mod = try tir_lowerer.run(&hir);
        // Debug: dump TIR of root module before MLIR emission
        {
            var buf: [1024]u8 = undefined;
            var errw = std.fs.File.stderr().writer(&buf);
            var writer = &errw.interface;
            var tp = tir.TirPrinter.init(writer, &root_mod);
            _ = writer.write("(debug) Root TIR\n") catch {};
            tp.print() catch {};
        }

        const mlir_ctx = compile.initMLIR(self.allocator);
        var gen = mlir_codegen.MlirCodegen.init(self.allocator, mlir_ctx);
        var mlir_module = try gen.emitModule(&root_mod, &type_info.store);

        // Resolve imports recursively and append their codegen (reuse resolver)
        var imports: std.ArrayList([]const u8) = .empty;
        defer {
            for (imports.items) |s| self.allocator.free(s);
            imports.deinit(self.allocator);
        }
        try resolver.collectImportsFromAst(&hir, &imports);
        var seen = std.StringHashMap(bool).init(self.allocator);
        defer seen.deinit();
        for (imports.items) |imp| {
            if ((try seen.getOrPut(imp)).found_existing) continue;
            const me = try resolver.resolve(base_dir, imp, program.interner);
            // Apply name mangling to imported module functions (and their internal calls)
            const pref = name_to_prefix.get(imp) orelse computePrefix(self.allocator, imp) catch @panic("OOM");
            try mangleTIR(self.allocator, &me.tir, me.tir.instrs.strs, pref);
            // Debug: dump imported module TIR
            {
                var buf2: [1024]u8 = undefined;
                var errw2 = std.fs.File.stderr().writer(&buf2);
                var writer2 = &errw2.interface;
                var tp2 = tir.TirPrinter.init(writer2, &me.tir);
                _ = writer2.write("(debug) Imported TIR\n") catch {};
                tp2.print() catch {};
            }
            // append TIR into same generator (emit into same module)
            _ = try gen.emitModule(&me.tir, &me.type_info.store);
        }

        // finalize: print and pass pipeline + LLVM IR
        std.debug.print("Generated MLIR module:\n", .{});
        var op = mlir_module.getOperation();
        op.dump();
        try compile.run_passes(&gen.ctx, &mlir_module, true);
        try compile.convert_to_llvm_ir(mlir_module.handle, true, link_args);

        return .{ .hir = hir, .type_info = type_info, .module = root_mod, .mlir_module = mlir_module, .gen = gen };
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

fn computeModulePrefixes(gpa: std.mem.Allocator, a: *const ast.Ast, out: *std.StringHashMap([]const u8)) !void {
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

fn mangleTIR(gpa: std.mem.Allocator, t: *tir.TIR, strs: *cst.StringInterner, prefix: []const u8) !void {
    // Map of old function name -> new name
    var rename = std.AutoHashMap(cst.StrId, cst.StrId).init(gpa);
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
