const std = @import("std");
const cst_mod = @import("cst.zig");
const ast_mod = @import("ast.zig");
const tir_mod = @import("tir.zig");
const lower_to_ast = @import("lower_to_ast.zig");
const lower_tir = @import("lower_tir.zig");
const checker = @import("checker.zig");
const lexer_mod = @import("lexer.zig");
const parser_mod = @import("parser.zig");
const types = @import("types.zig");
const comp = @import("comptime.zig");
const interpreter = @import("interpreter.zig");
const codegen = @import("codegen_main.zig");
const mlir = @import("mlir_bindings.zig");
const compile = @import("compile.zig");
const tir_liveness = @import("tir_liveness.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;
const CompilationUnit = @import("package.zig").CompilationUnit;

pub const Result = struct {
    compilation_unit: ?CompilationUnit,
    mlir_module: ?mlir.Module = null,
    gen: ?codegen.Codegen = null,
    test_count: usize = 0,
};

pub const ProgressStage = enum { parsing, lowering_ast, type_checking, lowering_tir, mlir_codegen, llvm_codegen, count };
const stage_names = [_][]const u8{ "Parsing", "Lowering AST", "Type checking", "Lowering to TIR", "MLIR codegen", "LLVM codegen" };
pub fn stageName(s: ProgressStage) []const u8 {
    return stage_names[@intFromEnum(s)];
}

pub const ProgressReporter = struct {
    callback: *const fn (?*anyopaque, ProgressStage, usize, usize) void,
    context: ?*anyopaque,
    pub fn report(self: *ProgressReporter, s: ProgressStage) void {
        self.callback(self.context, s, @intFromEnum(s) + 1, @intFromEnum(ProgressStage.count));
    }
};

pub const Pipeline = struct {
    gpa: std.mem.Allocator,
    context: *compile.Context,
    mlir_ctx: ?mlir.Context = null,
    tir_prune_unused: bool = true,
    tir_warn_unused: bool = false,
    debug_info: bool = false,

    pub const Mode = enum { lex, parse, ast, check, tir, tir_liveness, mlir, passes, llvm_ir, llvm_passes, jit, compile, run, test_mode, interpret, repl };

    /// Represents compile-time bindings injected into the interpreter.
    pub const ComptimeBinding = union(enum) {
        type_param: struct { name: ast_mod.StrId, ty: types.TypeId },
        value_param: struct { name: ast_mod.StrId, ty: types.TypeId, value: comp.ComptimeValue },
    };

    pub fn init(allocator: std.mem.Allocator, context: *compile.Context) Pipeline {
        return .{ .gpa = allocator, .context = context };
    }
    pub fn ensureMlirContext(self: *Pipeline) *mlir.Context {
        if (self.mlir_ctx) |*c| return c;
        self.mlir_ctx = compile.initMLIR(self.gpa);
        return &self.mlir_ctx.?;
    }

    pub fn run(self: *Pipeline, src_or_path: []const u8, link_args: []const []const u8, mode: Mode, progress: ?*ProgressReporter, opt_level: ?[]const u8) !Result {
        const fname = if (mode == .repl) "temp.sr" else src_or_path;
        const fid = try self.context.source_manager.add(fname);
        const src = if (mode == .repl) src_or_path else try self.context.source_manager.read(fid);
        defer self.gpa.free(src);
        const src_z = try self.gpa.dupeZ(u8, src);

        if (progress) |r| r.report(.parsing);
        if (mode == .lex) return self.runLexer(src_z, fid);

        // parsing setup
        var parser = parser_mod.Parser.init(self.gpa, src_z, fid, self.context.diags, self.context);
        const main_th = try std.Thread.spawn(.{}, parser_mod.Parser.run, .{&parser});
        self.context.compilation_unit.mutex.lock();
        try self.context.parse_worklist.append(self.gpa, .{ .path = fname, .file_id = fid, .thread = main_th, .diags = self.context.diags, .parser = &parser });
        self.context.compilation_unit.mutex.unlock();

        // main parse loop
        try self.processParseWorklist();
        self.context.parse_worklist.deinit(self.gpa);

        if (self.context.diags.anyErrors()) return error.ParseFailed;
        if (mode == .parse) return .{ .compilation_unit = self.context.compilation_unit };

        // AST lowering
        if (progress) |r| r.report(.lowering_ast);
        try self.runAstLowering();

        // Cycle detection
        if (try self.checkImportCycles()) return error.CycleDetected;
        if (self.context.diags.anyErrors()) return error.LoweringFailed;
        if (mode == .ast) return .{ .compilation_unit = self.context.compilation_unit };

        // Type checking
        if (progress) |r| r.report(.type_checking);
        var chk = checker.Checker.init(self.gpa, self.context, self);
        defer chk.deinit();

        // Need to recompute dep levels after AST phase
        var dep_lvls = try compile.computeDependencyLevels(self.gpa, &self.context.compilation_unit, self.context.interner, self.context.source_manager);
        defer dep_lvls.deinit();
        try chk.run(&dep_lvls);

        if (self.context.diags.anyErrors()) return error.TypeCheckFailed;
        if (mode == .check) return .{ .compilation_unit = self.context.compilation_unit };

        if (mode == .interpret) {
            try runInterpreterStage(self);
            return .{ .compilation_unit = self.context.compilation_unit };
        }

        // TIR Lowering
        if (progress) |r| r.report(.lowering_tir);
        var tir_low = lower_tir.LowerTir.init(self.gpa, self.context, self, &chk, mode == .test_mode);
        defer tir_low.deinit();
        _ = tir_low.run(&dep_lvls) catch |e| return e;
        const t_count = if (mode == .test_mode) tir_low.test_funcs.items.len else 0;

        if (self.context.diags.anyErrors()) return error.TirLoweringFailed;
        if (self.tir_prune_unused) try @import("tir_prune.zig").pruneUnusedFunctions(self.gpa, self.context, &self.context.compilation_unit, .{ .warn_unused = self.tir_warn_unused });

        if (mode == .tir or mode == .tir_liveness) return self.handleTirMode(mode, t_count);

        // MLIR Codegen
        if (progress) |r| r.report(.mlir_codegen);
        codegen.enable_debug_info = self.debug_info;
        var gen = codegen.Codegen.init(self.gpa, self.context, self.ensureMlirContext(), false);
        gen.resetDebugCaches();

        var mod = gen.emit(&dep_lvls) catch |e| return if (e == error.CompilationFailed) error.MlirCodegenFailed else e;
        try self.dumpMlir(mod, "out/temp.mlir");

        if (!mod.getOperation().verify()) try self.context.diags.addError(.{ .file_id = fid, .start = 0, .end = 0 }, .mlir_verification_failed, .{gen.diagnostic_data.msg orelse ""});
        if (self.context.diags.anyErrors()) return error.MlirCodegenFailed;

        if (gen.has_triton_fns) try self.runTritonPipeline(&dep_lvls);

        if (mode == .mlir) {
            mod.getOperation().dump();
            return .{ .compilation_unit = self.context.compilation_unit, .mlir_module = mod, .gen = gen, .test_count = t_count };
        }

        try compile.run_passes(&gen.mlir_ctx, &mod);
        if (self.context.diags.anyErrors()) return error.MlirPassesFailed;
        if (mode == .passes) {
            mod.getOperation().dump();
            return .{ .compilation_unit = self.context.compilation_unit, .mlir_module = mod, .gen = gen, .test_count = t_count };
        }

        // LLVM Codegen
        if (progress) |r| r.report(.llvm_codegen);
        const lmode: compile.Mode = switch (mode) {
            .llvm_ir => .llvm_ir,
            .llvm_passes => .llvm_passes,
            .test_mode => .compile,
            else => .compile,
        };
        try compile.convert_to_llvm_ir(mod.handle, link_args, lmode, opt_level, self.debug_info);

        if (self.context.diags.anyErrors()) return error.LLVMIRFailed;
        if (mode == .jit) {
            compile.runJit(mod.handle);
            if (self.context.diags.anyErrors()) return error.JITFailed;
        }
        return .{ .compilation_unit = self.context.compilation_unit, .mlir_module = mod, .gen = gen, .test_count = t_count };
    }

    fn runLexer(_: *Pipeline, src: [:0]const u8, fid: u32) !Result {
        var lex = lexer_mod.Tokenizer.init(src, fid, .semi);
        while (true) {
            const tok = lex.next();
            if (tok.tag == .eof) break;
            std.debug.print("{}({},{}) `{s}`\n", .{ tok.tag, tok.loc.start, tok.loc.end, src[tok.loc.start..tok.loc.end] });
        }
        return .{ .compilation_unit = null };
    }

    fn processParseWorklist(self: *Pipeline) !void {
        var idx: usize = 0;
        while (true) {
            self.context.compilation_unit.mutex.lock();
            if (idx >= self.context.parse_worklist.items.len) {
                self.context.compilation_unit.mutex.unlock();
                break;
            }
            const work = self.context.parse_worklist.items[idx];
            self.context.compilation_unit.mutex.unlock();

            work.thread.join();
            if (idx > 0) {
                const no_note: u32 = 0xFFFF_FFFF;
                const note_offset: u32 = @intCast(self.context.diags.notes.items.len);
                for (work.diags.notes.items) |note| {
                    var n = note;
                    if (n.next_note != no_note) n.next_note += note_offset;
                    try self.context.diags.notes.append(self.gpa, n);
                }
                for (work.diags.messages.items) |message| {
                    var m = message;
                    if (m.first_note != no_note) m.first_note += note_offset;
                    try self.context.diags.messages.append(self.gpa, m);
                }
            }

            const failed = work.diags.anyErrors();
            if (!failed and self.context.load_imports) try self.scanImports(work);
            if (!failed) try self.registerPackageSource(work);
            idx += 1;
        }
    }

    fn scanImports(self: *Pipeline, work: anytype) !void {
        const decls = work.parser.cst_u.exprs.decl_pool.slice(work.parser.cst_u.program.top_decls);
        for (decls) |did| {
            const decl = work.parser.cst_u.exprs.Decl.get(did);
            if (work.parser.cst_u.kind(decl.rhs) != .Import) continue;

            const imp = work.parser.cst_u.exprs.get(.Import, decl.rhs);
            const imp_name = work.parser.cst_u.exprs.strs.get(imp.path);
            const resolved = compile.resolveImportPath(self.gpa, self.context.source_manager, work.file_id, imp_name) catch {
                _ = self.context.diags.addError(work.parser.cst_u.exprs.locs.get(imp.loc), .import_not_found, .{}) catch {};
                continue;
            };
            defer self.gpa.free(resolved);

            const imp_fid = try self.context.source_manager.add(resolved);
            const sm_path = self.context.source_manager.get(imp_fid).?;

            // Update CST path
            var row = work.parser.cst_u.exprs.table(.Import).get(work.parser.cst_u.exprs.index.rows.items[decl.rhs.toRaw()]);
            row.path = self.context.interner.intern(sm_path);
            work.parser.cst_u.exprs.table(.Import).set(work.parser.cst_u.exprs.index.rows.items[decl.rhs.toRaw()], row);

            try self.queueImportParse(imp_fid, sm_path);
            try self.context.compilation_unit.addDependency(work.file_id, self.context.interner.intern(sm_path));
        }
    }

    fn queueImportParse(self: *Pipeline, fid: u32, path: []const u8) !void {
        self.context.compilation_unit.mutex.lock();
        defer self.context.compilation_unit.mutex.unlock();

        var exists = false;
        var it = self.context.compilation_unit.packages.iterator();
        while (it.next()) |pkg| if (pkg.value_ptr.sources.contains(path)) {
            exists = true;
            break;
        };
        if (!exists) for (self.context.parse_worklist.items) |i| if (i.file_id == fid) {
            exists = true;
            break;
        };

        if (!exists) {
            const src = try self.context.source_manager.read(fid);
            const src_z = try self.gpa.dupeZ(u8, src);
            self.gpa.free(src);
            const diag = try self.gpa.create(Diagnostics);
            diag.* = Diagnostics.init(self.gpa, self.context.type_store, self.context.interner);
            const parser = try self.gpa.create(parser_mod.Parser);
            parser.* = parser_mod.Parser.init(self.gpa, src_z, fid, diag, self.context);
            try self.context.parse_worklist.append(self.gpa, .{ .path = path, .file_id = fid, .thread = try std.Thread.spawn(.{}, parser_mod.Parser.run, .{parser}), .diags = diag, .parser = parser });
        }
    }

    fn registerPackageSource(self: *Pipeline, work: anytype) !void {
        self.context.compilation_unit.mutex.lock();
        defer self.context.compilation_unit.mutex.unlock();
        const pname = self.context.interner.get(work.parser.cst_u.program.package_name.unwrap());
        const res = try self.context.compilation_unit.packages.getOrPut(self.gpa, pname);
        if (!res.found_existing) {
            const k = try self.gpa.dupe(u8, pname);
            res.key_ptr.* = k;
            res.value_ptr.* = .{ .gpa = self.gpa, .name = k, .source_manager = self.context.source_manager, .sources = .{} };
        }
        try res.value_ptr.sources.put(self.gpa, work.path, .{ .file_id = work.file_id, .cst = work.parser.cst_u, .ast = null, .tir = null, .type_info = null });
    }

    fn runAstLowering(self: *Pipeline) !void {
        var pkg_iter = self.context.compilation_unit.packages.iterator();
        var threads = std.ArrayList(struct { std.Thread, *lower_to_ast.Lower, []const u8, []const u8 }){};
        defer threads.deinit(self.gpa);

        while (pkg_iter.next()) |pkg| {
            var src_it = pkg.value_ptr.sources.iterator();
            while (src_it.next()) |u| {
                const lp = try self.gpa.create(lower_to_ast.Lower);
                lp.* = try lower_to_ast.Lower.init(self.gpa, &u.value_ptr.cst.?, self.context, u.value_ptr.file_id);
                const t = try std.Thread.spawn(.{}, struct {
                    fn run(l: *lower_to_ast.Lower) !void {
                        try l.runLower();
                    }
                }.run, .{lp});
                try threads.append(self.gpa, .{ t, lp, pkg.key_ptr.*, u.key_ptr.* });
            }
        }
        for (threads.items) |t| {
            t.@"0".join();
            self.context.compilation_unit.mutex.lock();
            if (self.context.compilation_unit.packages.getPtr(t.@"2")) |p| {
                if (p.sources.getPtr(t.@"3")) |s| s.ast = t.@"1".ast_unit;
            }
            self.context.compilation_unit.mutex.unlock();
            for (t.@"1".dependencies.items) |d| try self.context.compilation_unit.addDependency(t.@"1".file_id, d);
            t.@"1".dependencies.deinit(self.gpa);
            self.gpa.destroy(t.@"1");
        }
    }

    fn checkImportCycles(self: *Pipeline) !bool {
        var cycles = try compile.detectImportCycles(self.gpa, &self.context.compilation_unit, self.context.interner, self.context.source_manager);
        defer cycles.deinit();
        if (cycles.cycles.items.len == 0) return false;

        for (cycles.cycles.items) |cy| {
            var buf = std.ArrayList(u8){};
            defer buf.deinit(self.gpa);
            for (cy.items, 0..) |id, i| {
                if (i > 0) try buf.appendSlice(self.gpa, " -> ");
                try buf.appendSlice(self.gpa, self.context.source_manager.get(id) orelse "?");
            }
            _ = self.context.diags.addError(.init(cy.items[0], 0, 0), .import_cycle_detected, .{self.context.interner.get(self.context.interner.intern(buf.items))}) catch {};
        }
        return true;
    }

    fn handleTirMode(self: *Pipeline, mode: Mode, t_count: usize) !Result {
        if (mode == .tir_liveness) {
            var pi = self.context.compilation_unit.packages.iterator();
            while (pi.next()) |p| {
                var si = p.value_ptr.sources.iterator();
                while (si.next()) |u| if (u.value_ptr.tir) |t| try tir_liveness.dump(self.gpa, t);
            }
        }
        return .{ .compilation_unit = self.context.compilation_unit, .test_count = t_count };
    }

    fn runTritonPipeline(self: *Pipeline, deps: *compile.DependencyLevels) !void {
        var tgen = codegen.Codegen.init(self.gpa, self.context, &self.mlir_ctx.?, true);
        defer tgen.deinit();
        var tmod = tgen.emitTritonModule(deps) catch |e| return if (e == error.CompilationFailed) error.MlirCodegenFailed else e;

        try self.dumpMlir(tmod, "out/triton_kernels.mlir");

        // Arena for driver args to avoid manual cleanup of multiple strings
        var arena = std.heap.ArenaAllocator.init(self.gpa);
        defer arena.deinit();
        const aa = arena.allocator();
        var args = std.ArrayList([]const u8){};
        defer args.deinit(self.gpa);

        try args.append(self.gpa, "third-party/triton/build/cmake.linux-x86_64-cpython-3.13/bin/triton_mlir_driver");
        try args.append(self.gpa, try std.fmt.allocPrint(aa, "--input={s}", .{"out/triton_kernels.mlir"}));
        try args.append(self.gpa, try std.fmt.allocPrint(aa, "--emit-ptx={s}", .{"out/triton_kernels.ptx"}));

        var mop = tmod.getOperation();
        if (getStrAttr(&mop, "ttg.target")) |s| if (std.mem.startsWith(u8, s, "cuda:")) try args.append(self.gpa, try std.fmt.allocPrint(aa, "--sm={s}", .{s["cuda:".len..]}));
        if (getIntAttr(&mop, "ttg.num-warps")) |v| try args.append(self.gpa, try std.fmt.allocPrint(aa, "--num-warps={d}", .{v}));
        if (getIntAttr(&mop, "ttg.threads-per-warp")) |v| try args.append(self.gpa, try std.fmt.allocPrint(aa, "--threads-per-warp={d}", .{v}));
        if (getIntAttr(&mop, "ttg.ptx-version")) |v| try args.append(self.gpa, try std.fmt.allocPrint(aa, "--ptx-version={d}", .{v}));
        if (getIntAttr(&mop, "ttg.num-ctas")) |v|
            try args.append(self.gpa, try std.fmt.allocPrint(aa, "--num-ctas={d}", .{v}))
        else
            try args.append(self.gpa, "--num-ctas=1");

        var child = std.process.Child.init(args.items, self.gpa);
        child.cwd = ".";
        const term = try child.spawnAndWait();
        switch (term) {
            .Exited => |code| if (code != 0) return error.TritonDriverFailed,
            else => return error.TritonDriverFailed,
        }
    }

    fn dumpMlir(self: *Pipeline, mod: mlir.Module, path: []const u8) !void {
        var buf = std.array_list.Managed(u8).init(self.gpa);
        defer buf.deinit();
        var err = false;
        var sink = codegen.PrintBuffer{ .list = &buf, .had_error = &err };
        mod.getOperation().print(codegen.printCallback, &sink);
        if (!err) {
            std.fs.cwd().makePath("out") catch |e| if (e != error.PathAlreadyExists) return e;
            try std.fs.cwd().writeFile(.{ .data = sink.list.items, .sub_path = path });
        }
    }
};

fn getStrAttr(op: *mlir.Operation, name: []const u8) ?[]const u8 {
    const a = op.getDiscardableAttributeByName(.from(name));
    return if (!a.isNull() and a.isAString()) a.stringAttrGetValue().toSlice() else null;
}
fn getIntAttr(op: *mlir.Operation, name: []const u8) ?i64 {
    const a = op.getDiscardableAttributeByName(.from(name));
    return if (!a.isNull() and a.isAInteger()) a.integerAttrGetValueInt() else null;
}

fn runInterpreterStage(self: *Pipeline) !void {
    var found = false;
    var pkg_iter = self.context.compilation_unit.packages.iterator();
    while (pkg_iter.next()) |pkg| {
        var src_iter = pkg.value_ptr.sources.iterator();
        while (src_iter.next()) |unit| if (unit.value_ptr.ast) |ast| {
            found = (try interpretAstUnit(self, ast)) or found;
        };
    }
    if (!found) std.debug.print("Interpreter stage: no comptime blocks found in ASTs\n", .{});
}

fn interpretAstUnit(self: *Pipeline, ast: *ast_mod.Ast) !bool {
    var interp = try interpreter.Interpreter.init(self.gpa, ast, null, null, null, undefined);
    defer interp.deinit();
    var found = false;
    for (ast.exprs.decl_pool.slice(ast.unit.decls)) |did| {
        const decl = ast.exprs.Decl.get(did);
        var res = interp.evalExpr(decl.value) catch |e| switch (e) {
            error.UnsupportedExpr, error.InvalidStatement => continue,
            else => return e,
        };
        found = true;
        if (!decl.pattern.isNone()) if (ast.kind(decl.pattern.unwrap()) == .Binding) try interp.setBinding(ast.pats.get(.Binding, decl.pattern.unwrap()).name, try interp.cloneValue(res));
        std.debug.print("Interpreter: decl {d} -> ", .{did.toRaw()});
        printComptimeValue(&res);
        std.debug.print("\n", .{});
        res.destroy(self.gpa);
    }
    return found;
}

fn printComptimeValue(v: *const comp.ComptimeValue) void {
    switch (v.*) {
        .Void => std.debug.print("<void>", .{}),
        .Int => |i| std.debug.print("{d}", .{i}),
        .Float => |f| std.debug.print("{}", .{f}),
        .Bool => |b| std.debug.print("{s}", .{if (b) "true" else "false"}),
        .String => |s| std.debug.print("\"{s}\"", .{s}),
        .Sequence => |s| std.debug.print("<sequence len={d}>", .{s.values.items.len}),
        .Struct => |s| std.debug.print("<struct len={d}>", .{s.fields.items.len}),
        .Variant => std.debug.print("<variant>", .{}),
        .Range => |r| std.debug.print("range({d}..{d}{s})", .{ r.start, r.end, if (r.inclusive) "=" else "" }),
        .Type => |t| std.debug.print("type({d})", .{t.toRaw()}),
        .MlirType => std.debug.print("<mlir-type>", .{}),
        .MlirAttribute => std.debug.print("<mlir-attribute>", .{}),
        .MlirModule => std.debug.print("<mlir-module>", .{}),
        .Function => std.debug.print("<function>", .{}),
        .Code => std.debug.print("<code>", .{}),
        .Pointer => std.debug.print("<pointer>", .{}),
        .Map => |m| std.debug.print("<map len={d}>", .{m.entries.items.len}),
    }
}
