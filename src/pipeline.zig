const std = @import("std");
const cst_mod = @import("cst.zig");
const ast_mod = @import("ast.zig");
const tir_mod = @import("tir.zig");
const lower_to_ast = @import("lower_to_ast.zig");
const lower_tir = @import("lower_tir.zig");
const checker = @import("checker.zig");
const lexer_mod = @import("lexer.zig");
const Lexer = lexer_mod.Tokenizer;
const Loc = lexer_mod.Token.Loc;
const Parser = @import("parser.zig").Parser;
const types = @import("types.zig");
const comp = @import("comptime.zig");
const interpreter = @import("interpreter.zig");
const codegen = @import("codegen_main.zig");
const mlir = @import("mlir_bindings.zig");
const compile = @import("compile.zig");
const tir_liveness = @import("tir_liveness.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;
const Package = @import("package.zig").Package;
const CompilationUnit = @import("package.zig").CompilationUnit;

pub const Result = struct {
    compilation_unit: ?CompilationUnit,
    mlir_module: ?mlir.Module = null,
    gen: ?codegen.Codegen = null,
};

pub const Pipeline = struct {
    allocator: std.mem.Allocator,
    context: *compile.Context,
    mlir_ctx: ?mlir.Context = null,
    // Optional analysis/transform passes (TIR level)
    tir_prune_unused: bool = true,
    tir_warn_unused: bool = true,

    pub const Mode = enum {
        lex,
        parse,
        ast,
        check,
        tir,
        tir_liveness,
        mlir,
        passes,
        llvm_ir,
        llvm_passes,
        jit,
        compile,
        run,
        interpret,

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

    pub fn run(
        self: *Pipeline,
        filename_or_src: []const u8,
        link_args: []const []const u8,
        mode: Mode,
        optimization_level: ?[]const u8,
    ) anyerror!Result {
        const filename = if (mode == .repl) "temp.sr" else filename_or_src;
        const file_id = try self.context.source_manager.add(filename);
        const source_path = self.context.source_manager.get(file_id) orelse filename;
        const source = if (mode == .repl)
            filename_or_src
        else
            try self.context.source_manager.read(file_id);
        defer self.allocator.free(source);
        const source0 = try self.allocator.dupeZ(u8, source);

        if (mode == .lex) {
            var lexer = Lexer.init(source0, file_id, .semi);
            while (true) {
                const token = lexer.next();
                if (token.tag == .eof) break;
                const lexeme = source0[token.loc.start..token.loc.end];
                std.debug.print("{}({},{}) `{s}`\n", .{ token.tag, token.loc.start, token.loc.end, lexeme });
            }
            return .{ .compilation_unit = null };
        }

        var parser = Parser.init(self.allocator, source0, file_id, self.context.diags, self.context);
        const main_thread = try std.Thread.spawn(.{}, Parser.run, .{&parser});
        self.context.compilation_unit.mutex.lock();
        try self.context.parse_worklist.append(self.allocator, .{
            .path = filename,
            .file_id = file_id,
            .thread = main_thread,
            .diags = self.context.diags,
            .parser = &parser,
        });
        self.context.compilation_unit.mutex.unlock();

        var i: usize = 0;
        var parse_failed = false;
        while (true) {
            self.context.compilation_unit.mutex.lock();
            if (i >= self.context.parse_worklist.items.len) {
                self.context.compilation_unit.mutex.unlock();
                break;
            }
            const work = self.context.parse_worklist.items[i];
            self.context.compilation_unit.mutex.unlock();

            work.thread.join();
            if (i > 0) {
                try self.context.diags.messages.appendSlice(try work.diags.messages.toOwnedSlice());
            }
            // If parsing this unit produced errors, skip consuming its CST.
            // Diagnostics are already merged; the pipeline will stop after the loop.
            if (work.diags.anyErrors()) {
                parse_failed = true;
                self.context.requestCancel();
                i += 1;
                continue;
            }
            if (self.context.isCancelled()) {
                // Cancellation requested due to another thread's failure; skip consuming this unit.
                i += 1;
                continue;
            }
            self.context.compilation_unit.mutex.lock();
            const package_id = work.parser.cst_u.program.package_name.unwrap();
            const package_name = self.context.interner.get(package_id);
            const package = self.context.compilation_unit.packages.getPtr(package_name);
            if (package) |pkg| {
                try pkg.sources.put(self.allocator, work.path, .{
                    .file_id = work.file_id,
                    .cst = work.parser.cst_u,
                    .ast = null,
                    .tir = null,
                    .type_info = null,
                });
            } else {
                const pkg_name = try self.allocator.dupe(u8, package_name);
                try self.context.compilation_unit.packages.put(
                    self.allocator,
                    pkg_name,
                    .{
                        .gpa = self.allocator,
                        .name = pkg_name,
                        .source_manager = self.context.source_manager,
                        .sources = .{},
                    },
                );
                const pkg = self.context.compilation_unit.packages.getPtr(pkg_name).?;
                try pkg.sources.put(self.allocator, work.path, .{
                    .file_id = work.file_id,
                    .cst = work.parser.cst_u,
                    .ast = null,
                    .tir = null,
                    .type_info = null,
                });
            }
            self.context.compilation_unit.mutex.unlock();
            i += 1;
        }
        self.context.parse_worklist.deinit(self.allocator);

        if (parse_failed or self.context.diags.anyErrors()) {
            return error.ParseFailed;
        }

        if (mode == .parse) {
            return .{ .compilation_unit = self.context.compilation_unit };
        }

        var pkg_iter = self.context.compilation_unit.packages.iterator();
        const runFn = struct {
            fn run(lower_pass: *lower_to_ast.Lower) !void {
                try lower_pass.runLower();
            }
        }.run;
        var threads = std.ArrayList(struct { std.Thread, *lower_to_ast.Lower, []const u8, []const u8 }){};
        while (pkg_iter.next()) |pkg| {
            var source_iter = pkg.value_ptr.sources.iterator();
            while (source_iter.next()) |unit| {
                if (self.context.isCancelled()) break;
                const lower_pass = try self.allocator.create(lower_to_ast.Lower);
                lower_pass.* = try lower_to_ast.Lower.init(
                    self.allocator,
                    &unit.value_ptr.cst.?,
                    self.context,
                    unit.value_ptr.file_id,
                );
                const thread = try std.Thread.spawn(.{}, runFn, .{lower_pass});
                try threads.append(self.allocator, .{ thread, lower_pass, pkg.key_ptr.*, unit.key_ptr.* });
            }
            if (self.context.isCancelled()) break;
        }

        for (threads.items) |thread| {
            thread.@"0".join();
            if (!self.context.isCancelled()) {
                self.context.compilation_unit.mutex.lock();
                const pkg = self.context.compilation_unit.packages.getPtr(thread.@"2").?;
                pkg.sources.getPtr(thread.@"3").?.ast = thread.@"1".ast_unit;
                self.context.compilation_unit.mutex.unlock();
            }
            // Always destroy per-thread state.
            self.allocator.destroy(thread.@"1");
        }
        var dep_levels = try compile.computeDependencyLevels(
            self.allocator,
            &self.context.compilation_unit,
            self.context.interner,
            self.context.source_manager,
        );
        defer dep_levels.deinit();
        // for (dep_levels.levels.items, 0..) |level, l| {
        //     std.debug.print("Dep level {}:\n", .{l});
        //     for (level.items) |id| {
        //         const fname = self.context.source_manager.get(id) orelse "Not Found";
        //         std.debug.print("Dep {}: {s}\n", .{ id, fname });
        //     }
        // }
        // Detect import cycles and abort early with clear diagnostics
        var cycle_report = try compile.detectImportCycles(
            self.allocator,
            &self.context.compilation_unit,
            self.context.interner,
            self.context.source_manager,
        );
        defer cycle_report.deinit();
        if (cycle_report.cycles.items.len > 0) {
            // Emit one error per cycle, summarizing the cycle chain
            for (cycle_report.cycles.items) |cy| {
                if (cy.items.len == 0) continue;
                // Build message: path1 -> path2 -> ... -> path1
                var buf = std.ArrayList(u8){};
                defer buf.deinit(self.allocator);
                var first = true;
                for (cy.items) |fid| {
                    const p = self.context.source_manager.get(fid) orelse "?";
                    if (!first) _ = buf.appendSlice(self.allocator, " -> ") catch {};
                    _ = buf.appendSlice(self.allocator, p) catch {};
                    first = false;
                }
                const sid = self.context.interner.intern(buf.items);
                const msg = self.context.interner.get(sid);
                const anchor = Loc.init(cy.items[0], 0, 0);
                _ = self.context.diags.addError(anchor, .import_cycle_detected, .{msg}) catch {};
            }
            if (cycle_report.blocked.items.len > 0) {
                var buf = std.ArrayList(u8){};
                defer buf.deinit(self.allocator);
                var first = true;
                for (cycle_report.blocked.items) |fid| {
                    const p = self.context.source_manager.get(fid) orelse "?";
                    if (!first) _ = buf.appendSlice(self.allocator, ", ") catch {};
                    _ = buf.appendSlice(self.allocator, p) catch {};
                    first = false;
                }
                const sid = self.context.interner.intern(buf.items);
                const msg = self.context.interner.get(sid);
                const anchor = Loc.init(cycle_report.blocked.items[0], 0, 0);
                _ = self.context.diags.addError(anchor, .imports_blocked_by_cycle, .{msg}) catch {};
            }
            return error.CycleDetected;
        }
        if (self.context.isCancelled() or self.context.diags.anyErrors()) {
            return error.LoweringFailed;
        }

        const canonical_path_opt = try canonicalizePath(self.allocator, source_path);
        defer if (canonical_path_opt) |p| self.allocator.free(p);

        if (mode == .ast) {
            return .{ .compilation_unit = self.context.compilation_unit };
        }

        var chk = checker.Checker.init(self.allocator, self.context, self);
        defer chk.deinit();
        try chk.run(&dep_levels);
        if (self.context.diags.anyErrors()) {
            return error.TypeCheckFailed;
        }
        if (mode == .check) {
            return .{ .compilation_unit = self.context.compilation_unit };
        }

        if (mode == .interpret) {
            try runInterpreterStage(self);
            return .{ .compilation_unit = self.context.compilation_unit };
        }

        var tir_lowerer = lower_tir.LowerTir.init(self.allocator, self.context, self, &chk);
        defer tir_lowerer.deinit();

        // If any TIR lowering thread fails, do not proceed further.
        _ = tir_lowerer.run(&dep_levels) catch |err| {
            self.context.requestCancel();
            return err;
        };

        if (self.context.isCancelled() or self.context.diags.anyErrors()) {
            return error.TirLoweringFailed;
        }
        if (mode == .tir) {
            return .{ .compilation_unit = self.context.compilation_unit };
        }
        if (mode == .tir_liveness) {
            // Optional pruning before dump
            if (self.tir_prune_unused) {
                try @import("tir_prune.zig").pruneUnusedFunctions(self.allocator, self.context, &self.context.compilation_unit, .{ .warn_unused = self.tir_warn_unused });
            }
            // Iterate all lowered units and dump liveness
            var pkg_it2 = self.context.compilation_unit.packages.iterator();
            while (pkg_it2.next()) |pkg| {
                var src_it2 = pkg.value_ptr.sources.iterator();
                while (src_it2.next()) |unit| {
                    if (unit.value_ptr.tir) |t| {
                        try tir_liveness.dump(self.allocator, t);
                    }
                }
            }
            return .{ .compilation_unit = self.context.compilation_unit };
        }

        // Optional pruning in normal pipeline modes
        if (self.tir_prune_unused) {
            try @import("tir_prune.zig").pruneUnusedFunctions(self.allocator, self.context, &self.context.compilation_unit, .{ .warn_unused = self.tir_warn_unused });
        }

        // Print Types
        // type_info.print();

        const mlir_ctx_ptr = self.ensureMlirContext();
        var gen = codegen.Codegen.init(self.allocator, self.context, mlir_ctx_ptr.*);
        gen.resetDebugCaches();

        var mlir_module = gen.emit(&dep_levels) catch |err| {
            switch (err) {
                error.CompilationFailed => {
                    return error.MlirCodegenFailed;
                },
                else => return err,
            }
        };

        var buf = std.array_list.Managed(u8).init(self.allocator);
        defer buf.deinit();
        var had_error = false;
        var sink = codegen.PrintBuffer{ .list = &buf, .had_error = &had_error };
        mlir_module.getOperation().print(codegen.printCallback, &sink);
        if (!had_error) {
            std.fs.cwd().makePath("out") catch |err| {
                if (err != error.PathAlreadyExists) return err;
            };
            const path = "out/temp.mlir";
            try std.fs.cwd().writeFile(.{ .data = sink.list.items, .sub_path = path });
        }

        // verify module
        if (!mlir_module.getOperation().verify()) {
            mlir_module.getOperation().dump();
            const msg = gen.diagnostic_data.msg orelse "";
            try self.context.diags.addError(
                .{ .file_id = file_id, .start = 0, .end = 0 },
                .mlir_verification_failed,
                .{msg},
            );
        }
        if (self.context.diags.anyErrors()) {
            return error.MlirCodegenFailed;
        }
        if (mode == .mlir) {
            std.debug.print("Generated MLIR module:\n", .{});
            var op = mlir_module.getOperation();
            op.dump();
            return .{
                .compilation_unit = self.context.compilation_unit,
                .mlir_module = mlir_module,
                .gen = gen,
            };
        }

        try compile.run_passes(&gen.mlir_ctx, &mlir_module);
        if (self.context.diags.anyErrors()) {
            return error.MlirPassesFailed;
        }
        if (mode == .passes) {
            std.debug.print("Transformed MLIR module:\n", .{});
            var op = mlir_module.getOperation();
            op.dump();
            return .{
                .compilation_unit = self.context.compilation_unit,
                .mlir_module = mlir_module,
                .gen = gen,
            };
        }

        try compile.convert_to_llvm_ir(mlir_module.handle, link_args, switch (mode) {
            .llvm_ir => .llvm_ir,
            .llvm_passes => .llvm_passes,
            else => .compile,
        }, optimization_level);
        if (self.context.diags.anyErrors()) {
            return error.LLVMIRFailed;
        }
        if (mode == .llvm_ir or mode == .llvm_passes) {
            return .{
                .compilation_unit = self.context.compilation_unit,
                .mlir_module = mlir_module,
                .gen = gen,
            };
        }
        if (mode == .compile) {
            return .{
                .compilation_unit = self.context.compilation_unit,
                .mlir_module = mlir_module,
                .gen = gen,
            };
        }

        if (mode == .jit) {
            compile.runJit(mlir_module.handle);
            if (self.context.diags.anyErrors()) {
                return error.JITFailed;
            }
            return .{
                .compilation_unit = self.context.compilation_unit,
                .mlir_module = mlir_module,
                .gen = gen,
            };
        }
        // For 'run' mode, do not launch the program here.
        // Let the CLI print diagnostics first, then run.
        return .{
            .compilation_unit = self.context.compilation_unit,
            .mlir_module = mlir_module,
            .gen = gen,
        };
    }
};

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

fn runInterpreterStage(self: *Pipeline) anyerror!void {
    var found_any: bool = false;
    var pkg_iter = self.context.compilation_unit.packages.iterator();
    while (pkg_iter.next()) |pkg| {
        var src_iter = pkg.value_ptr.sources.iterator();
        while (src_iter.next()) |unit| {
            if (unit.value_ptr.ast) |ast_unit| {
                const found = try interpretAstUnit(self, ast_unit);
                found_any = found_any or found;
            }
        }
    }
    if (!found_any) {
        std.debug.print("Interpreter stage: no comptime blocks found in ASTs\n", .{});
    }
}

fn interpretAstUnit(self: *Pipeline, ast_unit: *ast_mod.Ast) anyerror!bool {
    var interp = try interpreter.Interpreter.init(self.allocator, ast_unit);
    defer interp.deinit();

    var found_block = false;
    const decl_ids = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);
    for (decl_ids) |decl_id| {
        const decl = ast_unit.exprs.Decl.get(decl_id);
        var result = interp.evalExpr(decl.value) catch |err| switch (err) {
            interpreter.Interpreter.Error.UnsupportedExpr => continue,
            interpreter.Interpreter.Error.InvalidStatement => continue,
            else => return err,
        };
        found_block = true;
        if (decl.pattern.isNone()) {
            // no binding to register
        } else {
            const pat_id = decl.pattern.unwrap();
            if (ast_unit.pats.index.kinds.items[pat_id.toRaw()] == .Binding) {
                const binding = ast_unit.pats.get(.Binding, pat_id);
                const bound_value = try interp.cloneValue(result);
                try interp.setBinding(binding.name, bound_value);
            }
        }
        std.debug.print("Interpreter: decl {d} -> ", .{decl_id.toRaw()});
        printComptimeValue(&result);
        std.debug.print("\n", .{});
        result.destroy(self.allocator);
    }
    return found_block;
}

fn printComptimeValue(value: *const comp.ComptimeValue) void {
    switch (value.*) {
        .Void => std.debug.print("<void>", .{}),
        .Int => |i| std.debug.print("{d}", .{i}),
        .Float => |f| std.debug.print("{}", .{f}),
        .Bool => |b| std.debug.print("{s}", .{if (b) "true" else "false"}),
        .String => |s| std.debug.print("\"{s}\"", .{s}),
        .Sequence => |seq| std.debug.print("<sequence len={d}>", .{seq.values.items.len}),
        .Struct => |sv| std.debug.print("<struct len={d}>", .{sv.fields.items.len}),
        .Range => |rg| std.debug.print("range({d}..{d}{s})", .{ rg.start, rg.end, if (rg.inclusive) "=" else "" }),
        .Type => |ty| std.debug.print("type({d})", .{ty.toRaw()}),
        .MlirType => std.debug.print("<mlir-type>", .{}),
        .MlirAttribute => std.debug.print("<mlir-attribute>", .{}),
        .MlirModule => std.debug.print("<mlir-module>", .{}),
        .Function => std.debug.print("<function>", .{}),
    }
}
