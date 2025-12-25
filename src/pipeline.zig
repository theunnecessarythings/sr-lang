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

/// Outcome of running part of the pipeline (contains compilation unit/IR if produced).
pub const Result = struct {
    /// Optional compilation unit produced by the pipeline stages.
    compilation_unit: ?CompilationUnit,
    /// Generated MLIR module when code generation completed.
    mlir_module: ?mlir.Module = null,
    /// Active codegen emitter (needed when emitting debug output or diagnostics).
    gen: ?codegen.Codegen = null,
    /// Number of discovered test functions when running in test mode.
    test_count: usize = 0,
};

pub const ProgressStage = enum {
    parsing,
    lowering_ast,
    type_checking,
    lowering_tir,
    mlir_codegen,
    llvm_codegen,
    count,
};

const stageNames: [@intFromEnum(ProgressStage.count)][]const u8 = .{
    "Parsing",
    "Lowering AST",
    "Type checking",
    "Lowering to TIR",
    "MLIR codegen",
    "LLVM codegen",
};

pub fn stageName(stage: ProgressStage) []const u8 {
    return stageNames[@intFromEnum(stage)];
}

pub const ProgressCallback = *const fn (?*anyopaque, ProgressStage, usize, usize) void;

pub const ProgressReporter = struct {
    callback: ProgressCallback,
    context: ?*anyopaque,

    pub fn report(self: *ProgressReporter, stage: ProgressStage) void {
        const idx = @intFromEnum(stage) + 1;
        const total = @intFromEnum(ProgressStage.count);
        self.callback(self.context, stage, idx, total);
    }
};

/// Manages the compilation pipeline stages driven by CLI modes.
pub const Pipeline = struct {
    /// Allocator used for temporary passes and intermediate buffers.
    allocator: std.mem.Allocator,
    /// Shared compilation context.
    context: *compile.Context,
    /// Cached MLIR context reused across runs.
    mlir_ctx: ?mlir.Context = null,
    /// Whether to prune unused TIR entities.
    tir_prune_unused: bool = true,
    /// Emit warnings for unused TIR during pruning.
    tir_warn_unused: bool = false,
    /// Enable debug info generation.
    debug_info: bool = false,

    /// Execution modes supported by the pipeline (lex, parse, analyze, codegen...).
    pub const Mode = enum {
        /// Tokenize the source and print tokens.
        lex,
        /// Stop after parsing and return the CST.
        parse,
        /// Stop after building the AST.
        ast,
        /// Run the checker stage.
        check,
        /// Dump the lowered TIR.
        tir,
        /// Dump TIR liveness analysis.
        tir_liveness,
        /// Emit MLIR and stop.
        mlir,
        /// Run MLIR passes and show the transformed module.
        passes,
        /// Emit LLVM IR without further actions.
        llvm_ir,
        /// Run LLVM passes and dump the IR.
        llvm_passes,
        /// JIT the generated module and run it.
        jit,
        /// Full compile pipeline producing an executable.
        compile,
        /// Build, emit, and run the compiled binary (run only path, CLI handles launch).
        run,
        // Compile all tests and emit a harness main that executes them.
        test_mode,
        /// Execute the interpreter stage (comptime only).
        interpret,

        /// REPL mode that incrementally evaluates source lines.
        repl,
    };

    /// Create a pipeline instance bound to the given allocator/context.
    pub fn init(allocator: std.mem.Allocator, context: *compile.Context) Pipeline {
        return .{ .allocator = allocator, .context = context };
    }

    /// Lazily create an MLIR context if not already available.
    pub fn ensureMlirContext(self: *Pipeline) *mlir.Context {
        if (self.mlir_ctx) |*ctx| return ctx;
        self.mlir_ctx = compile.initMLIR(self.allocator);
        return &self.mlir_ctx.?;
    }

    /// Represent compile-time bindings injected into the interpreter.
    pub const ComptimeBinding = union(enum) {
        /// A type parameter binding (name + `TypeId`).
        type_param: struct { name: ast_mod.StrId, ty: types.TypeId },
        /// A value parameter binding with its runtime `ComptimeValue`.
        value_param: struct { name: ast_mod.StrId, ty: types.TypeId, value: comp.ComptimeValue },
    };

    /// Run the pipeline beginning from `filename_or_src` up to `mode`, optionally linking/optimizing.
    pub fn run(
        self: *Pipeline,
        filename_or_src: []const u8,
        link_args: []const []const u8,
        mode: Mode,
        progress: ?*ProgressReporter,
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

        if (progress) |reporter| reporter.report(.parsing);
        if (mode == .lex) {
            var lexer: Lexer = .init(source0, file_id, .semi);
            while (true) {
                const token = lexer.next();
                if (token.tag == .eof) break;
                const lexeme = source0[token.loc.start..token.loc.end];
                std.debug.print("{}({},{}) `{s}`\n", .{ token.tag, token.loc.start, token.loc.end, lexeme });
            }
            return .{ .compilation_unit = null };
        }

        var parser: Parser = .init(self.allocator, source0, file_id, self.context.diags, self.context);
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
            }
            if (!parse_failed and self.context.load_imports) {
                const program = work.parser.cst_u.program;
                const decl_ids = work.parser.cst_u.exprs.decl_pool.slice(program.top_decls);
                for (decl_ids) |decl_id| {
                    const decl = work.parser.cst_u.exprs.Decl.get(decl_id);
                    if (work.parser.cst_u.kind(decl.rhs) != .Import) continue;

                    const imp = work.parser.cst_u.exprs.get(.Import, decl.rhs);
                    const imp_name = work.parser.cst_u.exprs.strs.get(imp.path);
                    const resolved_path = compile.resolveImportPath(
                        self.allocator,
                        self.context.source_manager,
                        work.file_id,
                        imp_name,
                    ) catch {
                        _ = self.context.diags.addError(
                            work.parser.cst_u.exprs.locs.get(imp.loc),
                            .import_not_found,
                            .{},
                        ) catch {};
                        parse_failed = true;
                        continue;
                    };
                    defer self.allocator.free(resolved_path);

                    const import_file_id = try self.context.source_manager.add(resolved_path);
                    const sm_path = self.context.source_manager.get(import_file_id).?;
                    const resolved_id = self.context.interner.intern(sm_path);
                    const import_row_idx = work.parser.cst_u.exprs.index.rows.items[decl.rhs.toRaw()];
                    var import_row = work.parser.cst_u.exprs.table(.Import).get(import_row_idx);
                    import_row.path = resolved_id;
                    work.parser.cst_u.exprs.table(.Import).set(import_row_idx, import_row);

                    self.context.compilation_unit.mutex.lock();
                    var already_exists = false;
                    var pkg_iter = self.context.compilation_unit.packages.iterator();
                    while (pkg_iter.next()) |pkg| {
                        if (pkg.value_ptr.sources.get(sm_path) != null) {
                            already_exists = true;
                            break;
                        }
                    }
                    if (!already_exists) {
                        for (self.context.parse_worklist.items) |item| {
                            if (item.file_id == import_file_id) {
                                already_exists = true;
                                break;
                            }
                        }
                    }

                    if (!already_exists) {
                        const import_source = try self.context.source_manager.read(import_file_id);
                        const import_source0 = try self.allocator.dupeZ(u8, import_source);
                        self.allocator.free(import_source);

                        const child_diags = try self.allocator.create(Diagnostics);
                        child_diags.* = Diagnostics.init(self.allocator, self.context.type_store, self.context.interner);

                        const child_parser = try self.allocator.create(Parser);
                        child_parser.* = Parser.init(self.allocator, import_source0, import_file_id, child_diags, self.context);

                        const thread = try std.Thread.spawn(.{}, Parser.run, .{child_parser});
                        try self.context.parse_worklist.append(self.allocator, .{
                            .path = sm_path,
                            .file_id = import_file_id,
                            .thread = thread,
                            .diags = child_diags,
                            .parser = child_parser,
                        });
                    }
                    self.context.compilation_unit.mutex.unlock();

                    const dep_id = self.context.interner.intern(sm_path);
                    try self.context.compilation_unit.addDependency(work.file_id, dep_id);
                }
            }
            if (!parse_failed) {
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
            }
            i += 1;
        }
        self.context.parse_worklist.deinit(self.allocator);

        if (parse_failed or self.context.diags.anyErrors()) {
            return error.ParseFailed;
        }

        if (mode == .parse) {
            return .{ .compilation_unit = self.context.compilation_unit };
        }

        if (progress) |reporter| reporter.report(.lowering_ast);
        var pkg_iter = self.context.compilation_unit.packages.iterator();
        // Helper thread entry that executes a lowering pass.
        const runFn = struct {
            /// Thread entry that invokes `runLower` on the provided pass.
            fn run(lower_pass: *lower_to_ast.Lower) !void {
                try lower_pass.runLower();
            }
        }.run;
        var threads = std.ArrayList(struct { std.Thread, *lower_to_ast.Lower, []const u8, []const u8 }){};
        while (pkg_iter.next()) |pkg| {
            var source_iter = pkg.value_ptr.sources.iterator();
            while (source_iter.next()) |unit| {
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
        }

        for (threads.items) |thread| {
            thread.@"0".join();
            self.context.compilation_unit.mutex.lock();
            const pkg = self.context.compilation_unit.packages.getPtr(thread.@"2").?;
            pkg.sources.getPtr(thread.@"3").?.ast = thread.@"1".ast_unit;
            self.context.compilation_unit.mutex.unlock();
            for (thread.@"1".dependencies.items) |dep| {
                try self.context.compilation_unit.addDependency(thread.@"1".file_id, dep);
            }
            thread.@"1".dependencies.deinit(self.allocator);
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
                const anchor: Loc = .init(cy.items[0], 0, 0);
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
                const anchor: Loc = .init(cycle_report.blocked.items[0], 0, 0);
                _ = self.context.diags.addError(anchor, .imports_blocked_by_cycle, .{msg}) catch {};
            }
            return error.CycleDetected;
        }
        if (self.context.diags.anyErrors()) {
            return error.LoweringFailed;
        }

        const canonical_path_opt = try canonicalizePath(self.allocator, source_path);
        defer if (canonical_path_opt) |p| self.allocator.free(p);

        if (mode == .ast) {
            return .{ .compilation_unit = self.context.compilation_unit };
        }

        if (progress) |reporter| reporter.report(.type_checking);
        var chk: checker.Checker = .init(self.allocator, self.context, self);
        defer chk.deinit();
        try chk.run(&dep_levels);
        if (self.context.diags.anyErrors()) {
            return error.TypeCheckFailed;
        }
        if (mode == .check) {
            return .{ .compilation_unit = self.context.compilation_unit, .test_count = 0 };
        }

        if (mode == .interpret) {
            try runInterpreterStage(self);
            return .{ .compilation_unit = self.context.compilation_unit, .test_count = 0 };
        }

        if (progress) |reporter| reporter.report(.lowering_tir);
        var tir_lowerer: lower_tir.LowerTir = .init(self.allocator, self.context, self, &chk, mode == .test_mode);
        defer tir_lowerer.deinit();
        const test_count = if (mode == .test_mode) tir_lowerer.test_funcs.items.len else 0;

        // If any TIR lowering thread fails, do not proceed further.
        _ = tir_lowerer.run(&dep_levels) catch |err| return err;

        if (self.context.diags.anyErrors()) {
            return error.TirLoweringFailed;
        }
        if (mode == .tir) {
            return .{ .compilation_unit = self.context.compilation_unit, .test_count = test_count };
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
            return .{ .compilation_unit = self.context.compilation_unit, .test_count = test_count };
        }

        // Optional pruning in normal pipeline modes
        if (self.tir_prune_unused) {
            try @import("tir_prune.zig").pruneUnusedFunctions(self.allocator, self.context, &self.context.compilation_unit, .{ .warn_unused = self.tir_warn_unused });
        }

        // Print Types
        // type_info.print();

        if (progress) |reporter| reporter.report(.mlir_codegen);
        codegen.enable_debug_info = self.debug_info;
        const mlir_ctx_ptr = self.ensureMlirContext();
        var gen: codegen.Codegen = .init(self.allocator, self.context, mlir_ctx_ptr, false);
        gen.resetDebugCaches();

        var mlir_module = gen.emit(&dep_levels) catch |err| {
            switch (err) {
                error.CompilationFailed => {
                    return error.MlirCodegenFailed;
                },
                else => return err,
            }
        };

        var buf: std.array_list.Managed(u8) = .init(self.allocator);
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
            // mlir_module.getOperation().dump();
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

        // Emit Triton-only MLIR module and invoke Triton driver to produce PTX.
        // Re-run codegen in Triton-only mode to emit tt.func stubs.
        if (gen.has_triton_fns) {
            var gen_triton: codegen.Codegen = .init(self.allocator, self.context, mlir_ctx_ptr, true);
            defer gen_triton.deinit();
            var triton_module = gen_triton.emitTritonModule(&dep_levels) catch |err| {
                switch (err) {
                    error.CompilationFailed => return error.MlirCodegenFailed,
                    else => return err,
                }
            };

            var tbuf: std.array_list.Managed(u8) = .init(self.allocator);
            defer tbuf.deinit();
            var thad_error = false;
            var tsink = codegen.PrintBuffer{ .list = &tbuf, .had_error = &thad_error };
            triton_module.getOperation().print(codegen.printCallback, &tsink);
            if (thad_error) return error.MlirCodegenFailed;

            const tpath = "out/triton_kernels.mlir";
            std.fs.cwd().makePath("out") catch |err| {
                if (err != error.PathAlreadyExists) return err;
            };
            try std.fs.cwd().writeFile(.{ .data = tsink.list.items, .sub_path = tpath });

            const driver_path = "third-party/triton/build/cmake.linux-x86_64-cpython-3.13/bin/triton_mlir_driver";

            var arg_sm: ?[]u8 = null;
            var arg_num_warps: ?[]u8 = null;
            var arg_threads_per_warp: ?[]u8 = null;
            var arg_ptx_version: ?[]u8 = null;
            var arg_num_ctas: ?[]u8 = null;

            var mod_op = triton_module.getOperation();
            const target_attr = mod_op.getDiscardableAttributeByName(.from("ttg.target"));
            if (!target_attr.isNull() and target_attr.isAString()) {
                const s = target_attr.stringAttrGetValue();
                const slice = s.toSlice();
                if (std.mem.startsWith(u8, slice, "cuda:")) {
                    const sm_ver = slice["cuda:".len..];
                    arg_sm = try std.fmt.allocPrint(self.allocator, "--sm={s}", .{sm_ver});
                }
            }

            const num_warps_attr = mod_op.getDiscardableAttributeByName(.from("ttg.num-warps"));
            if (!num_warps_attr.isNull() and num_warps_attr.isAInteger()) {
                arg_num_warps = try std.fmt.allocPrint(self.allocator, "--num-warps={d}", .{num_warps_attr.integerAttrGetValueInt()});
            }

            const threads_per_warp_attr = mod_op.getDiscardableAttributeByName(.from("ttg.threads-per-warp"));
            if (!threads_per_warp_attr.isNull() and threads_per_warp_attr.isAInteger()) {
                arg_threads_per_warp = try std.fmt.allocPrint(self.allocator, "--threads-per-warp={d}", .{threads_per_warp_attr.integerAttrGetValueInt()});
            }

            const ptx_version_attr = mod_op.getDiscardableAttributeByName(.from("ttg.ptx-version"));
            if (!ptx_version_attr.isNull() and ptx_version_attr.isAInteger()) {
                arg_ptx_version = try std.fmt.allocPrint(self.allocator, "--ptx-version={d}", .{ptx_version_attr.integerAttrGetValueInt()});
            }

            const num_ctas_attr = mod_op.getDiscardableAttributeByName(.from("ttg.num-ctas"));
            if (!num_ctas_attr.isNull() and num_ctas_attr.isAInteger()) {
                arg_num_ctas = try std.fmt.allocPrint(self.allocator, "--num-ctas={d}", .{num_ctas_attr.integerAttrGetValueInt()});
            } else {
                arg_num_ctas = try std.fmt.allocPrint(self.allocator, "--num-ctas=1", .{});
            }

            const arg_input = try std.fmt.allocPrint(self.allocator, "--input={s}", .{tpath});
            const arg_ptx = try std.fmt.allocPrint(self.allocator, "--emit-ptx={s}", .{"out/triton_kernels.ptx"});
            defer {
                self.allocator.free(arg_input);
                self.allocator.free(arg_ptx);
                if (arg_sm) |t| self.allocator.free(t);
                if (arg_num_warps) |t| self.allocator.free(t);
                if (arg_threads_per_warp) |t| self.allocator.free(t);
                if (arg_ptx_version) |t| self.allocator.free(t);
                if (arg_num_ctas) |t| self.allocator.free(t);
            }

            var args = std.ArrayList([]const u8){};
            defer args.deinit(self.allocator);
            try args.append(self.allocator, driver_path);
            try args.append(self.allocator, arg_input);
            try args.append(self.allocator, arg_ptx);
            if (arg_sm) |t| try args.append(self.allocator, t);
            if (arg_num_warps) |t| try args.append(self.allocator, t);
            if (arg_threads_per_warp) |t| try args.append(self.allocator, t);
            if (arg_ptx_version) |t| try args.append(self.allocator, t);
            if (arg_num_ctas) |t| try args.append(self.allocator, t);

            var child: std.process.Child = .init(args.items, self.allocator);
            child.cwd = ".";
            try child.spawn();
            const term = try child.wait();
            switch (term) {
                .Exited => |code| {
                    if (code != 0) return error.TritonDriverFailed;
                },
                else => return error.TritonDriverFailed,
            }
        }

        if (mode == .mlir) {
            std.debug.print("Generated MLIR module:\n", .{});
            var op = mlir_module.getOperation();
            op.dump();
            return .{
                .compilation_unit = self.context.compilation_unit,
                .mlir_module = mlir_module,
                .gen = gen,
                .test_count = test_count,
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
                .test_count = test_count,
            };
        }

        if (progress) |reporter| reporter.report(.llvm_codegen);
        try compile.convert_to_llvm_ir(mlir_module.handle, link_args, switch (mode) {
            .llvm_ir => .llvm_ir,
            .llvm_passes => .llvm_passes,
            .test_mode => .compile,
            else => .compile,
        }, optimization_level, self.debug_info);
        if (self.context.diags.anyErrors()) {
            return error.LLVMIRFailed;
        }
        if (mode == .llvm_ir or mode == .llvm_passes) {
            return .{
                .compilation_unit = self.context.compilation_unit,
                .mlir_module = mlir_module,
                .gen = gen,
                .test_count = test_count,
            };
        }
        if (mode == .compile or mode == .test_mode) {
            return .{
                .compilation_unit = self.context.compilation_unit,
                .mlir_module = mlir_module,
                .gen = gen,
                .test_count = test_count,
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
                .test_count = test_count,
            };
        }
        // For 'run' mode, do not launch the program here.
        // Let the CLI print diagnostics first, then run.
        return .{
            .compilation_unit = self.context.compilation_unit,
            .mlir_module = mlir_module,
            .gen = gen,
            .test_count = test_count,
        };
    }
};

/// Return the package location if present, otherwise fall back to zero-width span at `file_id`.
fn packageLocOrDefault(ast: *const ast_mod.Ast, file_id: u32) Loc {
    if (!ast.unit.package_loc.isNone()) {
        const loc_id = ast.unit.package_loc.unwrap();
        return ast.exprs.locs.get(loc_id);
    }
    return .init(file_id, 0, 0);
}

/// Case-sensitive comparison of two name slices (wrapper around `std.mem.eql`).
fn namesEqual(a: []const u8, b: []const u8) bool {
    return std.mem.eql(u8, a, b);
}

/// Attempt to canonicalize `path`; return `null` if the file cannot be resolved.
fn canonicalizePath(
    allocator: std.mem.Allocator,
    path: []const u8,
) !?[]u8 {
    return std.fs.cwd().realpathAlloc(allocator, path) catch |err| switch (err) {
        error.FileNotFound, error.AccessDenied => return null,
        else => return err,
    };
}

/// Return the declared package name for `ast`, if any.
fn declareName(ast: *const ast_mod.Ast) ?[]const u8 {
    if (ast.unit.package_name.isNone()) return null;
    const sid = ast.unit.package_name.unwrap();
    return ast.exprs.strs.get(sid);
}

/// Execute the interpreter stage once all ASTs are available.
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

/// Interpret the comptime declarations in `ast_unit` and install bindings.
fn interpretAstUnit(self: *Pipeline, ast_unit: *ast_mod.Ast) anyerror!bool {
    var interp = try interpreter.Interpreter.init(self.allocator, ast_unit, null, null, null, undefined);
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
            if (ast_unit.kind(pat_id) == .Binding) {
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

/// Human-friendly printer used by the interpreter stage.
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
        .Pointer => |_| std.debug.print("<pointer>", .{}),
        .Map => |map| std.debug.print("<map len={d}>", .{map.entries.items.len}),
    }
}
