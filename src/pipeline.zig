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
const codegen = @import("codegen_main.zig");
const mlir = @import("mlir_bindings.zig");
const compile = @import("compile.zig");
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

    pub const Mode = enum {
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
        ast_unit: *ast_mod.Ast,
        expr: ast_mod.ExprId,
        result_ty: types.TypeId,
        bindings: []const ComptimeBinding,
    ) !comp.ComptimeValue {
        const ctx = try self.allocator.create(lower_tir.LowerContext);
        ctx.* = lower_tir.LowerContext{
            .method_lowered = .init(self.allocator),
            .module_call_cache = .init(self.allocator),
            .monomorphizer = .init(self.allocator),
        };

        return lower_tir.evalComptimeExpr(
            self.allocator,
            ctx,
            self.context,
            self,
            chk,
            ast_unit,
            expr,
            result_ty,
            bindings,
        );
    }

    pub fn run(
        self: *Pipeline,
        filename_or_src: []const u8,
        link_args: []const []const u8,
        mode: Mode,
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
        try self.context.parse_worklist.append(self.allocator, .{
            .path = filename,
            .file_id = file_id,
            .thread = main_thread,
            .diags = self.context.diags,
            .parser = &parser,
        });

        var i: usize = 0;
        while (i < self.context.parse_worklist.items.len) {
            const work = self.context.parse_worklist.items[i];
            work.thread.join();
            if (i > 0) {
                try self.context.diags.messages.appendSlice(try work.diags.messages.toOwnedSlice());
            }
            // If parsing this unit produced errors, skip consuming its CST.
            // Diagnostics are already merged; the pipeline will stop after the loop.
            if (work.diags.anyErrors()) {
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

        if (self.context.diags.anyErrors()) {
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
            self.allocator.destroy(thread.@"1");
        }
        var dep_levels = try compile.computeDependencyLevels(
            self.allocator,
            &self.context.compilation_unit,
            self.context.interner,
            self.context.source_manager,
        );
        defer dep_levels.deinit();
        for (dep_levels.levels.items, 0..) |level, l| {
            std.debug.print("Dep level {}:\n", .{l});
            for (level.items) |id| {
                const fname = self.context.source_manager.get(id) orelse "Not Found";
                std.debug.print("Dep {}: {s}\n", .{ id, fname });
            }
        }
        if (self.context.diags.anyErrors()) {
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

        var tir_lowerer = lower_tir.LowerTir.init(self.allocator, self.context, self, &chk);
        defer tir_lowerer.deinit();

        _ = try tir_lowerer.run(&dep_levels);

        if (self.context.diags.anyErrors()) {
            return error.TirLoweringFailed;
        }
        if (mode == .tir) {
            return .{ .compilation_unit = self.context.compilation_unit };
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

        try compile.convert_to_llvm_ir(mlir_module.handle, true, link_args, switch (mode) {
            .llvm_ir => .llvm_ir,
            .llvm_passes => .llvm_passes,
            else => .compile,
        });
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
        // run
        compile.run();
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
