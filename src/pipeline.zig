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

pub const Result = struct {
    cst: ?cst_mod.CST = null,
    ast: ?ast_mod.Ast = null,
    tir: ?tir_mod.TIR = null,
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
        ast_unit: *const ast_mod.Ast,
        expr: ast_mod.ExprId,
        result_ty: types.TypeId,
        bindings: []const ComptimeBinding,
    ) !comp.ComptimeValue {
        return lower_tir.evalComptimeExpr(
            self.allocator,
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
            return .{};
        }

        var parser = Parser.init(self.allocator, source0, file_id, self.context);
        const cst_program = try parser.parse();

        if (self.context.diags.anyErrors()) {
            return error.ParseFailed;
        }
        if (mode == .parse) {
            return .{ .cst = cst_program };
        }

        var lower_pass = lower_to_ast.Lower.init(self.allocator, &cst_program, self.context);
        var ast = try lower_pass.run();
        if (self.context.diags.anyErrors()) {
            return error.LoweringFailed;
        }

        const canonical_path_opt = try canonicalizePath(self.allocator, source_path);
        defer if (canonical_path_opt) |p| self.allocator.free(p);
        const module_path = canonical_path_opt orelse source_path;
        const base_dir = moduleBaseDir(module_path);

        if (mode == .ast) {
            return .{ .cst = cst_program, .ast = ast };
        }

        var chk = checker.Checker.init(self.allocator, &ast, self.context, self);
        chk.import_base_dir = base_dir;
        defer chk.deinit();
        try chk.run();
        if (self.context.diags.anyErrors()) {
            return error.TypeCheckFailed;
        }
        if (mode == .check) {
            return .{ .cst = cst_program, .ast = ast };
        }

        var tir_lowerer = lower_tir.LowerTir.init(self.allocator, self.context, self, &chk);
        defer tir_lowerer.deinit();

        const root_mod = try tir_lowerer.run(&ast);

        if (self.context.diags.anyErrors()) {
            return error.TirLoweringFailed;
        }
        if (mode == .tir) {
            return .{ .cst = cst_program, .ast = ast, .tir = root_mod };
        }

        // Print Types
        // type_info.print();

        const mlir_ctx_ptr = self.ensureMlirContext();
        var gen = codegen.Codegen.init(self.allocator, self.context, mlir_ctx_ptr.*);
        gen.resetDebugCaches();

        tir_lowerer.import_base_dir = base_dir;

        var mlir_module = gen.emitModule(&root_mod, &chk.type_info) catch |err| {
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
            return .{ .cst = cst_program, .ast = ast, .tir = root_mod, .mlir_module = mlir_module, .gen = gen };
        }

        try compile.run_passes(&gen.mlir_ctx, &mlir_module);
        if (self.context.diags.anyErrors()) {
            return error.MlirPassesFailed;
        }
        if (mode == .passes) {
            std.debug.print("Transformed MLIR module:\n", .{});
            var op = mlir_module.getOperation();
            op.dump();
            return .{ .cst = cst_program, .ast = ast, .tir = root_mod, .mlir_module = mlir_module, .gen = gen };
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
            return .{ .cst = cst_program, .ast = ast, .tir = root_mod, .mlir_module = mlir_module, .gen = gen };
        }
        if (mode == .compile) {
            return .{ .cst = cst_program, .ast = ast, .tir = root_mod, .mlir_module = mlir_module, .gen = gen };
        }

        if (mode == .jit) {
            compile.runJit(mlir_module.handle);
            if (self.context.diags.anyErrors()) {
                return error.JITFailed;
            }
            return .{ .cst = cst_program, .ast = ast, .tir = root_mod, .mlir_module = mlir_module, .gen = gen };
        }
        // run
        compile.run();
        return .{ .ast = ast, .tir = root_mod, .mlir_module = mlir_module, .gen = gen, .cst = cst_program };
    }
};

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
