const std = @import("std");
const cst = @import("cst.zig");
const ast = @import("ast.zig");
const tir = @import("tir.zig");
const lower = @import("lower.zig");
const lower_tir = @import("lower_tir.zig");
const checker = @import("checker.zig");
const bind = @import("bind.zig");
const infer = @import("infer.zig");
const mlir_codegen = @import("mlir_codegen.zig");
const mlir = @import("mlir_bindings.zig");
const compile = @import("compile.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;

pub const Result = struct {
    hir: ast.Unit,
    binder: ?bind.Binder,
    type_info: ?*infer.TypeInfo,
    module: tir.Module,
    mlir_module: mlir.Module,
    gen: ?mlir_codegen.TirLlvmGen,
};

pub const Pipeline = struct {
    allocator: std.mem.Allocator,
    diags: *Diagnostics,

    pub fn init(allocator: std.mem.Allocator, diags: *Diagnostics) Pipeline {
        return .{ .allocator = allocator, .diags = diags };
    }

    pub fn run(self: *Pipeline, program: *const cst.Program) !Result {
        // 1) Lower + desugar (future) from CST to AST
        var lower_pass = lower.Lower.init(self.allocator, self.diags);
        var hir = try lower_pass.run(program);

        // 2) Bind names into symbol table
        var binder = bind.Binder.init(self.allocator);
        try binder.run(&hir);

        // 3) Checker pass over HIR (structural checks)
        var chk = checker.Checker.init(self.allocator, self.diags);
        defer chk.deinit();
        try chk.run(&hir);

        // 4) Type inference: produce a side table of types
        var typer = infer.Typer.init(self.allocator, self.diags, &binder.symtab);
        const type_info = try self.allocator.create(infer.TypeInfo);
        type_info.* = typer.run(&hir) catch {
            try self.diags.addError(program.decls.items[0].loc, "type inference failed", .{});
            return error.TypeInferenceFailed;
        };

        // 5) Lower from AST to TIR
        var tir_lowerer: lower_tir.LowerTir = undefined;
        try tir_lowerer.init(self.allocator, &type_info.arena, &type_info.expr_types, &type_info.decl_types);
        const mod = tir_lowerer.run(&hir) catch {
            try self.diags.addError(program.decls.items[0].loc, "lowering to TIR failed", .{});
            return error.LoweringToTirFailed;
        };

        // 6) MLIR Codegen from TIR to MLIR
        var gen = mlir_codegen.TirLlvmGen.init(self.allocator);
        var mlir_module = try gen.emitModule(&mod, &type_info.arena);

        // 7) Run MLIR Passes to optimize and lower to LLVM dialect
        compile.run_passes(&gen.ctx, &mlir_module, true);

        // 8) Convert to LLVM IR and print
        compile.convert_to_llvm_ir(mlir_module.handle, true);

        // // 9) JIT Execution
        // compile.runJit(mlir_module.handle);

        return .{
            .hir = hir,
            .mlir_module = mlir_module,
            .module = mod,
            .binder = binder,
            .type_info = type_info,
            .gen = gen,
        };
    }
};
