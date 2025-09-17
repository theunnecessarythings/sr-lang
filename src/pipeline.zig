const std = @import("std");
const cst = @import("cst_v2.zig");
const ast = @import("ast_v2.zig");
const tir = @import("tir_v2.zig");
const lower = @import("lower_v2.zig");
const lower_tir = @import("lower_tir_v2.zig");
const checker = @import("checker_v2.zig");
const infer = @import("infer_v2.zig");
const mlir_codegen_v2 = @import("mlir_codegen_v2.zig");
const mlir = @import("mlir_bindings.zig");
const compile = @import("compile.zig");
const Diagnostics = @import("diagnostics_v2.zig").Diagnostics;

pub const Result = struct {
    hir: ast.Ast,
    type_info: *infer.TypeInfoV2,
    module: tir.TIR,
    mlir_module: mlir.Module,
    gen: mlir_codegen_v2.TirLlvmGenV2,
};

pub const Pipeline = struct {
    allocator: std.mem.Allocator,
    diags: *Diagnostics,

    pub fn init(allocator: std.mem.Allocator, diags: *Diagnostics) Pipeline {
        return .{ .allocator = allocator, .diags = diags };
    }

    pub fn run(self: *Pipeline, program: *const cst.CST) !Result {
        // 1) Lower from CST v2 to AST v2
        var lower_pass = lower.LowerV2.init(self.allocator, program);
        var hir = try lower_pass.run();

        // 2) Checker now includes type inference
        var chk = checker.CheckerV2.init(self.allocator, self.diags);
        defer chk.deinit();
        const type_info = try self.allocator.create(infer.TypeInfoV2);
        type_info.* = try chk.run(&hir);

        // 4) Lower from AST v2 to TIR v2
        var tir_lowerer = lower_tir.LowerTirV2.init(self.allocator, type_info);
        const mod = try tir_lowerer.run(&hir);

        // 5) MLIR Codegen v2 from TIR v2 to MLIR
        var gen = mlir_codegen_v2.TirLlvmGenV2.init(self.allocator);
        var mlir_module = try gen.emitModule(&mod, &type_info.store);
        var op = mlir_module.getOperation();
        op.dump();

        // 6) Run MLIR Passes (same)
        try compile.run_passes(&gen.ctx, &mlir_module, true);

        // 7) Convert to LLVM IR and print
        try compile.convert_to_llvm_ir(mlir_module.handle, true);

        return .{ .hir = hir, .type_info = type_info, .module = mod, .mlir_module = mlir_module, .gen = gen };
    }
};
