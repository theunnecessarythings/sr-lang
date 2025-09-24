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

    pub fn run(self: *Pipeline, program: *cst.CST) !Result {
        // 1) Lower from CST v2 to AST v2
        var lower_pass = lower.Lower.init(self.allocator, program, self.diags);
        var hir = try lower_pass.run();

        // 2) Checker now includes type inference
        var chk = checker.Checker.init(self.allocator, self.diags, &hir);
        defer chk.deinit();
        const type_info = try self.allocator.create(types.TypeInfo);
        type_info.* = try chk.runWithTypes();
        defer type_info.deinit();

        // 4) Lower from AST v2 to TIR v2
        var tir_lowerer = lower_tir.LowerTir.init(self.allocator, type_info);
        const mod = try tir_lowerer.run(&hir);

        const mlir_ctx = compile.initMLIR(self.allocator);

        // 5) MLIR Codegen v2 from TIR v2 to MLIR
        var gen = mlir_codegen.MlirCodegen.init(self.allocator, mlir_ctx);
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
