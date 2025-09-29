const std = @import("std");
const testing = std.testing;
const compiler = @import("compiler");

const Lowered = struct {
    tir: compiler.tir.TIR,
    type_info: *compiler.types.TypeInfo,
    context: *compiler.compile.Context,
};

var g_mlir_inited: bool = false;
var g_mlir_ctx: compiler.mlir.Context = undefined;

fn mlirContextOnce(alloc: std.mem.Allocator) compiler.mlir.Context {
    if (!g_mlir_inited) {
        g_mlir_ctx = compiler.compile.initMLIR(alloc);
        g_mlir_inited = true;
    }
    return g_mlir_ctx;
}

fn lowerToTir(gpa: std.mem.Allocator, src: []const u8) !Lowered {
    var context = compiler.compile.Context.init(gpa); // Create context
    defer context.deinit();

    const src0 = try std.mem.concatWithSentinel(gpa, u8, &.{src}, 0);
    defer gpa.free(src0);
    var parser = compiler.parser.Parser.init(gpa, src0, 0, &context); // Pass file_id and context
    var cst = try parser.parse();

    var lower1 = compiler.lower.Lower.init(gpa, &cst, &context); // Pass context
    var hir = try lower1.run();

    var pipeline = compiler.pipeline.Pipeline.init(gpa, &context); // Create pipeline
    var chk = compiler.checker.Checker.init(gpa, &hir, &context, &pipeline); // Pass context and pipeline
    try chk.run();
    if (context.diags.anyErrors()) return error.SemanticErrors; // Use context.diags

    // Persist a copy of type info on the heap for TIR/MLIR lifetime
    const ti = try gpa.create(compiler.types.TypeInfo);
    ti.* = context.type_info; // shallow copy; we won't deinit chk, only ti

    var lt = compiler.lower_tir.LowerTir.init(gpa, &context, &pipeline); // Pass context and pipeline
    defer lt.deinit();
    const t = try lt.run(&hir);
    return .{ .tir = t, .type_info = ti, .context = &context };
}

// test "mlir: match bool block arms codegen does not crash" {
//     const src =
//         \\
//         \\ f :: fn(b: bool) i64 {
//         \\   return match b { true => { 1 }, false => { 2 }, }
//         \\ }
//     ;
//     var lowered = try lowerToTir(std.heap.page_allocator, src);
//     defer {
//         lowered.tir.deinit();
//         lowered.type_info.deinit();
//         std.heap.page_allocator.destroy(lowered.type_info);
//     }
//
//     const ctx = mlirContextOnce(std.heap.page_allocator);
//     var gen = compiler.mlir_codegen.MlirCodegen.init(std.heap.page_allocator, lowered.context, ctx);
//     defer gen.deinit();
//
//     const module = try gen.emitModule(&lowered.tir, lowered.context);
//     _ = module;
// }
//
// test "mlir: if expression codegen does not crash" {
//     const src =
//         \\
//         \\ f :: fn(x: bool) i32 {
//         \\   y :: if x { 1 } else { 2 }
//         \\   return y
//         \\ }
//     ;
//     var lowered = try lowerToTir(std.heap.page_allocator, src);
//     defer {
//         lowered.tir.deinit();
//         lowered.type_info.deinit();
//         std.heap.page_allocator.destroy(lowered.type_info);
//     }
//
//     const ctx = mlirContextOnce(std.heap.page_allocator);
//     var gen = compiler.mlir_codegen.MlirCodegen.init(std.heap.page_allocator, lowered.context, ctx);
//     defer gen.deinit();
//
//     const module = try gen.emitModule(&lowered.tir, lowered.context);
//     _ = module;
// }
//
// test "mlir: catch expression codegen does not crash" {
//     const src =
//         \\
//         \\ g :: fn() i32 ! error{ E } { return 1 }
//         \\ f :: fn() i32 { return g() catch { 2 } }
//     ;
//     var lowered = try lowerToTir(std.heap.page_allocator, src);
//     defer {
//         lowered.tir.deinit();
//         lowered.type_info.deinit();
//         std.heap.page_allocator.destroy(lowered.type_info);
//     }
//
//     const ctx = mlirContextOnce(std.heap.page_allocator);
//     var gen = compiler.mlir_codegen.MlirCodegen.init(std.heap.page_allocator, ctx);
//     defer gen.deinit();
//
//     const module = try gen.emitModule(&lowered.tir, lowered.tir.type_store);
//     _ = module;
// }
