const std = @import("std");
const testing = std.testing;
const compiler = @import("compiler");

const Lowered = struct {
    tir: compiler.tir.TIR,
    checker: *compiler.checker.Checker,
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
    const context = try gpa.create(compiler.compile.Context);
    context.* = compiler.compile.Context.init(gpa);
    errdefer {
        context.deinit();
        gpa.destroy(context);
    }

    const src0 = try std.mem.concatWithSentinel(gpa, u8, &.{src}, 0);
    defer gpa.free(src0);
    var parser = compiler.parser.Parser.init(gpa, src0, 0, context);
    var cst = try parser.parse();
    defer cst.deinit();

    var lower1 = try compiler.lower_to_ast.Lower.init(gpa, &cst, context, 0);
    defer lower1.deinit();
    const result = try lower1.run();
    defer result.deinit();
    const hir = result.ast_unit;

    var pipeline = compiler.pipeline.Pipeline.init(gpa, context);
    const chk = try gpa.create(compiler.checker.Checker);
    chk.* = compiler.checker.Checker.init(gpa, context, &pipeline);
    errdefer {
        chk.deinit();
        gpa.destroy(chk);
    }
    try chk.runAst(hir);
    if (context.diags.anyErrors()) return error.SemanticErrors;

    var lt = compiler.lower_tir.LowerTir.init(gpa, context, &pipeline, chk);
    defer lt.deinit();
    const t = try lt.runAst(hir);
    return .{ .tir = t, .checker = chk, .type_info = &chk.type_info, .context = context };
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
//         lowered.checker.deinit();
//         std.heap.page_allocator.destroy(lowered.checker);
//         lowered.context.deinit();
//         std.heap.page_allocator.destroy(lowered.context);
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
//         lowered.checker.deinit();
//         std.heap.page_allocator.destroy(lowered.checker);
//         lowered.context.deinit();
//         std.heap.page_allocator.destroy(lowered.context);
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
//         lowered.checker.deinit();
//         std.heap.page_allocator.destroy(lowered.checker);
//         lowered.context.deinit();
//         std.heap.page_allocator.destroy(lowered.context);
//     }
//
//     const ctx = mlirContextOnce(std.heap.page_allocator);
//     var gen = compiler.mlir_codegen.MlirCodegen.init(std.heap.page_allocator, ctx);
//     defer gen.deinit();
//
//     const module = try gen.emitModule(&lowered.tir, lowered.tir.type_store);
//     _ = module;
// }
