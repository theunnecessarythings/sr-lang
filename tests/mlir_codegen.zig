const std = @import("std");
const testing = std.testing;
const compiler = @import("compiler");
const CST = compiler.cst_v2.CST;
const Parser = compiler.parser_v2.Parser;
const Lower = compiler.lower_v2.LowerV2;
const Checker = compiler.checker_v2.CheckerV2;
const diag = compiler.diagnostics_v2;
const LowerTir = compiler.lower_tir_v2.LowerTirV2;

const gpa = testing.allocator;

fn checkProgram(src: [:0]const u8, expected: []const diag.DiagnosticCode) !void {
    var diags = diag.Diagnostics.init(gpa);
    defer diags.deinit();

    // Step 1: Parse
    var parser = Parser.init(gpa, src, &diags);
    var cst = try parser.parse();
    defer cst.deinit();
    if (diags.count() != 0) {
        // print tokens for debugging
        var tokenizer = compiler.lexer.Tokenizer.init(src, .semi);
        while (true) {
            const token = tokenizer.next();
            if (token.tag == .eof) break;
            std.debug.print("Token: {any}\n", .{token.tag});
        }
        std.debug.print(
            "Errors during parsing: {}\n",
            .{diags.messages.items[0].code},
        );
    }
    try testing.expectEqual(0, diags.count());

    // Step 2: Lower to AST
    var lower = Lower.init(gpa, &cst, &diags);
    defer lower.deinit();
    var ast = try lower.run();

    // Step 3: Type Check
    var checker = Checker.init(gpa, &diags, &ast);
    defer checker.deinit();
    _ = try checker.run();
    defer checker.type_info.deinit();

    testing.expectEqual(0, diags.count()) catch |err| {
        for (diags.messages.items) |msg| {
            std.debug.print("  - Diagnostic: {}\n", .{msg.code});
        }
        return err;
    };

    var lower_tir = LowerTir.init(gpa, &checker.type_info);
    defer lower_tir.deinit();
    var tir = try lower_tir.run(&ast);
    defer tir.deinit();

    var mlir_gen = compiler.mlir_codegen_v2.MlirCodegen.init(gpa);
    defer mlir_gen.deinit();
    var mlir_module = try mlir_gen.emitModule(&tir, tir.type_store);

    _ = try compiler.compile.run_passes(&mlir_gen.ctx, &mlir_module, false);

    _ = expected;
}

test "simple program" {
    const src =
        \\ main :: proc() i32 {
        \\   return 42
        \\ }
    ;
    try checkProgram(src, &.{});
}
