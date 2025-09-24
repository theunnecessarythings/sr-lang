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
var ctx: ?compiler.mlir.Context = null;

fn checkProgram(src: [:0]const u8) !void {
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
    if (ctx == null)
        ctx = compiler.compile.initMLIR(gpa);
    var mlir_gen = compiler.mlir_codegen_v2.MlirCodegen.init(gpa, ctx.?);
    defer mlir_gen.deinit();
    var mlir_module = try mlir_gen.emitModule(&tir, tir.type_store);

    _ = try compiler.compile.run_passes(&mlir_gen.ctx, &mlir_module, false);
}

test "simple program" {
    const src =
        \\ main :: proc() i32 {
        \\   return 42.(i32);
        \\ }
    ;
    try checkProgram(src);
}

test "hello world" {
    const src =
        \\ printf :: extern proc(*void, any) i32
        \\ main :: proc() {
        \\  printf("Hello, World!\n".^(*void))
        \\ }
    ;
    try checkProgram(src);
}

test "arithmetic operations" {
    const src =
        \\ main :: proc() i32 {
        \\   a := 10;
        \\   b := 20;
        \\   c := (a + b) * 5 - 10 / 2;
        \\   return c.(i32);
        \\ }
    ;
    try checkProgram(src);
}

test "if-else statement" {
    const src =
        \\ main :: proc() i32 {
        \\   x := 10;
        \\   if x > 5 {
        \\     return 1;
        \\   } else {
        \\     return 0;
        \\   }
        \\ }
    ;
    try checkProgram(src);
}

test "while loop" {
    const src =
        \\ main :: proc() i32 {
        \\   i := 0;
        \\   sum := 0;
        \\   while i < 10 {
        \\     sum = sum + i;
        \\     i = i + 1;
        \\   }
        \\   return sum.(i32);
        \\ }
    ;
    try checkProgram(src);
}

test "for loop over array" {
    const src =
        \\  main :: proc() i32 {
        \\    arr := [1, 2, 3, 4, 5];
        \\    sum := 0;
        \\    for x in arr {
        \\      sum = sum + x;
        \\    }
        \\    return sum.(i32);
        \\  }
    ;
    try checkProgram(src);
}

test "function call with arguments" {
    const src =
        \\  add :: proc(a: i32, b: i32) i32 {
        \\    return a + b;
        \\  }
        \\  main :: proc() i32 {
        \\    return add(10, 20);
        \\  }
    ;
    try checkProgram(src);
}

test "struct definition and access" {
    const src =
        \\ Point :: struct { x: i32, y: i32 }
        \\ main :: proc() i32 {
        \\   p := Point{ x: 10, y: 20 };
        \\   return p.x;
        \\ }
    ;
    try checkProgram(src);
}

test "array access" {
    const src =
        \\main :: proc() i32 {
        \\  arr := [10, 20, 30];
        \\  return arr[1];
        \\}
    ;
    try checkProgram(src);
}

test "casts" {
    const src =
        \\ main :: proc() i32 {
        \\   f_val: f32 = 123.45;
        \\   i_val: i64 = 1000;
        \\   _ = f_val.(i32); // Normal cast
        \\   _ = i_val.^f32; // Bitcast
        \\   _ = i_val.|i8;  // Saturating cast
        \\   _ = (254 + 5).%u8; // Wrapping cast
        \\   _ = i_val.?i8; // Checked cast
        \\   return 0;
        \\ }
    ;
    try checkProgram(src);
}
