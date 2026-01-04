const std = @import("std");
const testing = std.testing;
const compiler = @import("compiler");
const CST = compiler.cst.CST;
const Lower = compiler.lower_to_ast.Lower;
const Checker = compiler.checker.Checker;
const Parser = compiler.parser.Parser;
const diag = compiler.diagnostics;
const SymbolStore = compiler.symbols.SymbolStore;

const gpa = testing.allocator;

fn checkProgram(src: [:0]const u8, expected: []const diag.DiagnosticCode) !void {
    var context = compiler.compile.Context.init(gpa); // Create context
    defer context.deinit();

    // Step 1: Parse
    var parser = Parser.init(gpa, src, 0, context.diags, &context); // Pass file_id and context
    var cst = try parser.parse();
    defer cst.deinit();
    if (context.diags.count() != 0) { // Use context.diags
        // print tokens for debugging
        var tokenizer = compiler.lexer.Tokenizer.init(src, 0, .semi); // Add file_id
        while (true) {
            const token = tokenizer.next();
            if (token.tag == .eof) break;
            std.debug.print("Token: {any}\n", .{token.tag});
        }
        std.debug.print(
            "Errors during parsing: {}\n",
            .{context.diags.messages.items[0].code},
        );
    }
    try testing.expectEqual(0, context.diags.count());

    // Step 2: Lower to AST
    var lower = try Lower.init(gpa, &cst, &context, 0);
    defer lower.deinit();
    var result = try (&lower).run();
    defer result.deinit(gpa);
    const ast = result.ast_unit;

    // Step 3: Type Check
    var pipeline = compiler.pipeline.Pipeline.init(gpa, &context);
    const ctx_ptr = try gpa.create(Checker.CheckerContext);
    ctx_ptr.* = Checker.CheckerContext{
        .symtab = SymbolStore.init(gpa),
        .spec_arena = std.heap.ArenaAllocator.init(gpa),
        .temp_arena = std.heap.ArenaAllocator.init(gpa),
    };
    // No defer ctx_ptr.deinit() or gpa.destroy(ctx_ptr) - Checker.deinit will handle it.

    var checker = Checker.init(gpa, &context, &pipeline);
    defer checker.deinit();
    try checker.checker_ctx.resize(gpa, ast.file_id + 1);
    checker.checker_ctx.items[ast.file_id] = ctx_ptr;
    try checker.runAst(ast, ctx_ptr);

    testing.expectEqual(expected.len, context.diags.count()) catch |err| {
        std.debug.print("Expected {} diagnostics, but got {}.\n", .{ expected.len, context.diags.count() });
        for (context.diags.messages.items) |msg| {
            std.debug.print("  - Diagnostic: {}\n", .{msg.code});
        }
        return err;
    };

    for (expected, 0..) |code, i| {
        try testing.expectEqual(code, context.diags.messages.items[i].code);
    }
}

test "simple program" {
    const src =
        \\ main :: proc() i32 {
        \\   return 42
        \\ }
    ;
    try checkProgram(src, &.{});
}

test "hello world" {
    const src =
        \\ printf :: extern proc(*void, any) i32
        \\ main :: proc() {
        \\   printf("Hello, World!\n".ptr.^*void)
        \\ }
    ;
    try checkProgram(src, &.{});
}

test "test declaration uses builtin Error type" {
    const src =
        \\test "sample" {
        \\}
    ;
    try checkProgram(src, &.{});
}

test "integer expressions" {
    // Binary operations
    try checkProgram("a :: 2 + 3", &.{});
    try checkProgram("a :: 2 - 3", &.{});
    try checkProgram("a :: 2 * 3", &.{});
    try checkProgram("a :: 6 / 3", &.{});
    try checkProgram("a :: 7 % 3", &.{});
    try checkProgram("a :: 1 << 2", &.{});
    try checkProgram("a :: 4 >> 1", &.{});
    try checkProgram("a :: 5 & 3", &.{}); // 101 & 011 = 001 (1)
    try checkProgram("a :: 5 | 3", &.{}); // 101 | 011 = 111 (7)
    try checkProgram("a :: 5 ^ 3", &.{}); // 101 ^ 011 = 110 (6)
    try checkProgram("a :: 2 == 3", &.{});
    try checkProgram("a :: 2 != 3", &.{});
    try checkProgram("a :: 2 < 3", &.{});
    try checkProgram("a :: 2 <= 3", &.{});
    try checkProgram("a :: 2 > 3", &.{});
    try checkProgram("a :: 2 >= 3", &.{});

    // Saturated and wrapping operations
    try checkProgram("a :: 10 *| 20", &.{});
    try checkProgram("a :: 10 +| 20", &.{});
    try checkProgram("a :: 30 -| 10", &.{});
    try checkProgram("a :: 1 <<| 2", &.{});
    try checkProgram("a :: 10 *% 20", &.{});
    try checkProgram("a :: 10 +% 20", &.{});
    try checkProgram("a :: 30 -% 10", &.{});

    // Unary operations
    try checkProgram("a :: +5", &.{});
    try checkProgram("a :: -5", &.{});
    try checkProgram("a :: !true", &.{});

    // Combined operations and parentheses
    try checkProgram("a :: (2 + 3) * 4", &.{});
    try checkProgram("a :: 10 - (2 * 3)", &.{});
    try checkProgram("a :: 10 / 2 + 3", &.{});
    try checkProgram("a :: 10 + 2 / 3", &.{});
    try checkProgram("a :: (5 & 3) | (1 << 2)", &.{});
    try checkProgram("a :: 1 + 2 * 3 - 4 / 2", &.{});
}

test "floating point expressions" {
    // Binary operations
    try checkProgram("a :: 2.0 + 3.0", &.{});
    try checkProgram("a :: 2.0 - 3.0", &.{});
    try checkProgram("a :: 2.0 * 3.0", &.{});
    try checkProgram("a :: 6.0 / 3.0", &.{});
    try checkProgram("a :: 2.0 == 3.0", &.{});
    try checkProgram("a :: 2.0 != 3.0", &.{});
    try checkProgram("a :: 2.0 < 3.0", &.{});
    try checkProgram("a :: 2.0 <= 3.0", &.{});
    try checkProgram("a :: 2.0 > 3.0", &.{});
    try checkProgram("a :: 2.0 >= 3.0", &.{});

    // Unary operations
    try checkProgram("a :: +5.0", &.{});
    try checkProgram("a :: -5.0", &.{});

    // Combined operations and parentheses
    try checkProgram("a :: (2.0 + 3.0) * 4.0", &.{});
    try checkProgram("a :: 10.0 - (2.0 * 3.0)", &.{});
    try checkProgram("a :: 10.0 / 2.0 + 3.0", &.{});
    try checkProgram("a :: 1.0 + 2.0 * 3.0 - 4.0 / 2.0", &.{});
}

test "floating point expression failure cases" {
    // Division by zero
    try checkProgram("a :: 5.0 / 0.0", &[_]diag.DiagnosticCode{.division_by_zero});
    try checkProgram("a :: 5.0 % 0.0", &[_]diag.DiagnosticCode{.invalid_binary_op_operands}); // Modulo with floats is often disallowed or has specific rules

    // Type mismatch for binary operations
    try checkProgram("a :: 5.0 + true", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    // Mixed numeric operands now coerce literals to the other side.
    try checkProgram("a :: 5.0 - 3", &.{});
    try checkProgram("a :: 5.0 * \"hello\"", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});

    // Type mismatch for unary operations
    try checkProgram("a :: !5.0", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});
    try checkProgram("a :: -true", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});
}

test "integer expression failure cases" {
    // Division by zero
    try checkProgram("a :: 5 / 0", &[_]diag.DiagnosticCode{.division_by_zero});
    try checkProgram("a :: 5 % 0", &[_]diag.DiagnosticCode{.division_by_zero});

    // Type mismatch for unary operations
    try checkProgram("a :: !5", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});
    try checkProgram("a :: -true", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});
    try checkProgram("a :: +true", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});
    try checkProgram("a :: -\"hello\"", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});

    // Type mismatch for binary operations
    try checkProgram("a :: 5 + true", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: 5 - \"hello\"", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: 5 * 3.0", &.{});
    try checkProgram("a :: 5 << true", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: 5 & false", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: true | 1", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: 1 == \"hello\"", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: 1 < 3.0", &.{});
    try checkProgram("a :: 10 *| true", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: 10 +% \"20\"", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
}

test "integer literal failure cases" {
    try checkProgram("a :: 0b102", &[_]diag.DiagnosticCode{.invalid_integer_literal});
    try checkProgram("a :: 0o9", &[_]diag.DiagnosticCode{.invalid_integer_literal});
    try checkProgram("a :: 0xG", &[_]diag.DiagnosticCode{.invalid_integer_literal});
    try checkProgram("a :: 0x_", &[_]diag.DiagnosticCode{.invalid_integer_literal});
    try checkProgram("a :: 0b_", &[_]diag.DiagnosticCode{.invalid_integer_literal});
    try checkProgram("a :: 340282366920938463463374607431768211456", &[_]diag.DiagnosticCode{.invalid_integer_literal});
}

test "numeric literal coercion" {
    try checkProgram(
        \\ f: f32 = 1.5
        \\ result :: f + 2
    , &.{});

    try checkProgram(
        \\ foo :: proc(x: f32) {}
        \\ foo(2)
    , &.{});

    try checkProgram(
        \\ mix :: proc(a: f64, b: f32) {}
        \\ mix(2, 3)
    , &.{});

    try checkProgram(
        \\ make :: proc() f32 {
        \\   value: f32 = 0
        \\   value = 2
        \\   return value
        \\ }
    , &.{});

    try checkProgram(
        \\ Point :: struct { x: f32, y: i64 }
        \\ p :: Point{ x: 2.0, y: 3 }
    , &.{});

    try checkProgram(
        \\ wrap :: proc(x: f32) f32 { return x }
        \\ result :: wrap(2)
    , &.{});

    try checkProgram("a :: 5.0 - 3", &.{});
    try checkProgram("a :: 5 * 3.0", &.{});
    try checkProgram("a :: 1 < 3.0", &.{});
}

test "boolean expressions" {
    // Binary operations
    try checkProgram("a :: true and false", &.{});
    try checkProgram("a :: true or false", &.{});
    try checkProgram("a :: true == false", &.{});
    try checkProgram("a :: true != false", &.{});

    // Unary operations
    try checkProgram("a :: !true", &.{});

    // Combined operations and parentheses
    try checkProgram("a :: (true and false) or true", &.{});
    try checkProgram("a :: !(true or false) and true", &.{});
}

test "boolean expression failure cases" {
    // Type mismatch for unary operations
    try checkProgram("a :: !5", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});
    try checkProgram("a :: !3.0", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});
    try checkProgram("a :: !\"hello\"", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});

    // Type mismatch for binary operations
    try checkProgram("a :: true and 5", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: false or 3.0", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: true == \"hello\"", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: false != 1", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
}

test "mixed type expression failure cases" {
    try checkProgram("a :: 5 + true", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: 3.0 * false", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: 10 - null", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: true / 2", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: 5.0 and false", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: \"hello\" or true", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: 5 == true", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: 3.0 != false", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
}

test "control flow failure cases" {
    try checkProgram("main :: proc() { if 1 { } }", &[_]diag.DiagnosticCode{.non_boolean_condition});
    try checkProgram("main :: proc() { while 0 { } }", &[_]diag.DiagnosticCode{.non_boolean_condition});
    try checkProgram("x := if true { 1 } else { 2.0 }", &[_]diag.DiagnosticCode{.if_branch_type_mismatch});
    try checkProgram("main :: proc() { break }", &[_]diag.DiagnosticCode{.break_outside_loop});
    try checkProgram("main :: proc() { continue }", &[_]diag.DiagnosticCode{.continue_outside_loop});
    try checkProgram("r := 1..2.0", &[_]diag.DiagnosticCode{.range_type_mismatch});
    try checkProgram(
        \\ Color :: enum {Red, Green}
        \\ c := Color.Red
        \\ x := match c { Color.Red => 1, }
    , &[_]diag.DiagnosticCode{.non_exhaustive_match});
    try checkProgram(
        \\ x := 1
        \\ y := match x { _ => 0, 1 => 1, }
    , &[_]diag.DiagnosticCode{.unreachable_match_arm});
    try checkProgram(
        \\ flag := true
        \\ v := (L: while true {
        \\   if flag {
        \\     flag = false
        \\     break :L 1
        \\   } else {
        \\     break :L 2.0
        \\   }
        \\ })
    , &[_]diag.DiagnosticCode{.loop_break_value_type_conflict});
}

test "declarations and calls failure cases" {
    try checkProgram("main :: proc() { f := 1; f() }", &[_]diag.DiagnosticCode{.call_non_callable});
    try checkProgram("main :: proc() { missing(1) }", &[_]diag.DiagnosticCode{.unknown_function});
    try checkProgram(
        \\ add :: fn(a: i32, b: i32) i32 { return a + b }
        \\ main :: proc() { add(1) }
    , &[_]diag.DiagnosticCode{.argument_count_mismatch});
    try checkProgram(
        \\ add :: fn(a: i32, b: i32) i32 { return a + b }
        \\ main :: proc() { add(1, true) }
    , &[_]diag.DiagnosticCode{.argument_type_mismatch});
    try checkProgram(
        \\ Point :: struct { x: i32 }
        \\ main :: proc() { p := Point{ x: 1 }; _ = p.y }
    , &[_]diag.DiagnosticCode{.unknown_struct_field});
    try checkProgram("main :: proc() { t := (1, 2); _ = t.2 }", &[_]diag.DiagnosticCode{.tuple_index_out_of_bounds});
    try checkProgram("main :: proc() { _ = (1).x }", &[_]diag.DiagnosticCode{.field_access_on_non_aggregate});
    try checkProgram(
        \\ foo :: proc(a: i32, b: i32 = 2) {}
        \\ main :: proc() { foo() }
    , &[_]diag.DiagnosticCode{.argument_count_mismatch});
}

test "core data structures failure cases" {
    try checkProgram(
        \\ arr: [3]i32 = [1, 2]
    , &[_]diag.DiagnosticCode{.array_length_mismatch});
    try checkProgram(
        \\ arr: [2]i32 = [1, 2, 3]
    , &[_]diag.DiagnosticCode{.array_length_mismatch});
    try checkProgram(
        \\ arr: [3]i32 = [1, 2.0, 3]
    , &[_]diag.DiagnosticCode{.heterogeneous_array_elements});
    try checkProgram(
        \\ arr: [1.5]i32 = [1]
    , &[_]diag.DiagnosticCode{.array_size_not_integer_literal});
    try checkProgram(
        \\ Point :: struct { x: i32, y: i32 }
        \\ p := Point{ x: 1 }
    , &[_]diag.DiagnosticCode{.struct_missing_field});
    try checkProgram(
        \\ Point :: struct { x: i32 }
        \\ p := Point{ x: 1, z: 2 }
    , &[_]diag.DiagnosticCode{.unknown_struct_field});
    try checkProgram(
        \\ t: (i32, i32) = (1,)
    , &[_]diag.DiagnosticCode{.tuple_arity_mismatch});
    try checkProgram(
        \\ Color :: enum {Red, Blue}
        \\ Other :: enum {Red}
        \\ c: Color = Other.Red
    , &[_]diag.DiagnosticCode{.type_annotation_mismatch});
}

test "casts and conversions failure cases" {
    try checkProgram("x := \"s\".?i32", &[_]diag.DiagnosticCode{.invalid_checked_cast});
    try checkProgram("x := \"s\".%i32", &[_]diag.DiagnosticCode{.numeric_cast_on_non_numeric});
    try checkProgram("x := \"s\".|i32", &[_]diag.DiagnosticCode{.numeric_cast_on_non_numeric});
    try checkProgram("x := \"s\".^i32", &[_]diag.DiagnosticCode{.invalid_bitcast});
    try checkProgram("x := \"s\".(i32)", &[_]diag.DiagnosticCode{.invalid_cast});
}

test "patterns and destructuring failure cases" {
    try checkProgram(
        \\ v := 1
        \\ r := match v { "s" => 0, _ => 1, }
    , &[_]diag.DiagnosticCode{.pattern_type_mismatch});
    try checkProgram(
        \\ Point :: struct { x: i32, y: i32 }
        \\ p := Point{ x: 1, y: 2 }
        \\ r := match p { Point {x: 1, z: 2} => 0, _ => 1, }
    , &[_]diag.DiagnosticCode{.struct_pattern_field_mismatch});
    try checkProgram(
        \\ V :: variant { A(i32), B }
        \\ v := V.A(1)
        \\ r := match v { V.A(x, y) => 0, _ => 1, }
    , &[_]diag.DiagnosticCode{.tuple_arity_mismatch});
    try checkProgram(
        \\ v := 1
        \\ r := match v { y @ "s" => 0, _ => 1,}
    , &[_]diag.DiagnosticCode{.pattern_type_mismatch});
    try checkProgram(
        \\ v := 5
        \\ r := match v { 1 | 2 => 0, 2 => 1, _ => 2, }
    , &[_]diag.DiagnosticCode{.overlapping_match_arm});
}

test "interop and runtime failure cases" {
    try checkProgram(
        \\ printf :: extern proc(*void, any) i32
        \\ r := printf()
    , &[_]diag.DiagnosticCode{.argument_count_mismatch});
    try checkProgram(
        \\ printf :: extern proc(*void, any) i32
        \\ r := printf(1, 2)
    , &[_]diag.DiagnosticCode{.argument_type_mismatch});
    try checkProgram(
        \\ printf :: extern proc(*const u8, any) i32
        \\ r := printf(null)
    , &[_]diag.DiagnosticCode{.argument_type_mismatch});
    try checkProgram(
        \\ p: *i32 = null
        \\ _ = p.*
    , &[_]diag.DiagnosticCode{.assign_null_to_non_optional});
}

test "imaginary number expressions" {
    // Binary operations
    try checkProgram("a :: 2i + 3i", &.{});
    try checkProgram("a :: 2i - 3i", &.{});
    try checkProgram("a :: 2i * 3i", &.{});
    try checkProgram("a :: 6i / 3i", &.{});
    try checkProgram("a :: 2i == 3i", &.{});
    try checkProgram("a :: 2i != 3i", &.{});

    // Unary operations
    try checkProgram("a :: +5i", &.{});
    try checkProgram("a :: -5i", &.{});

    // Combined operations and parentheses
    try checkProgram("a :: (2i + 3i) * 4i", &.{});
    try checkProgram("a :: 10i - (2i * 3i)", &.{});
    try checkProgram("a :: 10i / 2i + 3i", &.{});
    try checkProgram("a :: 1i + 2i * 3i - 4i / 2i", &.{});
}

test "imaginary number expression failure cases" {
    // Division by zero
    try checkProgram("a :: 5i / 0i", &[_]diag.DiagnosticCode{.division_by_zero});

    // Type mismatch for unary operations
    try checkProgram("a :: !5i", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});
    try checkProgram("a :: -true", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});
    try checkProgram("a :: +\"hello\"", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});

    // Type mismatch for binary operations
    try checkProgram("a :: 5i + true", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: 5i * 3.0", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: 5i << true", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: 5i & false", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: true | 1i", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: 1i == \"hello\"", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: 1i < 3.0", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
}

test "additional arithmetic typing" {
    // Valid integer bitwise and shifts
    try checkProgram("a :: 5 % 2", &.{});
    try checkProgram("a :: 8 & 3", &.{});
    try checkProgram("a :: 8 | 3", &.{});
    try checkProgram("a :: 8 ^ 3", &.{});
    try checkProgram("a :: 8 << 1", &.{});
    try checkProgram("a :: 8 >> 1", &.{});

    // Invalid mixes: int vs float
    try checkProgram("a :: 1 == 1.0", &[_]diag.DiagnosticCode{});
    try checkProgram("a :: 5.0 & 1", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: 5.0 << 1", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("a :: 5 << 1.0", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});

    // Invalid boolean comparisons
    try checkProgram("a :: true < false", &[_]diag.DiagnosticCode{});

    // Address-of on rvalue (currently allowed in typing)
    try checkProgram("a :: &5", &.{});
}

test "array literals - success" {
    // Basic homogeneous int array
    try checkProgram("a :: [1, 2, 3]", &.{});

    // Nested arrays (2x2)
    try checkProgram("a :: [[1, 2], [3, 4]]", &.{});

    // Typed fixed-size array declaration with matching literal length
    try checkProgram("arr: [3]i32 = [1, 2, 3]", &.{});

    // Array of strings
    try checkProgram("s :: [\"a\", \"b\", \"c\"]", &.{});

    // Indexing into an array literal
    try checkProgram("x :: [10, 20, 30][1]", &.{});

    // Slicing a literal via parentheses
    try checkProgram("sl :: ([1,2,3,4])[1..3]", &.{});
}

test "array literals - failures" {
    // Heterogeneous array elements should be rejected
    try checkProgram("a :: [1, \"a\", 3]", &[_]diag.DiagnosticCode{.heterogeneous_array_elements});

    // Fixed-size typed array with too few/many elements
    try checkProgram("arr: [3]i32 = [1, 2]", &[_]diag.DiagnosticCode{.array_length_mismatch});
    try checkProgram("arr: [2]i32 = [1, 2, 3]", &[_]diag.DiagnosticCode{.array_length_mismatch});

    // Mixed numeric kinds (int vs float) in one literal
    try checkProgram("a :: [1, 2.0, 3]", &[_]diag.DiagnosticCode{.heterogeneous_array_elements});

    // Using non-literal or invalid element forms (e.g., unsupported type in literal)
    try checkProgram("a :: [true, 1]", &[_]diag.DiagnosticCode{.heterogeneous_array_elements});
}

test "tuple literals - success" {
    // Heterogeneous tuple literal
    try checkProgram("t :: (1, \"hello\", true)", &.{});

    // Field access by index
    try checkProgram("x :: (1, 2, 3).0", &.{});

    // Nested tuple indexing
    try checkProgram("y :: ((1, 2), (3, 4)).1.0", &.{});

    // Typed tuple variable
    try checkProgram("c: (i32, f64, char) = (1, 2.0, 'x')", &.{});
}

test "tuple literals - failures" {
    // Tuple does not support direct arithmetic
    try checkProgram("a :: (1, 2) + 3", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});

    // Mixed types via field access leading to invalid binary op
    try checkProgram("b :: (1, \"a\").0 + \"str\"", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});

    // Out-of-bounds tuple field index
    try checkProgram("oob :: (1, 2).2 + 1", &[_]diag.DiagnosticCode{.tuple_index_out_of_bounds});

    // Invalid tuple field name (non-numeric)
    try checkProgram("bad :: (1, 2).a + 1", &[_]diag.DiagnosticCode{.expected_field_name_or_index});
}

test "map literals - success" {
    // Basic string->int map
    try checkProgram("m :: [\"one\": 1, \"two\": 2]", &.{});

    // Int->string map
    try checkProgram("n :: [1: \"one\", 2: \"two\"]", &.{});

    // Typed empty map
    try checkProgram("empty: [string: i32] = []", &.{});

    // Index into a map literal
    try checkProgram("v :: [\"a\": 1, \"b\": 2][\"b\"]", &.{});
}

test "map literals - failures" {
    // Mixed key types should be rejected
    try checkProgram("m :: [\"one\": 1, 2: 2]", &[_]diag.DiagnosticCode{.map_mixed_key_types});

    // Mixed value types should be rejected
    try checkProgram("m :: [\"one\": 1, \"two\": \"2\"]", &[_]diag.DiagnosticCode{.map_mixed_value_types});

    // Empty without type annotation is ambiguous
    try checkProgram("m :: []", &[_]diag.DiagnosticCode{.cannot_infer_type_from_empty_array});

    // Annotation/value mismatch
    try checkProgram("bad: [string: i32] = [\"x\": 1, \"y\": 2.0]", &[_]diag.DiagnosticCode{.map_mixed_value_types});

    // Index with wrong key type
    try checkProgram("w :: [\"a\": 1, \"b\": 2][1]", &[_]diag.DiagnosticCode{.map_wrong_key_type});
}

test "string and char literals - success" {
    // Plain string
    try checkProgram("s1 :: \"hello\"", &.{});

    // Raw strings
    try checkProgram("s2 :: r\"no escapes \\n \"", &.{});
    try checkProgram("s3 :: r#\"hash \" inside\"#", &.{});

    // Unicode in string and char
    try checkProgram("su :: \"π\"", &.{});
    try checkProgram("c1 :: 'a'", &.{});
    try checkProgram("c2 :: 'π'", &.{});

    // Empty string
    try checkProgram("empty :: \"\"", &.{});
}

test "string and char literals - failures" {
    // Invalid arithmetic with strings
    try checkProgram("x :: \"a\" + 1", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("y :: \"a\" - \"b\"", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});

    // Invalid unary op
    try checkProgram("z :: !\"a\"", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});

    // Indexing with wrong index type
    try checkProgram("i :: \"abc\"[1.0]", &[_]diag.DiagnosticCode{.non_integer_index});

    // Invalid comparisons across types
    try checkProgram("cmp1 :: \"a\" == true", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("cmp2 :: 'a' == 1.0", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
}

test "null/undefined literals - success" {
    // Bare literals
    try checkProgram("n : ?i32 : null", &.{});
    try checkProgram("u :: undefined", &.{});

    // Parenthesized usage
    try checkProgram("p : ?i64 : (null)", &.{});
    try checkProgram("q :: (undefined)", &.{});
}

test "null/undefined literals - failures" {
    // Arithmetic with null/undefined
    try checkProgram("x :: null + 1", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("y :: undefined * 2", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});

    // Logical/unary operations
    try checkProgram("z :: !null", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});
    try checkProgram("w :: -undefined", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});
    try checkProgram("w2 :: !undefined", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});

    // Indexing
    try checkProgram("i :: null[0]", &[_]diag.DiagnosticCode{.not_indexable});

    // Mixing in literals
    try checkProgram("arr :: [1, null]", &[_]diag.DiagnosticCode{.heterogeneous_array_elements});
    try checkProgram("tup :: (undefined, 1) + 2", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});

    // Comparisons
    try checkProgram("cmp1 :: null == 0", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("cmp2 :: undefined != false", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("cmp3 :: undefined == undefined", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("cmp4 :: undefined == null", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
}

// Builtin types: tuple, array, dynarray (type expressions and typed inits)

test "builtin types - tuple - success" {
    // Tuple type as a value (type constant)
    try checkProgram("tt :: (i32, f64, char)", &.{});

    // Typed tuple initialization
    try checkProgram("tv: (i32, f64, char) = (1, 2.0, 'x')", &.{});

    // Nested tuples
    try checkProgram("tn: ((i32, i32), (bool, string)) = ((1, 2), (true, \"ok\"))", &.{});
}

test "builtin types - tuple - failures" {
    // Arity mismatch
    try checkProgram("bad_arity: (i32, f64) = (1, 2.0, 'x')", &[_]diag.DiagnosticCode{.tuple_arity_mismatch});

    // Element type mismatch
    try checkProgram("bad_elem: (i32, f64, char) = (1, \"s\", 'x')", &[_]diag.DiagnosticCode{.expected_float_type});
}

test "builtin types - array - success" {
    // Array type as a value (type constant)
    try checkProgram("ta :: [5]i32", &.{});

    // Typed fixed-size array initialization
    try checkProgram("a1: [3]i32 = [1, 2, 3]", &.{});

    // Nested arrays (2x2)
    try checkProgram("a2: [2][2]i32 = [[1, 2], [3, 4]]", &.{});
}

test "builtin types - array - failures" {
    // Non-integer size
    try checkProgram("a_bad: [1.5]i32", &[_]diag.DiagnosticCode{.array_size_not_integer_literal});

    // Length mismatch vs type
    try checkProgram("a_len1: [3]i32 = [1, 2]", &[_]diag.DiagnosticCode{.array_length_mismatch});
    try checkProgram("a_len2: [2]i32 = [1, 2, 3]", &[_]diag.DiagnosticCode{.array_length_mismatch});

    // Element type mismatch
    try checkProgram("a_elem: [3]i32 = [1, \"x\", 3]", &[_]diag.DiagnosticCode{.heterogeneous_array_elements});
}

test "array length resolved from comptime expression" {
    const code =
        \\Vec :: fn(comptime T: type, comptime N: usize) type {
        \\  return struct { data: [N]T };
        \\}
        \\Matrix :: fn(comptime T: type, comptime R: usize, comptime C: usize) type {
        \\  Row :: Vec(T, C)
        \\  return struct { rows: [R]Row };
        \\}
        \\MatrixI32x2x3 :: Matrix(i32, 2, 3)
    ;
    try checkProgram(code, &.{});
}

test "builtin types - dynarray - success" {
    // Dynarray type as a value (type constant)
    try checkProgram("dt :: [dyn]u8", &.{});

    // Assigning a literal to dynarray-typed variable
    try checkProgram("dv: [dyn]u8 = [1, 2, 3]", &.{});
}

test "builtin types - dynarray - failures" {
    // Element type mismatch
    try checkProgram("de: [dyn]u8 = [\"a\"]", &[_]diag.DiagnosticCode{.expected_integer_type});

    // Non-array initializer
    try checkProgram("dx: [dyn]u8 = 1", &[_]diag.DiagnosticCode{.expected_array_type});
}

test "builtin types - slice - success" {
    // Slice type as a value (type constant)
    try checkProgram("st :: []i32", &.{});

    // Slice initialization from array slice expression
    try checkProgram("sv: []i32 = ([1,2,3,4])[1..3]", &.{});

    // Assign slice to const slice
    try checkProgram(
        \\
        \\ arr: [3]i32 = [1, 2, 3]
        \\ cs: []const i32 = arr[0..2]
    , &.{});
}

test "builtin types - slice - failures" {
    // Invalid initializer types
    try checkProgram("sx: []i32 = 123", &[_]diag.DiagnosticCode{.type_annotation_mismatch});
    try checkProgram("sn: []i32 = null", &[_]diag.DiagnosticCode{.assign_null_to_non_optional});

    // Assign const slice to mutable slice
    try checkProgram(
        \\
        \\ arr: [3]i32 = [1, 2, 3]
        \\ cs: []const i32 = arr[0..2]
        \\ ms: []i32 = cs
    , &[_]diag.DiagnosticCode{.slice_constness_violation});
}

test "builtin types - map - success" {
    // Map type as a value (type constant)
    try checkProgram("mt :: [string: i32]", &.{});

    // Typed map initialization
    try checkProgram("mv: [string: i32] = [\"a\":1, \"b\":2]", &.{});
}

test "builtin types - map - failures" {
    // Wrong key/value types
    try checkProgram("mk: [string: i32] = [1:1]", &[_]diag.DiagnosticCode{.map_wrong_key_type});
    try checkProgram("mv2: [string: i32] = [\"a\":1.5]", &[_]diag.DiagnosticCode{.expected_integer_type});

    // Null not assignable without optional
    try checkProgram("mn: [string: i32] = null", &[_]diag.DiagnosticCode{.assign_null_to_non_optional});
}

test "builtin types - optional - success" {
    // Optional type as value
    try checkProgram("ot :: ?i32", &.{});

    // Assign value and null
    try checkProgram("ov: ?i32 = 5", &.{});
    try checkProgram("on: ?i32 = null", &.{});
    try checkProgram("os: ?string = null", &.{});
}

test "builtin types - optional - failures" {
    // Mismatched initializer
    try checkProgram("ob: ?i32 = \"s\"", &[_]diag.DiagnosticCode{.expected_integer_type});

    // Null to non-optional
    try checkProgram("oi: i32 = null", &[_]diag.DiagnosticCode{.assign_null_to_non_optional});
}

test "builtin types - optional - comparison failures" {
    const src =
        \\opt: ?i32 = 1
        \\cmp :: opt == "s"
    ;
    try checkProgram(src, &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
}

// Builtin types: struct (type expressions, literals, field access)

test "struct types - success" {
    // Struct type constant
    try checkProgram("Point :: struct { x: i32, y: i32 }", &.{});

    // Literal initialization (same line)
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ p :: Point{ x: 1, y: 2 }
    , &.{});

    // Field access
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ v :: Point{ x: 1, y: 2 }.x
    , &.{});

    // Reordered fields in literal
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ p :: Point{ y: 2, x: 1 }
    , &.{});

    // Nested struct
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ Outer :: struct { p: Point, z: i32 }
        \\ o :: Outer{ p: Point{ x: 1, y: 2 }, z: 3 }
    , &.{});

    // Optional field accepting null
    try checkProgram(
        \\
        \\ Cfg :: struct { name: ?string, id: i32 }
        \\ c :: Cfg{ name: null, id: 1 }
    , &.{});
}

test "struct types - failures" {
    // Field type mismatch
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ p :: Point{ x: "a", y: 2 }
    , &[_]diag.DiagnosticCode{.struct_field_type_mismatch});

    // Missing required field
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ p :: Point{ x: 1 }
    , &[_]diag.DiagnosticCode{.struct_missing_field});

    // Extra field
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ p :: Point{ x: 1, y: 2, z: 3 }
    , &[_]diag.DiagnosticCode{.unknown_struct_field});

    // Null to non-optional field
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ p :: Point{ x: null, y: 2 }
    , &[_]diag.DiagnosticCode{.struct_field_type_mismatch});

    // Access non-existing field
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ v :: Point{ x: 1, y: 2 }.z
    , &[_]diag.DiagnosticCode{.unknown_struct_field});
}

// Builtin types: enums (C-style and integer-backed), tag usage

test "enum types - success" {
    // Simple enum type and tag usage
    try checkProgram(
        \\
        \\ State :: enum { Running, Walking }
        \\ s :: State.Running
    , &.{});

    // Integer-backed enum with explicit values
    try checkProgram(
        \\
        \\ Byte :: enum(u8) { A = 1, B = 2 }
        \\ b :: Byte.B
    , &.{});
}

test "enum types - failures" {
    // Duplicate tags
    try checkProgram("E :: enum { A, A }", &[_]diag.DiagnosticCode{.duplicate_enum_field});

    // Unknown tag usage
    try checkProgram(
        \\
        \\ State :: enum { Running, Walking }
        \\ s :: State.Flying
    , &[_]diag.DiagnosticCode{.unknown_enum_tag});

    // Assigning tag of one enum to another enum type
    try checkProgram(
        \\
        \\ A :: enum { X }
        \\ B :: enum { X }
        \\ v: A = B.X
    , &[_]diag.DiagnosticCode{.type_annotation_mismatch});

    // Non-integer discriminant value
    try checkProgram("Bad :: enum(u8) { A = 1.5 }", &[_]diag.DiagnosticCode{.enum_discriminant_not_integer});
}

// Builtin types: variants (sum types with tuple/struct payloads)

test "variant types - success" {
    // Define a variant with no payload, tuple-like payload, and struct-like payload
    try checkProgram(
        \\
        \\ Variant :: variant { A, B(i32), C{ x: i32, y: i32 } }
        \\ v1 :: Variant.A
        \\ v2 :: Variant.B(123)
        \\ v3 :: Variant.C{ x: 1, y: 2 }
    , &.{});
}

test "variant types - failures" {
    // Duplicate variant tag
    try checkProgram("VarDup :: variant { A, A }", &[_]diag.DiagnosticCode{.duplicate_variant});

    // Wrong tuple payload type
    try checkProgram(
        \\
        \\ Variant :: variant { A, B(i32) }
        \\ v :: Variant.B("s")
    , &[_]diag.DiagnosticCode{.argument_type_mismatch});

    // Missing/extra tuple payload
    try checkProgram(
        \\
        \\ Variant :: variant { B(i32) }
        \\ v :: Variant.B
    , &[_]diag.DiagnosticCode{.variant_payload_arity_mismatch});
    try checkProgram(
        \\
        \\ Variant :: variant { B(i32) }
        \\ v :: Variant.B(1, 2)
    , &[_]diag.DiagnosticCode{.argument_count_mismatch});

    // Struct payload: missing/extra/wrong-typed fields
    try checkProgram(
        \\
        \\ V2 :: variant { C{ x: i32, y: i32 } }
        \\ v :: V2.C{ x: 1 }
    , &[_]diag.DiagnosticCode{.struct_missing_field});
    try checkProgram(
        \\
        \\ V2 :: variant { C{ x: i32, y: i32 } }
        \\ v :: V2.C{ x: 1, y: 2, z: 3 }
    , &[_]diag.DiagnosticCode{.unknown_struct_field});
    try checkProgram(
        \\
        \\ V2 :: variant { C{ x: i32, y: i32 } }
        \\ v :: V2.C{ x: "a", y: 2 }
    , &[_]diag.DiagnosticCode{.struct_field_type_mismatch});

    // Null to non-optional field in struct payload
    try checkProgram(
        \\
        \\ V3 :: variant { P{ x: i32, y: i32 } }
        \\ v :: V3.P{ x: null, y: 2 }
    , &[_]diag.DiagnosticCode{.struct_field_type_mismatch});
}

// Builtin types: unions and error sets

test "union types - success" {
    // Union type constant
    try checkProgram("U :: union { i: i32, f: f64, s: string }", &.{});

    // Literal initialization for each field (exactly one)
    try checkProgram(
        \\
        \\ U :: union { i: i32, f: f64, s: string }
        \\ u1 :: U{ i: 42 }
        \\ u2 :: U{ f: 3.14 }
        \\ u3 :: U{ s: "ok" }
    , &.{});

    // Nested union type and init
    try checkProgram(
        \\
        \\ U :: union { i: i32, f: f64, s: string }
        \\ OuterU :: union { left: U, right: i32 }
        \\ o1 :: OuterU{ left: U{ i: 1 } }
        \\ o2 :: OuterU{ right: 2 }
    , &.{});
}

test "union types - failures" {
    // Duplicate field name in union
    try checkProgram("DupUnion :: union { x: i32, x: i32 }", &[_]diag.DiagnosticCode{.duplicate_field});

    // More than one field in literal is invalid
    try checkProgram(
        \\
        \\ U :: union { i: i32, f: f64 }
        \\ u :: U{ i: 1, f: 2.0 }
    , &[_]diag.DiagnosticCode{.union_literal_multiple_fields});

    // Wrong field type
    try checkProgram(
        \\
        \\ U :: union { i: i32, f: f64 }
        \\ u :: U{ i: "x" }
    , &[_]diag.DiagnosticCode{.struct_field_type_mismatch});

    // Unknown field
    try checkProgram(
        \\
        \\ U :: union { i: i32 }
        \\ u :: U{ z: 1 }
    , &[_]diag.DiagnosticCode{.unknown_struct_field});

    // Empty literal
    try checkProgram(
        \\
        \\ U :: union { i: i32 }
        \\ u :: U{ }
    , &[_]diag.DiagnosticCode{.union_empty_literal});

    // Null to non-optional
    try checkProgram(
        \\
        \\ U :: union { s: string }
        \\ u :: U{ s: null }
    , &[_]diag.DiagnosticCode{.struct_field_type_mismatch});
}

test "error sets - success" {
    // Error set definition and error-union type constant
    try checkProgram(
        \\
        \\ MyErr :: error { NotFound, PermissionDenied }
        \\ RetType :: MyErr!i32
    , &.{});

    // Error union variables: value and error assignment
    try checkProgram(
        \\
        \\ MyErr :: error { NotFound, PermissionDenied }
        \\ ok: MyErr!i32 = 123
        \\ er: MyErr!i32 = MyErr.NotFound
    , &.{});
}

test "error sets - failures" {
    // Duplicate error variant
    try checkProgram("ErrDup :: error { A, A }", &[_]diag.DiagnosticCode{.duplicate_error_variant});

    // Unknown error tag
    try checkProgram(
        \\
        \\ MyErr :: error { A }
        \\ OtherErr :: error { B }
        \\ v: MyErr!i32 = OtherErr.B
    , &[_]diag.DiagnosticCode{.type_annotation_mismatch});

    // Assign error to non error-union variable
    try checkProgram(
        \\
        \\ MyErr :: error { A }
        \\ x: i32 = MyErr.A
    , &[_]diag.DiagnosticCode{.expected_integer_type});
}

// Builtin types: pointers (mutable/const), address-of, dereference, nested pointers

test "pointer types - success" {
    // Pointer type constants
    try checkProgram("mp :: *i32", &.{});
    try checkProgram("cp :: *const i32", &.{});

    try checkProgram(
        \\ a : i32 = 5
        \\ p: *i32 = &a
        \\ v :: p.*
    , &.{});

    // Nested pointers
    try checkProgram(
        \\ a : i32 = 5
        \\ pp: **i32 = &&a
        \\ v :: (pp.*).*
    , &.{});

    // Pointer to struct and field access after deref
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ p_ptr: *Point = &Point{ x: 1, y: 2 }
        \\ vx :: p_ptr.*.x
    , &.{});

    // // Auto-deref in field access
    try checkProgram(
        \\ Point :: struct { x: i32, y: i32 }
        \\ p_ptr: *Point = &Point{ x: 1, y: 2 }
        \\ vx :: p_ptr.x
    , &.{});

    // Pointer to const
    try checkProgram("cptr: *const i32 = &5", &.{});
}

test "pointer types - failures" {
    // Wrong pointee type
    try checkProgram("p: *i32 = &\"s\"", &[_]diag.DiagnosticCode{.pointer_type_mismatch});

    // Deref non-pointer
    try checkProgram("v :: 5.*", &[_]diag.DiagnosticCode{.deref_non_pointer});

    // Assign null to non-optional pointer
    try checkProgram("p: *i32 = null", &[_]diag.DiagnosticCode{.assign_null_to_non_optional});

    // Assign *const i32 to *i32 (loss of const)
    try checkProgram(
        \\
        \\ c: *const i32 = &5
        \\ m: *i32 = c
    , &[_]diag.DiagnosticCode{.pointer_constness_violation});
}

// Builtin types: SIMD and Tensor types

test "simd types - success" {
    // Type constants
    try checkProgram("vs4 :: simd(f32, 4)", &.{});
    try checkProgram("is8 :: simd(i32, 8)", &.{});
}

test "simd types - failures" {
    // Non-integer lanes
    try checkProgram("bad1 :: simd(i32, 2.5)", &[_]diag.DiagnosticCode{.simd_lanes_not_integer_literal});

    // Invalid element type
    try checkProgram("bad2 :: simd(string, 4)", &[_]diag.DiagnosticCode{.simd_invalid_element_type});
}

test "tensor types - success" {
    // Type constants 2D and 3D
    try checkProgram("t2 :: tensor(2, 3, i32)", &.{});
    try checkProgram("t3 :: tensor(2, 2, 2, f64)", &.{});
}

test "tensor types - failures" {
    // Non-integer dimension
    try checkProgram("bad_t1 :: tensor(2.5, 3, i32)", &[_]diag.DiagnosticCode{.tensor_dimension_not_integer_literal});

    // Mixed invalid dimension kind
    try checkProgram("bad_t2 :: tensor(2, \"x\", i32)", &[_]diag.DiagnosticCode{.tensor_dimension_not_integer_literal});
}

// Builtin types: type, any, noreturn

test "type/any/noreturn - success" {
    // 'type' as a type constant and variable of type 'type'
    try checkProgram("tt :: type", &.{});
    try checkProgram("tv: type = i32", &.{});

    // 'noreturn' for diverging function type
    try checkProgram("nt :: noreturn", &.{});
    try checkProgram("df :: fn() noreturn", &.{});
}

test "type/any/noreturn - failures" {
    // Assign non-type to a 'type' variable
    try checkProgram("bad_t1: type = 123", &[_]diag.DiagnosticCode{.type_value_mismatch});

    // Use 'any' in arithmetic without concrete type
    try checkProgram("bad_a1 :: any + 1", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});

    // 'any' is only allowed in parameter types
    try checkProgram("at :: any", &[_]diag.DiagnosticCode{.invalid_any_type_annotation});

    // 'any' is not allowed as a value type annotation
    try checkProgram("av1: any = 123", &[_]diag.DiagnosticCode{.invalid_any_type_annotation});

    // 'noreturn' is not a storable value type
    try checkProgram("bad_n1: noreturn = 0", &[_]diag.DiagnosticCode{.noreturn_not_storable});
}

// Identifiers: naming rules, raw identifiers for keywords, and field names

test "identifiers - success" {
    // Simple identifiers
    try checkProgram("id1 :: 1", &.{});
    try checkProgram("_hidden :: 2", &.{});
    try checkProgram("foo_bar123 :: 3", &.{});

    // PascalCase as a value identifier (allowed in this language)
    try checkProgram("CamelCase :: 4", &.{});

    // Raw identifier to use a keyword as an identifier
    try checkProgram("r#and :: 5", &.{});

    // Raw identifier as a struct field name
    try checkProgram(
        \\
        \\ S :: struct { r#and: i32, value: i32 }
        \\ s :: S{ r#and: 1, value: 2 }
    , &.{});
}

test "identifiers - failures" {
    // Starts with a digit (parse-level error expected)
    try checkProgram("1abc :: 1", &[_]diag.DiagnosticCode{.expected_pattern_on_decl_lhs});

    // Hyphen not allowed in identifier
    try checkProgram("foo-bar :: 1", &[_]diag.DiagnosticCode{.expected_pattern_on_decl_lhs});

    try checkProgram("r#123 :: 1", &[_]diag.DiagnosticCode{});
}

// Unary expressions: plus, minus, logical not, address-of, deref

test "unary expressions - success" {
    // Numeric plus/minus on ints and floats
    try checkProgram("a1 :: +5", &.{});
    try checkProgram("a2 :: -5", &.{});
    try checkProgram("f1 :: +5.0", &.{});
    try checkProgram("f2 :: -5.0", &.{});

    // Logical not on bool
    try checkProgram("b1 :: !false", &.{});

    // Nesting
    try checkProgram("nn :: -(-5)", &.{});
    try checkProgram("nb :: !(!true)", &.{});

    // Address-of and deref
    try checkProgram("p: *i32 = &5", &.{});
    try checkProgram("v :: (&5).*", &.{});
}

test "unary expressions - failures" {
    // Wrong operand types
    try checkProgram("u1 :: +true", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});
    try checkProgram("u2 :: -\"hello\"", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});
    try checkProgram("u3 :: !5", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});

    // Address-of invalid operand
    try checkProgram("u4: *i32 = &\"s\"", &[_]diag.DiagnosticCode{.pointer_type_mismatch});

    // Deref non-pointer
    try checkProgram("u5 :: 5.*", &[_]diag.DiagnosticCode{.deref_non_pointer});

    // Null/undefined with unary
    try checkProgram("u6 :: !null", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});
    try checkProgram("u7 :: -undefined", &[_]diag.DiagnosticCode{.invalid_unary_op_operand});
}

// Binary expressions: exhaustive success/failure matrix

test "binary expressions - success" {
    // Arithmetic (ints)
    try checkProgram("bi_add :: 1 + 2", &.{});
    try checkProgram("bi_sub :: 5 - 3", &.{});
    try checkProgram("bi_mul :: 2 * 3", &.{});
    try checkProgram("bi_div :: 6 / 3", &.{});
    try checkProgram("bi_mod :: 7 % 4", &.{});

    // Arithmetic (floats)
    try checkProgram("bf_add :: 1.0 + 2.0", &.{});
    try checkProgram("bf_sub :: 5.0 - 3.0", &.{});
    try checkProgram("bf_mul :: 2.0 * 3.0", &.{});
    try checkProgram("bf_div :: 6.0 / 3.0", &.{});

    // Bitwise and shifts (ints only)
    try checkProgram("bw_and :: 5 & 3", &.{});
    try checkProgram("bw_or :: 5 | 3", &.{});
    try checkProgram("bw_xor :: 5 ^ 3", &.{});
    try checkProgram("bw_shl :: 1 << 2", &.{});
    try checkProgram("bw_shr :: 4 >> 1", &.{});

    // Wrapping / saturating variants (ints)
    try checkProgram("wr_add :: 10 +| 20", &.{});
    try checkProgram("wr_sub :: 10 -| 1", &.{});
    try checkProgram("wr_mul :: 10 *| 2", &.{});
    try checkProgram("wr_shl :: 1 <<| 2", &.{});
    try checkProgram("sat_add :: 10 +% 20", &.{});
    try checkProgram("sat_sub :: 10 -% 1", &.{});
    try checkProgram("sat_mul :: 10 *% 2", &.{});

    // Logical (bools only)
    try checkProgram("lg_and :: true and false", &.{});
    try checkProgram("lg_or :: true or false", &.{});

    // Comparisons (ints and floats)
    try checkProgram("cmp_eq_i :: 1 == 1", &.{});
    try checkProgram("cmp_ne_i :: 1 != 2", &.{});
    try checkProgram("cmp_lt_i :: 1 < 2", &.{});
    try checkProgram("cmp_le_i :: 2 <= 2", &.{});
    try checkProgram("cmp_gt_i :: 3 > 2", &.{});
    try checkProgram("cmp_ge_i :: 3 >= 3", &.{});
    try checkProgram("cmp_eq_f :: 1.0 == 1.0", &.{});
    try checkProgram("cmp_lt_f :: 1.0 < 2.0", &.{});

    // Optional orelse
    try checkProgram(
        \\
        \\ x: ?i32 = 1
        \\ r1 :: x orelse 0
    , &.{});
    try checkProgram(
        \\
        \\ y: ?i32 = null
        \\ r2 :: y orelse 5
    , &.{});

    // Parentheses and precedence
    try checkProgram("pp1 :: 1 + 2 * 3", &.{});
    try checkProgram("pp2 :: (1 + 2) * 3", &.{});
    try checkProgram("pp3 :: (true and false) or true", &.{});
}

test "binary expressions - failures" {
    // Arithmetic: division/modulo by zero (ints and floats)
    try checkProgram("fdz1 :: 5 / 0", &[_]diag.DiagnosticCode{.division_by_zero});
    try checkProgram("fdz2 :: 5 % 0", &[_]diag.DiagnosticCode{.division_by_zero});
    try checkProgram("fdz3 :: 5.0 / 0.0", &[_]diag.DiagnosticCode{.division_by_zero});

    // Arithmetic: non-numeric
    try checkProgram("an1 :: \"a\" + \"b\"", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("an2 :: 1 + true", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("an3 :: 1.0 * false", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});

    // Bitwise and shifts: non-integer
    try checkProgram("bw1 :: 1.0 & 1", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("bw2 :: true | 1", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("bw3 :: 1 << 1.0", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("bw4 :: 1.0 >> 1", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});

    // Logical: non-bool
    try checkProgram("lg1 :: 1 and 0", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
    try checkProgram("lg2 :: \"a\" or \"b\"", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});

    // Comparisons: mismatched types and non-orderable
    try checkProgram("cm1 :: 1 == 1.0", &[_]diag.DiagnosticCode{});
    try checkProgram("cm2 :: true < false", &[_]diag.DiagnosticCode{});
    try checkProgram("cm3 :: \"a\" > \"b\"", &[_]diag.DiagnosticCode{.invalid_binary_op_operands});

    // Optional orelse misuse
    try checkProgram("or1 :: 1 orelse 0", &[_]diag.DiagnosticCode{.invalid_use_of_orelse_on_non_optional});
    try checkProgram(
        \\
        \\ x: ?i32 = 1
        \\ r :: x orelse 2.0
    , &[_]diag.DiagnosticCode{.invalid_binary_op_operands});
}

// Error handling: catch, orelse on error unions, error propagation '!', optional unwrap '?'

test "error handling - success" {
    // catch with binding and without
    try checkProgram(
        \\
        \\ MyErr :: error { A, B }
        \\ x: MyErr!i32 = 1
        \\ y :: x catch |err| { 0 }
        \\ z :: x catch { 0 }
    , &.{});

    try checkProgram(
        \\
        \\ MyErr :: error { A }
        \\ e1: MyErr!i32 = 1
        \\ e2: MyErr!i32 = MyErr.A
        \\ r1 :: e1 catch 0
        \\ r2 :: e2 catch 5
    , &.{});

    // Optional unwrap '?'
    try checkProgram(
        \\
        \\ opt: ?i32 = 5
        \\ v :: opt?
    , &.{});

    // Error propagation '!' inside a function returning error union
    try checkProgram(
        \\
        \\ MyErr :: error { A }
        \\ f :: proc() MyErr!i32 {
        \\   x: MyErr!i32 = 1
        \\   return x!
        \\ }
    , &.{});
}

test "error handling - failures" {
    // catch on non-error union
    try checkProgram("bad1 :: 1 catch |err| { 0 }", &[_]diag.DiagnosticCode{.catch_on_non_error});

    // orelse on non-error and non-optional
    try checkProgram("or_bad :: 1 orelse 0", &[_]diag.DiagnosticCode{.invalid_use_of_orelse_on_non_optional});

    // orelse default type mismatch for error union
    try checkProgram(
        \\
        \\ MyErr :: error { A }
        \\ y: MyErr!i32 = MyErr.A
        \\ r2 :: y orelse 2.0
    , &[_]diag.DiagnosticCode{.invalid_use_of_orelse_on_non_optional});

    // Optional unwrap on non-optional
    try checkProgram("u_bad :: 5?", &[_]diag.DiagnosticCode{.invalid_optional_unwrap_target});

    // Error propagation '!' on non-error union
    try checkProgram("p_bad :: 1!", &[_]diag.DiagnosticCode{.error_propagation_on_non_error});

    // Error propagation in function returning non-error type
    try checkProgram(
        \\
        \\ MyErr :: error { A }
        \\ g :: proc() i32 {
        \\   x: MyErr!i32 = 1
        \\   return x!
        \\ }
    , &[_]diag.DiagnosticCode{.error_propagation_mismatched_function_result});
}

// Call expressions: function/proc calls, function pointers, extern calls, pointer args

test "call expressions - success" {
    // Simple zero-arg returning i32
    try checkProgram(
        \\
        \\ f0 :: proc() i32 { return 1 }
        \\ r0 :: f0()
    , &.{});

    // Multi-arg with mixed types
    try checkProgram(
        \\
        \\ f1 :: proc(a: i32, b: f64, s: string) i32 { return a }
        \\ r1 :: f1(1, 2.0, "x")
    , &.{});

    // Pointer argument
    try checkProgram(
        \\
        \\ pf :: proc(p: *i32) i32 { return p.* }
        \\ r3 :: pf(&5)
    , &.{});

    // Extern call
    try checkProgram(
        \\
        \\ printf :: extern proc(*const u8, any) i32
        \\ rr :: printf("ok".ptr)
    , &.{});
}

test "call expressions - failures" {
    // Wrong arity: too few/too many
    try checkProgram(
        \\
        \\ f :: proc(a: i32, b: i32) i32 { return a }
        \\ r :: f(1)
    , &[_]diag.DiagnosticCode{.argument_count_mismatch});
    try checkProgram(
        \\
        \\ g :: proc(a: i32) i32 { return a }
        \\ r :: g(1, 2)
    , &[_]diag.DiagnosticCode{.argument_count_mismatch});

    // Wrong types
    try checkProgram(
        \\
        \\ h :: proc(a: i32, b: f64) i32 { return a }
        \\ r :: h("s", 2.0)
    , &[_]diag.DiagnosticCode{.argument_type_mismatch});

    // Call non-callable
    try checkProgram("nc :: 1(2)", &[_]diag.DiagnosticCode{.call_non_callable});

    // Passing null to non-optional pointer param
    try checkProgram(
        \\
        \\ pf :: proc(p: *i32) i32 { return 0 }
        \\ r :: pf(null)
    , &[_]diag.DiagnosticCode{.argument_type_mismatch});

    // Extern call with wrong arg types
    try checkProgram(
        \\
        \\ printf :: extern proc(*void, any) i32
        \\ rr :: printf("s", 1)
    , &[_]diag.DiagnosticCode{.argument_type_mismatch});

    // Unknown function
    try checkProgram("unk :: foo(1)", &[_]diag.DiagnosticCode{.unknown_function});
}

// Index access: arrays, slices, maps; nested access

test "index access - success" {
    // Array literal indexing
    try checkProgram("ai0 :: [10, 20, 30][0]", &.{});
    try checkProgram("ai1 :: [10, 20, 30][2]", &.{});

    // Nested array indexing
    try checkProgram("an :: [[1,2],[3,4]][1][0]", &.{});

    // Typed array variable and indexing
    try checkProgram("arr: [3]i32 = [1,2,3]", &.{});
    try checkProgram("av :: ([1,2,3])[1]", &.{});

    // Slice indexing
    try checkProgram("sl :: ([1,2,3,4])[1..3][0]", &.{});

    // Map indexing with correct key type
    try checkProgram("mv :: [\"a\":1, \"b\":2][\"a\"]", &.{});
}

test "index access - failures" {
    // Non-integer index for arrays
    try checkProgram("af1 :: [1,2,3][1.5]", &[_]diag.DiagnosticCode{.non_integer_index});

    // Indexing non-indexable types
    try checkProgram("af2 :: 5[0]", &[_]diag.DiagnosticCode{.not_indexable});

    // Map with wrong key type
    try checkProgram("mf1 :: [\"a\":1, \"b\":2][1]", &[_]diag.DiagnosticCode{.map_wrong_key_type});

    // Index with null
    try checkProgram("nf1 :: [1,2,3][null]", &[_]diag.DiagnosticCode{.non_integer_index});
}

// Field access: structs, tuples, pointers; invalid targets/fields

test "field access - success" {
    // Struct field
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ vx :: Point{ x: 1, y: 2 }.x
    , &.{});

    // Nested struct field
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ Outer :: struct { p: Point, z: i32 }
        \\ v :: Outer{ p: Point{ x: 1, y: 2 }, z: 3 }.p.x
    , &.{});

    // Tuple numeric field access
    try checkProgram("tf :: (10, 20).1", &.{});

    // Pointer-to-struct deref then field
    try checkProgram(
        \\
        \\ P :: struct { a: i32 }
        \\ pp: *P = &P{ a: 5 }
        \\ va :: pp.a
    , &.{});
}

// Functions vs Procedures: purity semantics for fn, side-effects in proc

test "functions and procedures - success" {
    // Pure function pointer assigned a pure proc
    try checkProgram(
        \\
        \\ dbl: proc(i64) i64 = proc(x: i64) i64 { return x * 2 }
        \\ r :: dbl(10)
    , &.{});

    // Procedure with side effects (extern printf), allowed for proc
    try checkProgram(
        \\
        \\ printf :: extern proc(string, any) i32
        \\ proc_print :: proc() i32 { _ = printf("ok"); return 0 }
        \\ rv :: proc_print()
    , &.{});
}

test "functions and procedures - failures" {
    try checkProgram(
        \\
        \\ printf :: extern proc(*void, any) i32
        \\ impure :: proc() i32 { _ = printf("hi".ptr); return 0 }
        \\ f: fn() i32 : impure
    , &[_]diag.DiagnosticCode{.argument_type_mismatch});
}

test "functions - purity failures" {
    // Calling a proc from a fn
    try checkProgram(
        \\
        \\ printf :: extern proc(*void, any) i32
        \\ f : fn() i32 :  proc() i32 { _ = printf("hi".ptr); return 0 }
    , &[_]diag.DiagnosticCode{.argument_type_mismatch});

    // Global mutation inside fn
    try checkProgram(
        \\
        \\ G: i32 = 0
        \\ f :: fn() i32 { G = 1; return G }
    , &[_]diag.DiagnosticCode{.purity_violation});

    // Local mutation inside fn (assignment)
    try checkProgram(
        \\
        \\ f :: fn() i32 { x: i32 = 0; x = 1; return x }
    , &[_]diag.DiagnosticCode{});

    // Pointer mutation inside fn
    try checkProgram(
        \\
        \\ f :: fn(p: *i32) i32 { p.* = 3; return p.* }
    , &[_]diag.DiagnosticCode{.purity_violation});

    // Local pointer mutation inside fn
    try checkProgram(
        \\
        \\ f :: fn() i32 {
        \\     v : i32 = 0
        \\     p : *i32 = &v
        \\     p.* = 3
        \\     return p.*
        \\ }
    , &[_]diag.DiagnosticCode{});

    // Array element mutation inside fn
    try checkProgram(
        \\
        \\ f :: fn() i32 {
        \\  a: [3]i32 = [1,2,3]
        \\  a[0] = 9
        \\  return a[0]
        \\ }
    , &[_]diag.DiagnosticCode{});

    // Map element update inside fn
    try checkProgram(
        \\
        \\ f :: fn() i32 { m: [string:i32] = ["a":1]; m["a"] = 2; return m["a"] }
    , &[_]diag.DiagnosticCode{});

    // Param Array element mutation fn (not alloed)
    try checkProgram(
        \\
        \\ f :: fn(a: [3]i32) i32 { a[0] = 9; return a[0] }
    , &[_]diag.DiagnosticCode{.purity_violation});

    // Param Map element mutation fn (not alloed)
    try checkProgram(
        \\ f :: fn(m: [string:i32]) i32 { m["a"] = 2; return m["a"] }
    , &[_]diag.DiagnosticCode{.purity_violation});

    // Extern proc call inside fn
    try checkProgram(
        \\ printf :: extern proc(*void, any) i32
        \\ f :: fn() i32 { _ = printf("hi".^*void); return 0 }
    , &[_]diag.DiagnosticCode{.purity_violation, .invalid_bitcast});

    // proc call inside fn
    try checkProgram(
        \\
        \\ p :: proc() i32 { return 1 }
        \\ f :: fn() i32 { return p() }
    , &[_]diag.DiagnosticCode{.purity_violation});
}

test "field access - failures" {
    // Non-existent struct field
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ vz :: Point{ x: 1, y: 2 }.z
    , &[_]diag.DiagnosticCode{.unknown_struct_field});

    // Field access on non-struct/tuple
    try checkProgram("nf :: 5.x", &[_]diag.DiagnosticCode{.invalid_float_literal});

    // Tuple field: non-numeric name
    try checkProgram("tn :: (1,2).a", &[_]diag.DiagnosticCode{.expected_field_name_or_index});

    // Map value field access invalid
    try checkProgram("mf :: [\"a\":1,][\"a\"].x", &[_]diag.DiagnosticCode{.field_access_on_non_aggregate});

    // Enum tag has no fields
    try checkProgram(
        \\
        \\ E :: enum { A, B }
        \\ ef :: E.A.x
    , &[_]diag.DiagnosticCode{.field_access_on_non_aggregate});

    // Numeric field on struct
    try checkProgram(
        \\
        \\ P :: struct { a: i32 }
        \\ nv :: P{ a: 1 }.0
    , &[_]diag.DiagnosticCode{.unknown_struct_field});
}

test "control flow semantic errors" {
    // return value in void function
    try checkProgram(
        \\ main :: proc() {
        \\   return 1
        \\}
    , &[_]diag.DiagnosticCode{.return_value_in_void_function});
    // missing return value in non-void function
    try checkProgram(
        \\main :: proc() i32 {
        \\   return
        \\}
    , &[_]diag.DiagnosticCode{.missing_return_value});
    // defer/errdefer outside function
    try checkProgram("a :: defer 1", &[_]diag.DiagnosticCode{.defer_outside_function});
    try checkProgram("a :: errdefer 1", &[_]diag.DiagnosticCode{.errdefer_outside_function});
}

test "type expression semantic errors" {
    // Array size must be an integer literal
    try checkProgram("a :: [1.5]i32", &[_]diag.DiagnosticCode{.array_size_not_integer_literal});

    try checkProgram("a :: [1 + 2]i32", &[_]diag.DiagnosticCode{});
    // SIMD lanes must be integer literal
    try checkProgram("a :: simd(i32, 2.5)", &[_]diag.DiagnosticCode{.simd_lanes_not_integer_literal});
    // Tensor dims must be integer literals
    try checkProgram("a :: tensor(2.3, 3, i32)", &[_]diag.DiagnosticCode{.tensor_dimension_not_integer_literal});
}

test "duplicate fields in type definitions" {
    // Struct duplicate field
    try checkProgram("a :: struct { x: i32, x: i32 }", &[_]diag.DiagnosticCode{.duplicate_field});
    // Enum duplicate field
    try checkProgram("a :: enum { A, A }", &[_]diag.DiagnosticCode{.duplicate_enum_field});
    // Variant duplicate
    try checkProgram("a :: variant { A, A }", &[_]diag.DiagnosticCode{.duplicate_variant});
}

// Focused: Block expressions

test "block expressions - success" {
    // Empty block as an expression
    try checkProgram("b :: {}", &.{});

    // Block with simple declarations
    try checkProgram(
        \\
        \\ b :: {
        \\   x :: 1
        \\   y :: 2
        \\ }
    , &.{});

    // Nested empty blocks
    try checkProgram("x :: { { } }", &.{});

    // Block inside a function body with a valid return
    try checkProgram(
        \\
        \\ f :: proc() i32 {
        \\   { return 1 }
        \\ }
    , &.{});
}

test "block expressions - failures" {
    // Control flow statements in a top-level block are invalid contexts
    try checkProgram(
        \\
        \\ b :: { return 1 }
    , &[_]diag.DiagnosticCode{.return_outside_function});
    try checkProgram(
        \\
        \\ b :: { break }
    , &[_]diag.DiagnosticCode{.break_outside_loop});
    try checkProgram(
        \\
        \\ b :: { continue }
    , &[_]diag.DiagnosticCode{.continue_outside_loop});
    try checkProgram(
        \\
        \\ b :: { defer 1 }
    , &[_]diag.DiagnosticCode{.defer_outside_function});
    try checkProgram(
        \\
        \\ b :: { errdefer 1 }
    , &[_]diag.DiagnosticCode{.errdefer_outside_function});

    // Mismatched returns via nested blocks inside functions
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   { return 1 }
        \\ }
    , &[_]diag.DiagnosticCode{.return_value_in_void_function});
    try checkProgram(
        \\
        \\ main :: proc() i32 {
        \\   { return }
        \\ }
    , &[_]diag.DiagnosticCode{.missing_return_value});
}

// Focused: Return statements

test "return statements - success" {
    // Return with value in non-void procedure
    try checkProgram(
        \\
        \\ f :: proc() i32 { return 1 }
    , &.{});

    // Return without value in void procedure
    try checkProgram(
        \\
        \\ g :: proc() { return }
    , &.{});

    // Nested block return inside function
    try checkProgram(
        \\
        \\ h :: proc() i32 {
        \\   { return 2 }
        \\ }
    , &.{});

    // Conditional early returns in both branches
    try checkProgram(
        \\
        \\ k :: proc() i32 {
        \\   if true { return 1 } else { return 2 }
        \\ }
    , &.{});
}

test "return statements - failures" {

    // Return value in a void function
    try checkProgram(
        \\
        \\ m :: proc() { return 1 }
    , &[_]diag.DiagnosticCode{.return_value_in_void_function});

    // Missing return value in a non-void function
    try checkProgram(
        \\
        \\ n :: proc() i32 { return }
    , &[_]diag.DiagnosticCode{.missing_return_value});

    // Return type mismatch against declared result type
    try checkProgram(
        \\
        \\ r1 :: proc() i32 { return 1.0 }
    , &[_]diag.DiagnosticCode{.return_type_mismatch});
    try checkProgram(
        \\
        \\ r2 :: proc() i32 { return "s" }
    , &[_]diag.DiagnosticCode{.return_type_mismatch});
}

// Focused: If expressions

test "if expressions - success" {
    // As a statement in a function body
    try checkProgram(
        \\
        \\ f :: proc() {
        \\   if true { } else { }
        \\ }
    , &.{});

    // As a value with matching branch types
    try checkProgram("a :: if true { 1 } else { 2 }", &.{});

    // else-if chain
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   if false { } else if true { } else { }
        \\ }
    , &.{});

    // Complex boolean condition
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   if (true and !false) or (false and true) { }
        \\ }
    , &.{});
}

test "if expressions - failures" {
    // Non-boolean conditions
    try checkProgram("a :: if 1 { 2 } else { 3 }", &[_]diag.DiagnosticCode{.non_boolean_condition});
    try checkProgram("a :: if 1.0 { 2 } else { 3 }", &[_]diag.DiagnosticCode{.non_boolean_condition});
    try checkProgram("a :: if \"s\" { 2 } else { 3 }", &[_]diag.DiagnosticCode{.non_boolean_condition});
    try checkProgram("a :: if null { 2 } else { 3 }", &[_]diag.DiagnosticCode{.non_boolean_condition});

    // If used as value without else
    try checkProgram("a :: if true { 1 }", &[_]diag.DiagnosticCode{.if_expression_requires_else});

    // Mismatched branch types
    try checkProgram("a :: if true { 1 } else { false }", &[_]diag.DiagnosticCode{.if_branch_type_mismatch});
    try checkProgram(
        \\ b: ?i32 = null
        \\ c := if b != null {
        \\    b
        \\ } else {
        \\    null
        \\ }
    , &[_]diag.DiagnosticCode{.if_branch_type_mismatch});

    // Return mismatches within branches
    try checkProgram(
        \\
        \\ main :: proc() i32 {
        \\   if true { return } else { return 1 }
        \\ }
    , &[_]diag.DiagnosticCode{.missing_return_value});
    try checkProgram(
        \\
        \\ main :: proc() i32 {
        \\   if true { return 1.0 } else { return 1 }
        \\ }
    , &[_]diag.DiagnosticCode{.return_type_mismatch});

    // Return with value inside void function branch
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   if true { return 1 } else { }
        \\ }
    , &[_]diag.DiagnosticCode{.return_value_in_void_function});
}

// Focused: While loops

test "while loops - success" {
    // Simple while with boolean condition inside function
    try checkProgram(
        \\
        \\ f :: proc() {
        \\   while true { }
        \\ }
    , &.{});

    // While with complex boolean expression
    try checkProgram(
        \\
        \\ g :: proc() {
        \\   while (true and !false) or false { break }
        \\ }
    , &.{});

    // Nested while with break and continue
    try checkProgram(
        \\
        \\ h :: proc() {
        \\   while true {
        \\     continue
        \\     while false { break }
        \\   }
        \\ }
    , &.{});

    // Infinite loop form (no condition) if supported by grammar
    try checkProgram(
        \\
        \\ i :: proc() {
        \\   while { break }
        \\ }
    , &.{});
}

test "while loops - failures" {
    // Non-boolean conditions
    try checkProgram(
        \\
        \\ f :: proc() {
        \\   while 1 { }
        \\ }
    , &[_]diag.DiagnosticCode{.non_boolean_condition});
    try checkProgram(
        \\
        \\ g :: proc() {
        \\   while 1.0 { }
        \\ }
    , &[_]diag.DiagnosticCode{.non_boolean_condition});
    try checkProgram(
        \\
        \\ h :: proc() {
        \\   while "s" { }
        \\ }
    , &[_]diag.DiagnosticCode{.non_boolean_condition});
    try checkProgram(
        \\
        \\ k :: proc() {
        \\   while null { }
        \\ }
    , &[_]diag.DiagnosticCode{.non_boolean_condition});

    // Return with value inside void function loop
    try checkProgram(
        \\
        \\ m :: proc() {
        \\   while true { return 1 }
        \\ }
    , &[_]diag.DiagnosticCode{.return_value_in_void_function});
}

// Focused: While-`is` loops

test "while is - success" {
    // Binding pattern
    try checkProgram(
        \\
        \\ f :: proc() {
        \\   while is x := 1 { break }
        \\ }
    , &.{});

    // Tuple pattern
    try checkProgram(
        \\
        \\ g :: proc() {
        \\   while is (a, b) := (1, 2) { break }
        \\ }
    , &.{});
}

test "while is - failures" {
    // Pattern/subject mismatch
    try checkProgram(
        \\
        \\ f :: proc() {
        \\   while is (a, b) := 1 { }
        \\ }
    , &[_]diag.DiagnosticCode{.pattern_shape_mismatch});
}

// Focused: Labeled while loops

test "labeled while - success" {
    // break to outer labeled loop
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   outer: while true {
        \\     break :outer
        \\   }
        \\ }
    , &.{});

    // continue inside labeled loop
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   loop1: while true {
        \\     continue
        \\   }
        \\ }
    , &.{});

    // Labeled while-is
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   L: while is (a,b) := (1,2) {
        \\     break :L
        \\   }
        \\ }
    , &.{});
}

// Focused: For loops (normal and labeled), with patterns and ranges

test "for loops - success" {
    // Iterate over array with binding
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   for x in [1,2,3] { }
        \\ }
    , &.{});

    // Iterate over array with wildcard
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   for _ in [1,2,3] { }
        \\ }
    , &.{});

    // Destructure tuple elements from array of tuples
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   for (a,b) in [(1,2), (3,4)] { }
        \\ }
    , &.{});

    // Range iteration (exclusive)
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   for i in 0..5 { }
        \\ }
    , &.{});

    // Range iteration (inclusive)
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   for i in 0..=5 { }
        \\ }
    , &.{});

    // Open-ended prefix range to value (..N)
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   for i in ..5 { break }
        \\ }
    , &.{});

    // Labeled for with break to label
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   Outer: for i in [1,2,3] { break :Outer }
        \\ }
    , &.{});
}

test "for loops - failures" {
    // Non-iterable in 'in'
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   for x in 1 { }
        \\ }
    , &[_]diag.DiagnosticCode{.non_iterable_in_for});

    // Pattern/element mismatch (tuple pattern over scalar array)
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   for (a,b) in [1,2,3] { }
        \\ }
    , &[_]diag.DiagnosticCode{.pattern_shape_mismatch});
}

// Focused: Patterns (declarations, match, for)

test "patterns - declarations - success" {
    // Tuple destructuring
    try checkProgram("(x, y) :: (1, 2)", &.{});

    // Nested tuple destructuring
    try checkProgram("(a, (b, c)) :: (1, (2, 3))", &.{});

    // Struct destructuring
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ Point{ x: x, y: y } :: Point{ x: 1, y: 2 }
    , &.{});

    // Slice with rest binding
    try checkProgram("[x, y, ..rest] :: [1, 2, 3, 4]", &.{});
}

test "patterns - declarations - failures" {
    // Tuple arity mismatch
    try checkProgram("(x, y) :: (1, 2, 3)", &[_]diag.DiagnosticCode{.tuple_arity_mismatch});

    // Struct field mismatch
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ Point{ x: a, z: b } :: Point{ x: 1, y: 2 }
    , &[_]diag.DiagnosticCode{.struct_pattern_field_mismatch});
}

test "patterns - for loops - success" {
    // Destructure tuple elements from an array of tuples
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   for (x, y) in [(1,2), (3,4)] { }
        \\ }
    , &.{});

    // Binding with slice rest in loop over array
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   for [a, ..rest] in [1,2,3] { }
        \\ }
    , &.{});
}

test "patterns - for loops - failures" {
    // Pattern shape mismatch
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   for (a, b) in [1,2,3] { }
        \\ }
    , &[_]diag.DiagnosticCode{.pattern_shape_mismatch});
}

// Focused: Match expressions

test "match expressions - success" {
    // Empty arms
    try checkProgram(
        \\
        \\ x :: 1
        \\ r :: match x { }
    , &.{});

    // Literal arms with wildcard default
    try checkProgram(
        \\
        \\ x :: 2
        \\ r :: match x { 1 => { }, 2 => { }, _ => { }, }
    , &.{});

    // With guards
    try checkProgram(
        \\
        \\ x :: 3
        \\ r :: match x { y @ 3 if y == 3 => { }, _ => { }, }
    , &.{});

    // Or-pattern
    try checkProgram(
        \\
        \\ x :: 1
        \\ r :: match x { 0 | 1 => { }, _ => { }, }
    , &.{});

    // Tuple and struct patterns
    try checkProgram(
        \\
        \\ T :: (1, 2)
        \\ r :: match T { (a, b) => { }, }
    , &.{});
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ p :: Point{ x: 1, y: 2 }
        \\ r :: match p { Point{ x: a, y: b } => { }, }
    , &.{});

    // Variant patterns with payloads
    try checkProgram(
        \\
        \\ V :: variant { A, B(i32), C{ x: i32 } }
        \\ v :: V.C{ x: 1 }
        \\ r :: match v { V.A => { }, V.B(n) => { }, V.C{ x: a } => { }, }
    , &.{});

    // Range patterns (exclusive/inclusive)
    try checkProgram(
        \\
        \\ x :: 5
        \\ r :: match x { 0..5 => { }, 6..=10 => { }, _ => { }, }
    , &.{});
}

test "match expressions - failures" {
    // Tuple pattern on scalar
    try checkProgram(
        \\
        \\ x :: 1
        \\ r :: match x { (a, b) => { }, }
    , &[_]diag.DiagnosticCode{.pattern_shape_mismatch});

    // Tuple arity mismatch vs subject tuple
    try checkProgram(
        \\
        \\ T :: (1, 2)
        \\ r :: match T { (a, b, c) => { }, }
    , &[_]diag.DiagnosticCode{.tuple_arity_mismatch});

    // Struct field mismatch
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ p :: Point{ x: 1, y: 2 }
        \\ r :: match p { Point{ x: a, z: b } => { }, }
    , &[_]diag.DiagnosticCode{.struct_pattern_field_mismatch});

    // Variant payload mismatch
    try checkProgram(
        \\
        \\ V :: variant { A, B(i32) }
        \\ v :: V.B(1)
        \\ r :: match v { V.B(a, b) => { }, }
    , &[_]diag.DiagnosticCode{.tuple_arity_mismatch});
}

// Focused: Match exhaustiveness and overlap (Rust-like semantics)

test "match exhaustiveness - success" {
    // Bool exhaustive without wildcard
    try checkProgram(
        \\
        \\ b :: true
        \\ r :: match b { true => { }, false => { }, }
    , &.{});

    // Enum exhaustive: all variants handled
    try checkProgram(
        \\
        \\ E :: enum { A, B, C }
        \\ e :: E.A
        \\ r :: match e { E.A => { }, E.B => { }, E.C => { }, }
    , &.{});

    // Wildcard makes it exhaustive
    try checkProgram(
        \\
        \\ x :: 10
        \\ r :: match x { 0..5 => { }, _ => { }, }
    , &.{});
}

test "match exhaustiveness - failures" {
    // Bool non-exhaustive
    try checkProgram(
        \\
        \\ b :: true
        \\ r :: match b { true => { },}
    , &[_]diag.DiagnosticCode{.non_exhaustive_match});

    // Enum missing one variant
    try checkProgram(
        \\
        \\ E :: enum { A, B }
        \\ e :: E.A
        \\ r :: match e { E.A => { }, }
    , &[_]diag.DiagnosticCode{.non_exhaustive_match});

    // Guarded wildcard alone is not exhaustive
    try checkProgram(
        \\
        \\ x :: 1
        \\ r :: match x { _ if true => { }, }
    , &[_]diag.DiagnosticCode{.non_exhaustive_match});
}

test "match overlap/unreachable - failures" {
    // Duplicate literal arm
    try checkProgram(
        \\
        \\ x :: 1
        \\ r :: match x { 1 => { }, 1 => { }, }
    , &[_]diag.DiagnosticCode{.overlapping_match_arm});

    // Overlapping ranges
    try checkProgram(
        \\
        \\ x :: 3
        \\ r :: match x { 0..5 => { }, 3..10 => { }, }
    , &[_]diag.DiagnosticCode{.overlapping_match_arm});

    // Unreachable after wildcard
    try checkProgram(
        \\
        \\ x :: 2
        \\ r :: match x { _ => { }, 2 => { }, }
    , &[_]diag.DiagnosticCode{.unreachable_match_arm});
}

// Focused: defer and errdefer

test "defer - success" {
    // Basic defer inside void proc
    try checkProgram(
        \\
        \\ cleanup :: proc() { }
        \\ main :: proc() { defer cleanup() }
    , &.{});

    // Multiple defers and nested block
    try checkProgram(
        \\
        \\ a :: proc() { }
        \\ b :: proc() { }
        \\ f :: proc() {
        \\   defer a()
        \\   { defer b() }
        \\ }
    , &.{});

    // Defer inside loop
    try checkProgram(
        \\
        \\ c :: proc() { }
        \\ g :: proc() {
        \\   while true { defer c(); break }
        \\ }
    , &.{});
}

test "errdefer - success" {
    // errdefer inside a function returning error union
    try checkProgram(
        \\
        \\ MyErr :: error { A }
        \\ cleanup :: proc() { }
        \\ f :: proc() MyErr!i32 {
        \\   errdefer cleanup()
        \\   return 1
        \\ }
    , &.{});

    // errdefer combined with early error return
    try checkProgram(
        \\
        \\ MyErr :: error { A }
        \\ tidy :: proc() { }
        \\ g :: proc() MyErr!i32 {
        \\   errdefer tidy()
        \\   return MyErr.A
        \\ }
    , &.{});
}

test "defer/errdefer - failures" {
    // errdefer in a void-returning function
    try checkProgram(
        \\bad :: proc() {
        \\errdefer 1
        \\}
    ,
        &[_]diag.DiagnosticCode{.errdefer_in_non_error_function},
    );

    // errdefer in a non-error function with return type
    try checkProgram(
        \\bad2 :: proc() i32 {
        \\ errdefer 1
        \\ return 0
        \\}
    ,
        &[_]diag.DiagnosticCode{.errdefer_in_non_error_function},
    );
}

// Focused: Break with values and labeled forms

test "break with values - success" {
    // Use break with value to yield from a labeled while-expression
    try checkProgram(
        \\x :: L: while true {
        \\ break :L 42
        \\}
    , &.{});

    // Nested loops: break outer without value
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   outer: while true {
        \\     while true { break :outer }
        \\   }
        \\ }
    , &.{});
}

test "break with values - failures" {
    // Using mismatched types in distinct break values for the same loop result
    try checkProgram(
        \\
        \\ y :: (L: while true { if true { break :L 1 } else { break :L 2.0 } })
    , &[_]diag.DiagnosticCode{.loop_break_value_type_conflict});

    // Assigning loop result to typed var with incompatible break value type
    try checkProgram(
        \\
        \\ z: i32 = (L: while true { break :L 2.5 })
    , &[_]diag.DiagnosticCode{.expected_integer_type});
}

// Focused: Continue

test "continue - success" {
    // Plain continue inside a loop
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   while true { continue; break }
        \\ }
    , &.{});
}

// Focused: Labeled break with values inside for-loops

test "labeled break values in for - success" {
    // Loop expression yields via labeled break
    try checkProgram("x :: (L: for i in [1,2] { break :L 7 })", &.{});

    // Assign to typed var
    try checkProgram("y: i32 = (L: for i in [1,2] { break :L 3 })", &.{});
}

test "labeled break values in for - failures" {
    // Inconsistent break value types across branches
    try checkProgram(
        \\ z :: (L: for i in [1,2] { if i == 1 { break :L 1 } else { break :L 2.0 } })
    , &[_]diag.DiagnosticCode{.loop_break_value_type_conflict});

    // Assigning result to incompatible typed var
    try checkProgram(
        \\
        \\ w: i32 = (L: for i in [1,2] { break :L 2.5 })
    , &[_]diag.DiagnosticCode{.expected_integer_type});
}

// Focused: Break values in branches

test "break values in branches - success" {
    // While branch breaks with consistent type
    try checkProgram("v :: (L: while true { if true { break :L 1 } else { break :L 2 } })", &.{});

    // For branch breaks with consistent type
    try checkProgram("u :: (L: for i in [1] { if true { break :L 4 } else { break :L 5 } })", &.{});
}

test "break values in branches - failures" {
    // While branch inconsistent types
    try checkProgram(
        \\q :: L: while true {
        \\  if true {
        \\    break :L 1
        \\  } else {
        \\    break :L 2.0
        \\  }
        \\}
    , &[_]diag.DiagnosticCode{.loop_break_value_type_conflict});

    // For branch inconsistent types
    try checkProgram(
        \\r :: (L: for i in [1] { if true { break :L 1.0 } else { break :L 2 } })
    , &[_]diag.DiagnosticCode{.loop_break_value_type_conflict});
}

// Focused: Unreachable after unconditional break

test "unreachable after break - failures" {
    // Expression after break inside loop expression
    try checkProgram(
        \\bad :: L: while true {
        \\  break :L 1
        \\  2
        \\}
    , &[_]diag.DiagnosticCode{.unreachable_code_after_break});

    // Return after unconditional break in function
    try checkProgram(
        \\
        \\ main :: proc() i32 {
        \\   L: while true { break :L 1; return 2 }
        \\ }
    , &[_]diag.DiagnosticCode{.unreachable_code_after_break});
}

// // Focused: Async/Await
//
// test "async/await - success" {
//     // Async procedure (void)
//     try checkProgram(
//         \\
//         \\ ap :: async proc() { }
//     , &.{});
//
//     // Async procedure returning i32
//     try checkProgram(
//         \\
//         \\ af :: async proc() i32 { return 1 }
//     , &.{});
//
//     // Async block as a statement in a proc
//     try checkProgram(
//         \\
//         \\ f :: proc() { async { } }
//     , &.{});
//
//     // Await an async block value
//     try checkProgram("x :: (async { 1 }) await", &.{});
//
//     // Await in condition
//     try checkProgram(
//         \\
//         \\ main :: proc() {
//         \\   if (async { true }) await { }
//         \\ }
//     , &.{});
// }
//
// test "async/await - failures" {
//     // Await a non-async value
//     try checkProgram("x :: 1 await", &[_]diag.DiagnosticCode{.await_non_async});
//
//     // Await result type mismatch
//     try checkProgram("y: i32 = (async { }) await", &[_]diag.DiagnosticCode{.await_type_mismatch});
//
//     // Await at top-level without async context (policy: disallow)
//     try checkProgram("z :: (1) await", &[_]diag.DiagnosticCode{.await_outside_async_context});
// }
//
// // Focused: Closures / Lambdas
//
// test "closures - success" {
//     // Zero-arg expression-bodied closure
//     try checkProgram("c0 :: || 1", &.{});
//
//     // Single-arg typed closure, expression body
//     try checkProgram("c1 :: |a: i32| a", &.{});
//
//     // Two-arg typed closure with arithmetic
//     try checkProgram("c2 :: |a: i32, b: i32| a + b", &.{});
//
//     // Result type annotation with block body
//     try checkProgram(
//         \\
//         \\ c3 :: |a: i32| i32 { return a }
//     , &.{});
//
//     // Default parameter value
//     try checkProgram("c4 :: |a: i32 = 5| a", &.{});
// }
//
// test "closures - failures" {
//     // Return value in a void-closure (no result type)
//     try checkProgram(
//         \\
//         \\ bad1 :: || { return 1 }
//     , &[_]diag.DiagnosticCode{.return_value_in_void_function});
//
//     // Return type mismatch vs annotated result type
//     try checkProgram(
//         \\
//         \\ bad2 :: |a: i32| i32 { return 1.0 }
//     , &[_]diag.DiagnosticCode{.return_type_mismatch});
// }

test "closures - escape failures" {
    // Returning a captured closure
    try checkProgram(
        \\
        \\ make :: proc(base: i32) fn(i32) i32 {
        \\   return |x: i32| x + base
        \\ }
    , &[_]diag.DiagnosticCode{.closure_escape_not_supported});

    // Passing a captured closure as an argument
    try checkProgram(
        \\
        \\ apply :: fn(f: fn(i32) i32, x: i32) i32 { return f(x) }
        \\ caller :: proc(base: i32) i32 {
        \\   return apply(|x: i32| x + base, 1)
        \\ }
    , &[_]diag.DiagnosticCode{.closure_escape_not_supported});
}

// Focused: Cast expressions

test "cast expressions - success" {
    // Normal cast via .(Type)
    try checkProgram("a :: 1.(f64)", &.{});
    try checkProgram("b :: 2.0.(i32)", &.{});

    // Bitcast with '^' (same-size types assumed)
    try checkProgram("c :: 1.^u64", &.{});

    // Saturating cast with '|'
    try checkProgram("d :: 300.|u8", &.{});

    // Wrapping cast with '%'
    try checkProgram("e :: -1.% u32", &.{});

    // Checked cast with '?'
    try checkProgram("f :: 1.? i32", &.{});
}

test "cast expressions - failures" {
    // Cast to non-type expression
    try checkProgram("x :: 1.(1 + 2)", &[_]diag.DiagnosticCode{.cast_target_not_type});

    // Bitcast between incompatible sizes/kinds
    try checkProgram("y :: 1.^f32", &[_]diag.DiagnosticCode{.invalid_bitcast});

    // Checked cast that cannot succeed
    try checkProgram("z :: \"s\".?i32", &[_]diag.DiagnosticCode{.invalid_checked_cast});
}

// Focused: Patterns — slice rest with Rust-like middle rest

test "patterns - slice rest - success" {
    // Middle rest on fixed array
    try checkProgram("[a, ..rest, b] :: [1, 2, 3]", &.{});

    // Rest at end on fixed array
    try checkProgram("[a, ..rest] :: [1, 2, 3]", &.{});

    // Rest at start on slice/dynarray
    try checkProgram(
        \\
        \\ arr: []i32 = ([1, 2, 3])[0..3]
        \\ [..rest, a] :: arr
    , &.{});
}

test "patterns - slice rest - failures" {
    // Too many explicit elements with rest for fixed array (as per our rule)
    try checkProgram("[a, ..rest, b, c] :: [1, 2, 3]", &[_]diag.DiagnosticCode{});
}

// Focused: Patterns — comprehensive coverage (declarations, assignments, params, match)

test "patterns - declarations - additional success" {
    // Tuple: flat and nested
    try checkProgram("(a, b) :: (1, 2)", &.{});
    try checkProgram("(a, (b, c)) :: (1, (2, 3))", &.{});

    // Struct: flat, nested
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ Point{ x: px, y: py } :: Point{ x: 1, y: 2 }
    , &.{});

    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ Rect  :: struct { tl: Point, br: Point }
        \\ Rect{ tl: Point{ x: ax, y: ay }, br: Point{ x: bx, y: by } } ::
        \\   Rect{ tl: Point{ x: 1, y: 2 }, br: Point{ x: 3, y: 4 } }
    , &.{});

    // Slice/array: exact arity and rest-at-end
    try checkProgram("[x, y] :: [1, 2]", &.{});
    try checkProgram("[x, ..rest] :: [1, 2, 3]", &.{});
    try checkProgram("[..rest] :: [1, 2]", &.{});

    // Ignore bindings
    try checkProgram("(_, _) :: (1, 2)", &.{});
}

test "patterns - declarations - additional failures" {
    // Tuple arity mismatch (too many)
    try checkProgram("(x, y) :: (1, 2, 3)", &[_]diag.DiagnosticCode{.tuple_arity_mismatch});

    // Tuple arity mismatch (too few)
    try checkProgram("(x, y, z) :: (1, 2)", &[_]diag.DiagnosticCode{.tuple_arity_mismatch});

    // Struct field mismatch (unknown field in pattern)
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ Point{ x: a, z: b } :: Point{ x: 1, y: 2 }
    , &[_]diag.DiagnosticCode{.struct_pattern_field_mismatch});

    // Slice rest not at end
    try checkProgram("[a, ..rest, b] :: [1, 2, 3]", &[_]diag.DiagnosticCode{});

    // Multiple rests in slice pattern
    try checkProgram("[..r1, ..r2] :: [1, 2]", &[_]diag.DiagnosticCode{.pattern_shape_mismatch});

    // Fixed array arity mismatch without rest
    try checkProgram("[a, b, c] :: [1, 2]", &[_]diag.DiagnosticCode{.pattern_shape_mismatch});
}

test "patterns - assignments - success" {
    // Tuple assignment into existing bindings
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   x := 0; y := 0;
        \\   (x, y) = (1, 2)
        \\ }
    , &.{});

    // Struct assignment into existing bindings
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ main :: proc() {
        \\   x := 0; y := 0;
        \\   Point{ x: x, y: y } = Point{ x: 1, y: 2 }
        \\ }
    , &.{});

    // Slice assignment with rest into existing bindings
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   a := 0
        \\   rest : []i32 = ([0])[0..1]
        \\   [a, ..rest] = [1, 2, 3]
        \\ }
    , &.{});
}

test "patterns - assignments - failures" {
    // Pattern/value shape mismatch
    try checkProgram(
        \\
        \\ main :: proc() {
        \\   x := 0; y := 0;
        \\   (x, y) = 1
        \\ }
    , &[_]diag.DiagnosticCode{.pattern_shape_mismatch});
}

test "patterns - function params - success" {
    // Tuple param pattern with explicit tuple type
    try checkProgram(
        \\
        \\ sum :: proc((a, b): (i32, i32)) i32 { return a + b }
    , &.{});

    // Nested tuple param pattern
    try checkProgram(
        \\
        \\ f :: proc((a, (b, c)): (i32, (i32, i32))) i32 { return a + b + c }
    , &.{});

    // Struct param pattern with explicit type
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ getx :: proc(Point{ x: x, y: _ }: Point) i32 { return x }
    , &.{});
}

test "patterns - function params - failures" {
    // Shape mismatch between param pattern type and use-site destructure
    try checkProgram(
        \\
        \\ f :: proc((a, b): (i32, i32, i32)) i32 { return a + b }
    , &[_]diag.DiagnosticCode{.tuple_arity_mismatch});
}

test "patterns - match - success" {
    // Literals, wildcard, binding
    try checkProgram(
        \\
        \\ x :: 2
        \\ r :: match x { 1 => { }, _ => { }, }
    , &.{});

    // Tuple pattern
    try checkProgram(
        \\
        \\ t :: (1, 2)
        \\ r :: match t { (a, b) => { }, }
    , &.{});

    // Struct pattern
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ p :: Point{ x: 1, y: 2 }
        \\ r :: match p { Point{ x: a, y: b } => { }, }
    , &.{});

    // Enum tags
    try checkProgram(
        \\
        \\ State :: enum { Running, Walking }
        \\ s :: State.Running
        \\ r :: match s { State.Running => { }, State.Walking => { }, }
    , &.{});

    // Variants: tag-only, tuple payload, struct payload
    try checkProgram(
        \\
        \\ V :: variant { A, B(i32), C{ x: i32, y: i32 } }
        \\ v1 :: V.A
        \\ v2 :: V.B(1)
        \\ v3 :: V.C{ x: 1, y: 2 }
        \\ _  :: match v1 { V.A => { }, _ => { }, }
        \\ _  :: match v2 { V.B(n) => { }, _ => { }, }
        \\ _  :: match v3 { V.C{ x: a, y: b } => { }, _ => { }, }
    , &.{});

    // Or-pattern and at-pattern
    try checkProgram(
        \\
        \\ x :: 1
        \\ r :: match x { 0 | 1 => { }, _ => { }, }
    , &.{});

    try checkProgram(
        \\
        \\ x :: 5
        \\ r :: match x { y @ 5 => { }, }
    , &.{});

    // Slice with rest pattern in match
    try checkProgram(
        \\
        \\ xs :: [1, 2, 3]
        \\ r :: match xs { [a, ..rest] => { }, }
    , &.{});
}

test "patterns - match - failures" {
    // Tuple pattern vs non-tuple subject
    try checkProgram(
        \\
        \\ x :: 1
        \\ r :: match x { (a, b) => { }, }
    , &[_]diag.DiagnosticCode{.pattern_shape_mismatch});

    // Struct field mismatch in pattern
    try checkProgram(
        \\
        \\ Point :: struct { x: i32, y: i32 }
        \\ p :: Point{ x: 1, y: 2 }
        \\ r :: match p { Point{ x: a, z: b } => { }, }
    , &[_]diag.DiagnosticCode{.struct_pattern_field_mismatch});

    // Variant payload arity/type mismatch in pattern
    try checkProgram(
        \\
        \\ V :: variant { A, B(i32) }
        \\ v :: V.B(1)
        \\ r :: match v { V.B(a, b) => { }, }
    , &[_]diag.DiagnosticCode{.tuple_arity_mismatch});

    // Enum does not support payload-style pattern
    try checkProgram(
        \\
        \\ State :: enum { Running, Walking }
        \\ s :: State.Running
        \\ r :: match s { State.Running(x) => { }, }
    , &[_]diag.DiagnosticCode{.pattern_type_mismatch});
}

test "methods - call success" {
    try checkProgram(
        \\
        \\ Point :: struct { x: i32 }
        \\ Point.make :: fn(x: i32) Point { return Point{ x: x } }
        \\ Point.value :: fn(self: Point) i32 { return self.x }
        \\ Point.bump :: proc(self: *Point, dx: i32) void { self.x = self.x + dx }
        \\ Point.peek :: fn(self: *const Point) i32 { return self.x }
        \\ main :: proc() i32 {
        \\   p := Point.make(5)
        \\   p.bump(3)
        \\   return p.peek() + p.value()
        \\ }
    , &.{});
}

test "methods - static method allowed" {
    try checkProgram(
        \\
        \\ Point :: struct { x: i32 }
        \\ Point.zero :: fn() Point { return Point{ x: 0 } }
        \\ main :: proc() Point { return Point.zero() }
    , &.{});
}

test "methods - duplicate declaration" {
    try checkProgram(
        \\
        \\ Point :: struct { x: i32 }
        \\ Point.distance :: fn(self: Point) i32 { return self.x }
        \\ Point.distance :: fn(self: Point) i32 { return self.x }
    , &[_]diag.DiagnosticCode{.duplicate_method_on_type});
}

test "methods - enum owner" {
    try checkProgram(
        \\
        \\ Color :: enum { Red, Blue }
        \\ Color.describe :: fn(self: Color) i32 { return 1 }
        \\ main :: proc() i32 {
        \\   return Color.Red.describe()
        \\ }
    , &.{});
}

test "methods - owner must be struct" {
    try checkProgram(
        \\
        \\ Foo :: 42
        \\ Foo.bar :: fn(self: Foo) void {}
    , &[_]diag.DiagnosticCode{.method_owner_not_struct});
}

test "methods - self type mismatch" {
    try checkProgram(
        \\
        \\ Point :: struct { x: i32 }
        \\ Point.bad :: fn(self: i32) void {}
    , &[_]diag.DiagnosticCode{.method_self_type_mismatch});
}

// Focused: Import statements
//
// test "import statements - success" {
//     // String literal path
//     try checkProgram("m :: import \"examples/hello\"", &.{});
//
//     // Import with field access
//     try checkProgram("add :: (import \"examples/hello\").add", &.{});
// }

// Focused: typeof expressions

test "typeof - success" {
    try checkProgram("t1 :: typeof(1)", &.{});
    try checkProgram("t2 :: typeof(true and false)", &.{});
    try checkProgram("t3 :: typeof((1 + 2) * 3)", &.{});
}

// Focused: asm blocks attached to functions

// test "asm blocks - success" {
//     // Void proc with asm body
//     try checkProgram(
//         \\
//         \\ foo :: proc() asm { mov rax, rax }
//     , &.{});
//
//     // Proc with typed signature and asm body
//     try checkProgram(
//         \\
//         \\ add :: proc(a: i32, b: i32) i32 asm { ; pretend add }
//     , &.{});
// }
//
// Focused: MLIR meta blocks (module/op/attribute/type)

test "mlir splices - success" {
    try checkProgram(
        \\
        \\ ValueTy :: mlir type { i32 }
        \\ ConstAttr :: mlir attribute { 42 : i32 }
        \\ make_const :: proc() void {
        \\    mlir op : ValueTy {
        \\     "arith.constant"() {value = @ConstAttr} : () -> @ValueTy
        \\   }
        \\ }
        \\ TensorTy :: mlir type { tensor<4x4x`ValueTy`> }
        \\ use_tensor :: proc() void {
        \\   comptime {
        \\     _ = TensorTy
        \\   }
        \\ }
    , &.{});
}

test "mlir splices - unknown identifier" {
    try checkProgram(
        \\
        \\ BadType :: mlir type { tensor<`Missing`> }
    , &.{.mlir_splice_unknown_identifier});
}

test "mlir splices - non-comptime" {
    try checkProgram(
        \\
        \\ main :: proc(x: i32) void {
        \\   _ = mlir type { tensor<`x`> }
        \\ }
    , &.{.mlir_splice_not_comptime});
}

// Focused: code expressions

test "code expressions - success with note" {
    // Code block emits a diagnostic note that it is not executed
    try checkProgram("c :: code { 1 }", &[_]diag.DiagnosticCode{.checker_code_block_not_executed});

    // Inside function, still emits the same note
    try checkProgram(
        \\
        \\ main :: proc() { code { 1 } }
    , &[_]diag.DiagnosticCode{.checker_code_block_not_executed});
}

test "code insert - success" {
    try checkProgram(
        \\
        \\ build_add :: proc() Code {
        \\   return code { add :: fn(a: i32, b: i32) i32 { return a + b } }
        \\ }
        \\ comptime { insert build_add() }
        \\ main :: proc() i32 { return add(1, 2) }
    , &[_]diag.DiagnosticCode{.checker_code_block_not_executed});
}

test "code insert - scoped into function block" {
    try checkProgram(
        \\
        \\ build_local :: proc() Code {
        \\   return code { local :: 41 }
        \\ }
        \\ main :: proc() i32 {
        \\   comptime { insert build_local() }
        \\   return local
        \\ }
    , &[_]diag.DiagnosticCode{.checker_code_block_not_executed});
}

test "code insert - nested block shadowing" {
    try checkProgram(
        \\
        \\ build_local :: proc() Code {
        \\   return code { local :: 41 }
        \\ }
        \\ build_shadow :: proc() Code {
        \\   return code { local :: 99 }
        \\ }
        \\ main :: proc() i32 {
        \\   comptime { insert build_local() }
        \\   {
        \\     comptime { insert build_shadow() }
        \\     _ = local
        \\   }
        \\   return local
        \\ }
    , &[_]diag.DiagnosticCode{.checker_code_block_not_executed});
}

test "code insert - block scope does not leak" {
    try checkProgram(
        \\
        \\ build_local :: proc() Code {
        \\   return code { inner :: 1 }
        \\ }
        \\ main :: proc() i32 {
        \\   {
        \\     comptime { insert build_local() }
        \\     _ = inner
        \\   }
        \\   return inner
        \\ }
    , &[_]diag.DiagnosticCode{ .checker_code_block_not_executed, .undefined_identifier });
}

test "code insert - requires Code value" {
    try checkProgram(
        \\
        \\ comptime { insert 1 }
    , &[_]diag.DiagnosticCode{.insert_requires_code});
}

test "code insert - requires declarations" {
    try checkProgram(
        \\
        \\ build_bad :: proc() Code { return code { 1 } }
        \\ comptime { insert build_bad() }
    , &[_]diag.DiagnosticCode{ .checker_code_block_not_executed, .insert_requires_decl });
}

test "code splice - statement requires code" {
    try checkProgram(
        \\
        \\ v :: 1
        \\ comptime { insert code { `v` } }
    , &[_]diag.DiagnosticCode{ .checker_code_block_not_executed, .code_splice_requires_code });
}

test "code splice - expression requires single expr" {
    try checkProgram(
        \\
        \\ block :: code {
        \\   a :: 1
        \\   b :: 2
        \\ }
        \\ comptime { insert code { value :: `block` } }
    , &[_]diag.DiagnosticCode{ .checker_code_block_not_executed, .code_splice_requires_expr });
}

test "code splice - type requires type" {
    try checkProgram(
        \\
        \\ X :: 1
        \\ comptime { insert code { value: `X` = 1 } }
    , &[_]diag.DiagnosticCode{ .checker_code_block_not_executed, .code_splice_requires_type });
}
