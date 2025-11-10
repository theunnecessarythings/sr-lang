const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "expressions_operators: basic function call with arguments" {
    const globals =
        \\add :: fn(a: i32, b: i32) i32 {
        \\  return a + b
        \\}
    ;
    const src =
        \\r := add(5, 7)
        \\printf("Result: %d\n", r)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Result: 12\n");
}

test "expressions_operators: basic function call without arguments" {
    const globals =
        \\get_answer :: fn() i32 {
        \\  return 42
        \\}
    ;
    const src =
        \\r := get_answer()
        \\printf("Answer: %d\n", r)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Answer: 42\n");
}

test "expressions_operators: basic procedure call with arguments" {
    const globals =
        \\print_val :: proc(val: i32) {
        \\  printf("Value: %d\n", val)
        \\}
    ;
    const src =
        \\print_val(15)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Value: 15\n");
}

test "expressions_operators: basic procedure call without arguments" {
    const globals =
        \\say_hello :: proc() {
        \\  printf("Hello\n")
        \\}
    ;
    const src =
        \\say_hello()
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Hello\n");
}

test "expressions_operators: nested function calls" {
    const globals =
        \\add :: fn(a: i32, b: i32) i32 {
        \\  return a + b
        \\}
        \\multiply :: fn(a: i32, b: i32) i32 {
        \\  return a * b
        \\}
    ;
    const src =
        \\r := multiply(add(2, 3), 4) // (2+3)*4 = 20
        \\printf("Result: %d\n", r)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Result: 20\n");
}

