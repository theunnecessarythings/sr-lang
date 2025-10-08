const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "expressions_operators: integer addition" {
    const src =
        \\r := 10 + 20
        \\printf("Result: %d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 30\n");
}

test "expressions_operators: float subtraction" {
    const src =
        \\r := 25.5 - 10.2
        \\printf("Result: %f\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 15.300000\n");
}

test "expressions_operators: integer multiplication" {
    const src =
        \\r := 5 * 7
        \\printf("Result: %d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 35\n");
}

test "expressions_operators: integer division" {
    const src =
        \\r := 20 / 3
        \\printf("Result: %d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 6\n"); // Integer division truncates
}

test "expressions_operators: integer modulo" {
    const src =
        \\r := 20 % 3
        \\printf("Result: %d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 2\n");
}

test "expressions_operators: operator precedence" {
    const src =
        \\r := 1 + 2 * 3
        \\printf("Result: %d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 7\n");
}

test "expressions_operators: unary minus" {
    const src =
        \\r := -10
        \\printf("Result: %d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: -10\n");
}
