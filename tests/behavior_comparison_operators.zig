const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "expressions_operators: integer equality" {
    const src =
        \\r := 10 == 10
        \\printf("Result: %b\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 1\n");
}

test "expressions_operators: float inequality" {
    const src =
        \\r := 10.5 != 10.6
        \\printf("Result: %b\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 1\n");
}

test "expressions_operators: less than" {
    const src =
        \\r := 5 < 10
        \\printf("Result: %b\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 1\n");
}

test "expressions_operators: greater than or equal to" {
    const src =
        \\r := 10 >= 10
        \\printf("Result: %b\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 1\n");
}

test "expressions_operators: string equality" {
    if (true) return error.SkipZigTest;
    const src =
        \\r := "hello" == "hello"
        \\printf("Result: %b\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 1\n");
}

test "expressions_operators: boolean inequality" {
    const src =
        \\r := true != false
        \\printf("Result: %b\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 1\n");
}
