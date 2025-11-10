const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "expressions_operators: logical AND" {
    const src =
        \\r1 := true and true
        \\r2 := true and false
        \\printf("True AND True: %b\n", r1)
        \\printf("True AND False: %b\n", r2)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "True AND True: 1\nTrue AND False: 0\n");
}

test "expressions_operators: logical OR" {
    const src =
        \\r1 := true or false
        \\r2 := false or false
        \\printf("True OR False: %b\n", r1)
        \\printf("False OR False: %b\n", r2)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "True OR False: 1\nFalse OR False: 0\n");
}

test "expressions_operators: logical NOT" {
    const src =
        \\r1 := !true
        \\r2 := !false
        \\printf("NOT True: %b\n", r1)
        \\printf("NOT False: %b\n", r2)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "NOT True: 0\nNOT False: 1\n");
}

test "expressions_operators: logical operator precedence" {
    const src =
        \\r := true and false or true
        \\printf("Result: %b\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 1\n"); // (true and false) -> false; false or true -> true
}

