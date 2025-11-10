const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "expressions_operators: bitwise AND" {
    const src =
        \\r := 0b1010 & 0b1100  // 10 & 12 = 8 (0b1000)
        \\printf("Result: %d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 8\n");
}

test "expressions_operators: bitwise OR" {
    const src =
        \\r := 0b1010 | 0b1100  // 10 | 12 = 14 (0b1110)
        \\printf("Result: %d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 14\n");
}

test "expressions_operators: bitwise XOR" {
    const src =
        \\r := 0b1010 ^ 0b1100  // 10 ^ 12 = 6 (0b0110)
        \\printf("Result: %d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 6\n");
}

test "expressions_operators: left shift" {
    const src =
        \\r := 0b0001 << 2  // 1 << 2 = 4 (0b0100)
        \\printf("Result: %d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 4\n");
}

test "expressions_operators: right shift" {
    const src =
        \\r := 0b1000 >> 2  // 8 >> 2 = 2 (0b0010)
        \\printf("Result: %d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 2\n");
}

