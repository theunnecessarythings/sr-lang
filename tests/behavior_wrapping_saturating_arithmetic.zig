const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "expressions_operators: wrapping addition" {
    const src =
        \\x: u8 = 250
        \\y: u8 = 10
        \\r := x +% y // Should wrap around
        \\printf("Result: %d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 4\n"); // 250 + 10 = 260, 260 % 256 = 4
}

test "expressions_operators: wrapping add assignment" {
    const src =
        \\x: u8 = 250
        \\x +%= 10.(u8)
        \\printf("Result: %d\n", x)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 4\n");
}

test "expressions_operators: saturating addition" {
    const src =
        \\x: u8 = 250
        \\y: u8 = 10
        \\r := x +| y // Should saturate at 255
        \\printf("Result: %d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 255\n");
}

test "expressions_operators: saturating multiply assignment" {
    const src =
        \\x: u8 = 100
        \\x *|= 3.(u8) // 100 * 3 = 300, should saturate at 255
        \\printf("Result: %d\n", x)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 255\n");
}

test "expressions_operators: saturating addition clamps signed max" {
    const src =
        \\x: i8 = 120
        \\y: i8 = 120
        \\r := x +| y
        \\printf("Result: %d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 127\n");
}

test "expressions_operators: saturating addition clamps signed min" {
    const src =
        \\x: i8 = -120
        \\y: i8 = -20
        \\r := x +| y
        \\printf("Result: %d\n", r.(i64))
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: -128\n");
}

test "expressions_operators: saturating multiplication clamps signed min" {
    const src =
        \\x: i8 = -70
        \\y: i8 = 3
        \\r := x *| y
        \\printf("Result: %d\n", r.(i64))
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: -128\n");
}

test "expressions_operators: saturating shift clamps to max" {
    const src =
        \\x: u8 = 200
        \\r := x <<| 2.(u8)
        \\printf("Result: %d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 255\n");
}
