const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "casts: i32 to i8 checked (in range)" {
    const src =
        \\x: i32 = 100
        \\r := x.?i8
        \\if r != null {
        \\  printf("Result: %d\n", r?)
        \\} else {
        \\  printf("Result: null\n")
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 100\n");
}

test "casts: i32 to i8 checked (out of range)" {
    const src =
        \\x: i32 = 200
        \\r := x.?i8
        \\if r != null {
        \\  printf("Result: %d\n", r?)
        \\} else {
        \\  printf("Result: null\n")
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: null\n");
}

test "casts: float to i32 checked (in range)" {
    const src =
        \\x: f32 = 123.0
        \\r := x.?i32
        \\if r != null {
        \\  printf("Result: %d\n", r?)
        \\} else {
        \\  printf("Result: null\n")
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 123\n");
}

test "casts: float to i32 checked (out of range)" {
    const src =
        \\x: f32 = 2147483648.0 // i32 max is 2147483647
        \\r := x.?i32
        \\if r != null {
        \\  printf("Result: %d\n", r?)
        \\} else {
        \\  printf("Result: null\n")
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: null\n");
}

test "casts: float to i32 checked (just below min)" {
    const src =
        \\x: f64 = -2147483649.0
        \\r := x.?i32
        \\if r != null {
        \\  printf("Result: %d\n", r?)
        \\} else {
        \\  printf("Result: null\n")
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: null\n");
}

test "casts: float to i32 checked (just above max)" {
    const src =
        \\x: f64 = 2147483647.0 + 0.5
        \\r := x.?i32
        \\if r != null {
        \\  printf("Result: %d\n", r?)
        \\} else {
        \\  printf("Result: null\n")
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: null\n");
}
