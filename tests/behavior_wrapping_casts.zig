const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "casts: i32 to u8 wrapping (overflow)" {
    const src =
        \\x: i32 = 256
        \\r := x.%u8
        \\printf("Result: %d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 0\n"); // 256 wraps to 0 for u8
}

test "casts: u8 to i8 wrapping (overflow)" {
    const src =
        \\x: u8 = 128
        \\r := x.%i8
        \\printf("Result: %d\n", r.(i64))
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: -128\n"); // 128 wraps to -128 for i8
}

test "casts: negative i32 to u8 wrapping" {
    const src =
        \\x: i32 = -1
        \\r := x.%u8
        \\printf("Result: %d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 255\n"); // -1 wraps to 255 for u8
}
