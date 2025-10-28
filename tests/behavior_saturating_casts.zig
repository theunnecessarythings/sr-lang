const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "casts: i32 to i8 saturating (overflow max)" {
    const src =
        \\big_int: i32 = 99999
        \\saturated_to_i8 := big_int.|i8
        \\printf("Result: %d\n", saturated_to_i8)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 127\n"); // i8::MAX
}

test "casts: i32 to i8 saturating (overflow min)" {
    const src =
        \\small_int: i32 = -99999
        \\saturated_to_i8 := small_int.|i8
        \\printf("Result: %d\n", saturated_to_i8.(i64))
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: -128\n"); // i8::MIN
}

test "casts: i32 to u8 saturating (negative)" {
    const src =
        \\neg_int: i32 = -10
        \\saturated_to_u8 := neg_int.|u8
        \\printf("Result: %d\n", saturated_to_u8)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 0\n"); // u8::MIN
}

test "casts: i32 to u8 saturating (overflow max)" {
    const src =
        \\big_int: i32 = 300
        \\saturated_to_u8 := big_int.|u8
        \\printf("Result: %d\n", saturated_to_u8)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 255\n"); // u8::MAX
}
