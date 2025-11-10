const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "casts: integer to float bitcast" {
    const src =
        \\some_bits: u32 = 0x42F6E979 // Represents 123.45 in IEEE 754 single-precision
        \\bits_as_float := some_bits.^f32
        \\printf("Result: %f\n", bits_as_float.(f64)) // Promote to f64 for printf
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 123.456001\n");
}

test "casts: float to integer bitcast" {
    const src =
        \\some_float: f32 = 123.45
        \\float_as_bits := some_float.^u32
        \\printf("Result: 0x%X\n", float_as_bits)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 0x42F6E666\n");
}

test "casts: u32 to i32 bitcast" {
    const src =
        \\x: u32 = 0xFFFFFFFF // -1 as i32
        \\y := x.^i32
        \\printf("Result: %d\n", y)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: -1\n");
}
