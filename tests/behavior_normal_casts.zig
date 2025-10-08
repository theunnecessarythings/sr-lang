const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "casts: integer to integer (wider to narrower)" {
    const src =
        \\x: i32 = 256
        \\y := x.(u8) // Should truncate
        \\printf("Result: %d\n", y)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 0\n");
}

test "casts: integer to integer (narrower to wider)" {
    const src =
        \\x: u8 = 100
        \\y := x.(i32)
        \\printf("Result: %d\n", y)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 100\n");
}

test "casts: float to integer (truncation)" {
    const src =
        \\x := 123.45
        \\y := x.(i32)
        \\printf("Result: %d\n", y)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 123\n");
}

test "casts: integer to float" {
    const src =
        \\x := 100
        \\y := x.(f64)
        \\printf("Result: %f\n", y)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 100.000000\n");
}

test "casts: float to float (wider to narrower)" {
    const src =
        \\x: f64 = 3.1415926535
        \\y := x.(f32) // Potential precision loss
        \\printf("Result: %f\n", y.(f64))
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 3.141593\n"); // Value might vary slightly due to precision
}
