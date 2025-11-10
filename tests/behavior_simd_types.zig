const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "special_types: simd vector declaration and initialization" {
    const src =
        \\vec: simd(f64, 4) = [1.0, 2.0, 3.0, 4.0]
        \\printf("SIMD vec: %f, %f, %f, %f\n", vec[0], vec[1], vec[2], vec[3])
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "SIMD vec: 1.000000, 2.000000, 3.000000, 4.000000\n");
}

test "special_types: simd vector element access" {
    const src =
        \\vec: simd(i32, 2) = [10, 20]
        \\printf("First element: %d\n", vec[0])
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "First element: 10\n");
}

test "special_types: simd vector addition" {
    const src =
        \\vec1: simd(f32, 2) = [1.0, 2.0]
        \\vec2: simd(f32, 2) = [3.0, 4.0]
        \\sum := vec1 + vec2
        \\printf("SIMD sum: %f, %f\n", sum[0].(f64), sum[1].(f64))
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "SIMD sum: 4.000000, 6.000000\n");
}

test "special_types: simd vector multiplication" {
    const src =
        \\vec1: simd(i32, 2) = [2, 3]
        \\vec2: simd(i32, 2) = [4, 5]
        \\prod := vec1 * vec2
        \\printf("SIMD product: %d, %d\n", prod[0], prod[1])
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "SIMD product: 8, 15\n");
}
