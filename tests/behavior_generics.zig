const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "generics: simple specialization" {
    const globals =
        \\
        \\ max :: fn(comptime T: type, a: T, b: T) T {
        \\   return if a > b { a } else { b };
        \\ }
        \\ clamp :: fn(comptime T: type, comptime Limit: T, value: T) T {
        \\   return if value > Limit { Limit } else { value };
        \\ }
    ;

    const src =
        \\
        \\ printf("%d\n", max(i32, 10, 7))
        \\ printf("%d\n", clamp(i32, 5, 42))
    ;

    const code = getSource(globals, src);
    try runCompilerTest(code, "10\n5\n");
}

test "generics: nested type specializations" {
    const globals =
        \\
        \\ Vec :: fn(comptime T: type, comptime N: usize) type {
        \\   return struct { data: [N]T };
        \\ }
        \\ Matrix :: fn(comptime T: type, comptime R: usize, comptime C: usize) type {
        \\   Row :: Vec(T, C)
        \\   return struct { rows: [R]Row };
        \\ }
        \\ MatrixI32x2x3 :: Matrix(i32, 2, 3)
    ;

    const src =
        \\
        \\ row0 := Vec(i32, 3){ data : [1, 2, 3] }
        \\ row1 := Vec(i32, 3){ data : [4, 5, 6] }
        \\ mat := MatrixI32x2x3{ rows : [row0, row1] }
        \\ printf("%d,%d\n", mat.rows[0].data[2], mat.rows[1].data[0])
    ;

    const code = getSource(globals, src);
    try runCompilerTest(code, "3,4\n");
}
