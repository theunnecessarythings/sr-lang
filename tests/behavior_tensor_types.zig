const std = @import("std");
const behavior = @import("behavior.zig");

// Import functions from behavior.zig
const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "special_types: tensor declaration and initialization (2D)" {
    const src =
        \\t: tensor(i32, 2, 3) = [[1, 2, 3], [4, 5, 6]]
        \\printf("Tensor[0][1]=%d, Tensor[1][2]=%d\n", t[0][1], t[1][2])
    ;

    const code = getSource("", src);
    try runCompilerTest(code, "Tensor[0][1]=2, Tensor[1][2]=6\n");
}

test "special_types: tensor element access and modification" {
    const src =
        \\t: tensor(f32, 2, 2) = [[1.0, 2.0], [3.0, 4.0]]
        \\t[0][0] = 99.0
        \\printf("Modified Tensor[0][0]=%f\n", t[0][0].(f64))
    ;

    const code = getSource("", src);
    try runCompilerTest(code, "Modified Tensor[0][0]=99.000000\n");
}

test "special_types: tensor addition (element-wise)" {
    const src =
        \\t1: tensor(i32, 2, 2) = [[1, 2], [3, 4]]
        \\t2: tensor(i32, 2, 2) = [[5, 6], [7, 8]]
        \\sum := t1 + t2
        \\printf("Sum[0][0]=%d, Sum[1][1]=%d\n", sum[0][0], sum[1][1])
    ;

    const code = getSource("", src);
    try runCompilerTest(code, "Sum[0][0]=6, Sum[1][1]=12\n");
}
