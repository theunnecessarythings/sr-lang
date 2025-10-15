const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "composite_types: basic fixed-size array" {
    const src =
        \\arr: [3]i32 = [1, 2, 3]
        \\printf("Array: %d, %d, %d\n", arr[0], arr[1], arr[2])
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Array: 1, 2, 3\n");
}

test "composite_types: array indexing and modification" {
    const src =
        \\arr: [3]i32 = [10, 20, 30]
        \\arr[1] = 25
        \\printf("Modified array: %d, %d, %d\n", arr[0], arr[1], arr[2])
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Modified array: 10, 25, 30\n");
}

test "composite_types: nested arrays (2D matrix)" {
    const src =
        \\matrix: [2][2]i32 = [[1, 2], [3, 4]]
        \\printf("Matrix[0][1]=%d, Matrix[1][0]=%d\n", matrix[0][1], matrix[1][0])
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Matrix[0][1]=2, Matrix[1][0]=3\n");
}

test "composite_types: array iteration with for loop" {
    const src =
        \\arr: [4]i32 = [1, 2, 3, 4]
        \\sum : i32 = 0
        \\for x in arr {
        \\  sum = sum + x
        \\}
        \\printf("Array sum=%d\n", sum)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Array sum=10\n");
}

test "composite_types: array length from comptime binding" {
    const src =
        \\len: usize = 3
        \\arr: [len]i32 = [7, 8, 9]
        \\printf("arr=%d,%d,%d\n", arr[0], arr[1], arr[2])
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "arr=7,8,9\n");
}
