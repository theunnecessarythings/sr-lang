const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "misc: exclusive range in for loop" {
    const src =
        \\sum := 0
        \\for i in 0..3 { // 0, 1, 2
        \\  sum = sum + i.(i64)
        \\}
        \\printf("Sum: %d\n", sum)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Sum: 3\n");
}

test "misc: inclusive range in for loop" {
    const src =
        \\sum := 0
        \\for i in 0..=3 { // 0, 1, 2, 3
        \\  sum = sum + i.(i64)
        \\}
        \\printf("Sum: %d\n", sum)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Sum: 6\n");
}

test "misc: exclusive range assigned to variable" {
    const src =
        \\r := 1..5
        \\// Assuming range objects can be iterated or converted
        \\// For now, just check if it compiles and assigns
        \\printf("Range assigned\n")
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Range assigned\n");
}

test "misc: inclusive range assigned to variable" {
    const src =
        \\r := 1..=5
        \\printf("Range assigned\n")
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Range assigned\n");
}
