const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "misc: basic block expression" {
    const src =
        \\x := {
        \\  10 + 5
        \\}
        \\printf("Result: %d\n", x)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 15\n");
}

test "misc: block with multiple statements" {
    const src =
        \\x := {
        \\  tmp := 20
        \\  tmp + 5
        \\}
        \\printf("Result: %d\n", x)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 25\n");
}

test "misc: nested block expressions" {
    const src =
        \\x := {
        \\  y := {
        \\    1 + 1
        \\  }
        \\  y * 3
        \\}
        \\printf("Result: %d\n", x)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 6\n");
}

test "misc: block with variable scoping" {
    const src =
        \\outer_var := 10
        \\{
        \\  inner_var := 20
        \\  printf("Inner var: %d\n", inner_var)
        \\}
        \\printf("Outer var: %d\n", outer_var)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Inner var: 20\nOuter var: 10\n");
}
