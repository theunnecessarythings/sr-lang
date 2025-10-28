const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "literals: standard float" {
    const src =
        \\ x := 123.45;
        \\ printf("x=%f\n", x);
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=123.450000\n");
}

test "literals: negative float" {
    const src =
        \\ x := -67.89;
        \\ printf("x=%f\n", x);
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=-67.890000\n");
}

test "literals: scientific notation (positive exponent)" {
    const src =
        \\ x := 1.0e5;
        \\ printf("x=%f\n", x);
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=100000.000000\n");
}

test "literals: scientific notation (negative exponent)" {
    const src =
        \\ x := 1.0e-3;
        \\ printf("x=%f\n", x);
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=0.001000\n");
}
