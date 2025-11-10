const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "literals: decimal integer" {
    const src =
        \\ x := 123;
        \\ printf("x=%d\n", x);
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=123\n");
}

test "literals: negative decimal integer" {
    const src =
        \\ x := -456;
        \\ printf("x=%d\n", x);
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=-456\n");
}

test "literals: hexadecimal integer" {
    const src =
        \\ x := 0xFF;
        \\ printf("x=%d\n", x);
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=255\n");
}

test "literals: octal integer" {
    const src =
        \\ x := 0o755;
        \\ printf("x=%d\n", x);
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=493\n");
}

test "literals: binary integer" {
    const src =
        \\ x := 0b1011_0011;
        \\ printf("x=%d\n", x);
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=179\n");
}

test "literals: integer with digit separators" {
    const src =
        \\ x := 1_000_000;
        \\ printf("x=%d\n", x);
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=1000000\n");
}

test "literals: hexadecimal with digit separators" {
    const src =
        \\ x := 0x_FF_00;
        \\ printf("x=%d\n", x);
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=65280\n");
}
