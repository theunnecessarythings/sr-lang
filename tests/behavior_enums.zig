const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "composite_types: c-style enum definition and usage" {
    const globals =
        \\State :: enum { Running, Paused, Stopped }
    ;
    const src =
        \\s := State.Running
        \\printf("State: %d\n", s)
        \\if s == State.Running {
        \\  printf("State is Running\n")
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "State: 0\nState is Running\n");
}

test "composite_types: integer-backed enum" {
    const globals =
        \\HttpCode :: enum(u16) { Ok = 200, NotFound = 404, InternalError = 500 }
    ;
    const src =
        \\c := HttpCode.InternalError
        \\printf("HttpCode: %d\n", c)
        \\if c == HttpCode.InternalError {
        \\  printf("Code is InternalError\n")
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "HttpCode: 2\nCode is InternalError\n");
}

test "composite_types: enum in match expression" {
    const globals =
        \\Color :: enum { Red, Green, Blue }
    ;
    const src =
        \\c := Color.Green
        \\match c {
        \\  Color.Red => printf("Color is Red\n"),
        \\  Color.Green => printf("Color is Green\n"),
        \\  Color.Blue => printf("Color is Blue\n"),
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Color is Green\n");
}
