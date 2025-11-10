const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "patterns: wildcard in match expression" {
    const src =
        \\x := 10
        \\result := match x {
        \\  1 => "One",
        \\  _ => "Other",
        \\}
        \\printf("Result: %s\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: Other\n");
}

test "patterns: wildcard in tuple destructuring" {
    const src =
        \\(a, _, c) := (1, 2, 3)
        \\printf("a=%d, c=%d\n", a, c)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "a=1, c=3\n");
}

test "patterns: wildcard in struct destructuring" {
    const globals =
        \\Point :: struct { x: i32, y: i32 }
    ;
    const src =
        \\Point{ x: px, y: _ } := Point{ x: 10, y: 20 }
        \\printf("Point x: %d\n", px)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Point x: 10\n");
}

test "patterns: wildcard in variant destructuring" {
    const globals =
        \\Message :: variant { Quit, Move(i32, i32) }
    ;
    const src =
        \\m := Message.Move(10, 20)
        \\match m {
        \\  Message.Move(_, y) => printf("Move y: %d\n", y),
        \\  _ => printf("Other message\n"),
        \\}
        \\printf("After match\n")
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Move y: 20\nAfter match\n");
}
