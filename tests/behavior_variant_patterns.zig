const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "patterns: basic unit-like variant pattern" {
    const globals =
        \\Message :: variant { Quit, Move(i32, i32) }
    ;
    const src =
        \\m := Message.Quit
        \\result := match m {
        \\  Message.Quit => "Quit",
        \\  _ => "Other",
        \\}
        \\printf("Result: %s\n", result)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Result: Quit\n");
}

test "patterns: tuple-like variant pattern with binding" {
    const globals =
        \\Message :: variant { Quit, Move(i32, i32) }
    ;
    const src =
        \\m := Message.Move(10, 20)
        \\match m {
        \\  Message.Move(x, y) => printf("Move to %d, %d\n", x, y),
        \\  _ => printf("Other\n"),
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Move to 10, 20\n");
}

test "patterns: struct-like variant pattern with binding" {
    const globals =
        \\Event :: variant { Click { x: i32, y: i32 }, KeyPress(char) }
    ;
    const src =
        \\e := Event.Click{ x: 100, y: 200 }
        \\match e {
        \\  Event.Click{ x: px, y: py } => printf("Click at %d, %d\n", px, py),
        \\  _ => printf("Other\n"),
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Click at 100, 200\n");
}

test "patterns: variant pattern with wildcard" {
    const globals =
        \\Message :: variant { Quit, Move(i32, i32) }
    ;
    const src =
        \\m := Message.Move(10, 20)
        \\match m {
        \\  Message.Move(_, y) => printf("Move y: %d\n", y),
        \\  _ => printf("Other\n"),
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Move y: 20\n");
}

test "patterns: nested variant pattern" {
    const globals =
        \\Inner :: variant { A(i32), B }
        \\Outer :: variant { Wrap(Inner), Unwrap }
    ;
    const src =
        \\o := Outer.Wrap(Inner.A(50))
        \\match o {
        \\  Outer.Wrap(Inner.A(val)) => printf("Nested A with value %d\n", val),
        \\  _ => printf("Other\n"),
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Nested A with value 50\n");
}

