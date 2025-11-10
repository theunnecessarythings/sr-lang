const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "composite_types: unit-like variant" {
    const globals =
        \\Message :: variant { Quit, Move(i32, i32) }
    ;
    const src =
        \\m := Message.Quit
        \\match m {
        \\  Message.Quit => printf("Quit message\n"),
        \\  _ => printf("Other message\n"),
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Quit message\n");
}

test "composite_types: tuple-like variant" {
    const globals =
        \\Message :: variant { Quit, Move(i32, i32) }
    ;
    const src =
        \\m := Message.Move(10, 20)
        \\match m {
        \\  Message.Move(x, y) => printf("Move to %d, %d\n", x, y),
        \\  _ => printf("Other message\n"),
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Move to 10, 20\n");
}

test "composite_types: struct-like variant" {
    const globals =
        \\Event :: variant { Click { x: i32, y: i32 }, KeyPress(char) }
    ;
    const src =
        \\e := Event.Click{ x: 100, y: 200 }
        \\match e {
        \\  Event.Click{ x, y } => printf("Click at %d, %d\n", x, y),
        \\  _ => printf("Other event\n"),
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Click at 100, 200\n");
}

test "composite_types: nested variants" {
    const globals =
        \\Inner :: variant { A(i32), B }
        \\Outer :: variant { Wrap(Inner), Unwrap }
    ;
    const src =
        \\o := Outer.Wrap(Inner.A(50))
        \\match o {
        \\  Outer.Wrap(Inner.A(val)) => printf("Nested A with value %d\n", val),
        \\  _ => printf("Other nested variant\n"),
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Nested A with value 50\n");
}

