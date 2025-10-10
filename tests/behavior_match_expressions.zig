const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "control_flow: match with literal integer" {
    const src =
        \\x := 2
        \\result := match x {
        \\  1 => 10,
        \\  2 => 20,
        \\  _ => 30,
        \\}
        \\printf("Result: %d\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 20\n");
}

test "control_flow: match with or-pattern" {
    const src =
        \\x := 3
        \\result := match x {
        \\  1 | 2 => 10,
        \\  3 | 4 => 20,
        \\  _ => 30,
        \\}
        \\printf("Result: %d\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 20\n");
}

test "control_flow: match with range pattern" {
    const src =
        \\x := 7
        \\result := match x {
        \\  0..=5 => 10,
        \\  6..10 => 20,
        \\  _ => 30,
        \\}
        \\printf("Result: %d\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 20\n");
}

test "control_flow: match with enum variant" {
    const globals =
        \\Color :: enum { Red, Green, Blue }
    ;
    const src =
        \\c := Color.Green
        \\result := match c {
        \\  Color.Red => "Red",
        \\  Color.Green => "Green",
        \\  Color.Blue => "Blue",
        \\}
        \\printf("Color: %s\n", result)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Color: Green\n");
}

test "control_flow: match with variant payload (tuple)" {
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

test "control_flow: match with struct pattern" {
    const globals =
        \\Point :: struct { x: i32, y: i32 }
    ;
    const src =
        \\p := Point{ x: 5, y: 10 }
        \\match p {
        \\  Point{ x: px, y: py } => printf("Point at %d, %d\n", px, py),
        \\  _ => printf("Other pattern\n"),
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Point at 5, 10\n");
}

test "control_flow: match with if guard" {
    const src =
        \\x := 15
        \\result := match x {
        \\  y if y < 10 => "Small",
        \\  y if y >= 10 and y < 20 => "Medium",
        \\  _ => "Large",
        \\}
        \\printf("Size: %s\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Size: Medium\n");
}
