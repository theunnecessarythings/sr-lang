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

test "control_flow: match with open and closed range patterns" {
    const src =
        \\x := 5
        \\result1 := match x {
        \\  ..5 => "lt",
        \\  _ => "ge",
        \\}
        \\y := 5
        \\result2 := match y {
        \\  ..=5 => "le",
        \\  _ => "gt",
        \\}
        \\z := 5
        \\result3 := match z {
        \\  5.. => "ge",
        \\  _ => "lt",
        \\}
        \\printf("%s %s %s\n", result1, result2, result3)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "ge le ge\n");
}

test "control_flow: match with range inside at-pattern" {
    const src =
        \\x := 7
        \\result := match x {
        \\  y @ (0..5) => y,
        \\  _ => 99,
        \\}
        \\printf("Result: %d\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 99\n");
}

test "control_flow: match with range inside or-pattern" {
    const src =
        \\x := 10
        \\result := match x {
        \\  0 | 1..5 => 111,
        \\  _ => 222,
        \\}
        \\printf("Result: %d\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 222\n");
}
