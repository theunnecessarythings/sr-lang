const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "patterns: basic struct pattern" {
    const globals =
        \\Point :: struct { x: i32, y: i32 }
    ;
    const src =
        \\p := Point{ x: 10, y: 20 }
        \\result := match p {
        \\  Point{ x: 10, y: 20 } => "Matched (10, 20)",
        \\  _ => "Other",
        \\}
        \\printf("Result: %s\n", result)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Result: Matched (10, 20)\n");
}

test "patterns: struct pattern with variable binding" {
    const globals =
        \\Point :: struct { x: i32, y: i32 }
    ;
    const src =
        \\p := Point{ x: 100, y: 200 }
        \\match p {
        \\  Point{ x: px, y: py } => printf("X: %d, Y: %d\n", px, py),
        \\  _ => printf("Other\n"),
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "X: 100, Y: 200\n");
}

test "patterns: partial struct pattern" {
    if (true) return error.SkipZigTest;
    const globals =
        \\User :: struct { id: i32, name: string, age: i32 }
    ;
    const src =
        \\u := User{ id: 1, name: "Alice", age: 30 }
        \\match u {
        \\  User{ name: "Alice", .. } => printf("Matched Alice\n"),
        \\  _ => printf("Other\n"),
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Matched Alice\n");
}

test "patterns: nested struct pattern" {
    const globals =
        \\Point :: struct { x: i32, y: i32 }
        \\Rect  :: struct { tl: Point, br: Point }
    ;
    const src =
        \\r := Rect{ tl: Point{ x: 0, y: 0 }, br: Point{ x: 10, y: 10 } }
        \\match r {
        \\  Rect{ tl: Point{ x: tx, y: ty }, br: Point{ x: bx, y: by } } =>
        \\    printf("TL: (%d, %d), BR: (%d, %d)\n", tx, ty, bx, by),
        \\  _ => printf("Other\n"),
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "TL: (0, 0), BR: (10, 10)\n");
}
