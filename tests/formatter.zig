const std = @import("std");
const compiler = @import("compiler");
const formatter = compiler.formatter;

fn testFormat(source: [:0]const u8, expected: []const u8) !void {
    const gpa = std.testing.allocator;
    const formatted = try formatter.formatSource(gpa, source, "test.sr");
    defer gpa.free(formatted);

    try std.testing.expectEqualStrings(expected, formatted);
}

test "basic function indentation" {
    const input =
        \\main :: proc() {
        \\return 0
        \\}
    ;
    const expected =
        \\main :: proc() {
        \\    return 0
        \\}
        \\
    ;
    try testFormat(input, expected);
}

test "struct formatting" {
    const input =
        \\Point :: struct {
        \\x: i32,
        \\y: i32,
        \\}
    ;
    const expected =
        \\Point :: struct {
        \\    x: i32,
        \\    y: i32,
        \\}
        \\
    ;
    try testFormat(input, expected);
}

test "enum formatting" {
    const input =
        \\State :: enum {
        \\Running,
        \\Walking,
        \\}
    ;
    const expected =
        \\State :: enum {
        \\    Running,
        \\    Walking,
        \\}
        \\
    ;
    try testFormat(input, expected);
}

test "function call spacing" {
    const input =
        \\main :: proc() {
        \\add(1,2)
        \\}
    ;
    const expected =
        \\main :: proc() {
        \\    add(1, 2)
        \\}
        \\
    ;
    try testFormat(input, expected);
}

test "import statement" {
    const input =
        \\package main
        \\import "std"
    ;
    const expected =
        \\package main
        \\
        \\import "std"
        \\
    ;
    try testFormat(input, expected);
}

test "complex structs and enums" {
    const input =
        \\package structs_enums
        \\
        \\event := Event.Click{ x: 100, y: 50 }
        \\
        \\// Struct definition
        \\Point :: struct {
        \\  x: i32,
        \\  y: i32,
        \\}
        \\
        \\// Union definition
        \\IntOrFloat :: union {
        \\    i: i32,
        \\    f: f32,
        \\}
        \\
        \\// C-style enum
        \\State :: enum {
        \\  Running,
        \\  Walking,
        \\}
    ;
    const expected =
        \\package structs_enums
        \\
        \\event := Event.Click{ x: 100, y: 50 }
        \\
        \\// Struct definition
        \\Point :: struct {
        \\    x: i32,
        \\    y: i32,
        \\}
        \\
        \\// Union definition
        \\IntOrFloat :: union {
        \\    i: i32,
        \\    f: f32,
        \\}
        \\
        \\// C-style enum
        \\State :: enum {
        \\    Running,
        \\    Walking,
        \\}
        \\
    ;
    try testFormat(input, expected);
}

test "comments" {
    const input =
        \\// Top level comment
        \\
        \\// Another top level
        \\main :: proc() {
        \\    // Indented comment
        \\    a := 1 // Inline comment
        \\    /* Block comment */
        \\    b := 2
        \\}
        \\
        \\/// Doc comment
        \\Type :: struct {}
    ;
    const expected =
        \\// Top level comment
        \\
        \\// Another top level
        \\main :: proc() {
        \\    // Indented comment
        \\    a := 1 // Inline comment
        \\    /* Block comment */
        \\    b := 2
        \\}
        \\
        \\/// Doc comment
        \\Type :: struct {}
        \\
    ;
    try testFormat(input, expected);
}

test "trailing commas" {
    const input =
        \\a := [1, 2, 3,]
        \\b := [1, 2, 3]
        \\s := S{ x: 1, y: 2, }
        \\s2 := S{ x: 1, y: 2 }
    ;
    const expected =
        \\a := [
        \\    1,
        \\    2,
        \\    3,
        \\]
        \\b := [1, 2, 3]
        \\s := S{
        \\    x: 1,
        \\    y: 2,
        \\}
        \\s2 := S{ x: 1, y: 2 }
        \\
    ;
    try testFormat(input, expected);
}

test "test declarations" {
    const input =
        \\test "hello world" {
        \\  io.assert(1 + 1 == 2, "1 + 1 != 2")
        \\}
        \\
        \\test "fail" {
        \\  return Error.Fail
        \\}
    ;
    const expected =
        \\test "hello world" {
        \\    io.assert(1 + 1 == 2, "1 + 1 != 2")
        \\}
        \\
        \\test "fail" {
        \\    return Error.Fail
        \\}
        \\
    ;
    try testFormat(input, expected);
}

test "mlir formatting" {
    const input =
        \\foo :: proc(x: i32) {
        \\mlir op(x) : void { "some.op"(%arg0) : (i32) -> () }
        \\}
    ;
    const expected =
        \\foo :: proc(x: i32) {
        \\    mlir op(x) : void { "some.op"(%arg0) : (i32) -> () }
        \\}
        \\
    ;
    try testFormat(input, expected);
}
