const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "declarations: tuple destructuring" {
    const src =
        \\ (a, b) := (10, 20);
        \\ printf("a=%d, b=%d\n", a, b);
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "a=10, b=20\n");
}

test "declarations: struct destructuring" {
    const globals =
        \\ Point :: struct { x: i32, y: i32 };
    ;
    const src =
        \\ Point{ x: a, y: b } := Point{ x: 100, y: 200 };
        \\ printf("x=%d, y=%d\n", a, b);
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "x=100, y=200\n");
}

test "declarations: partial struct destructuring" {
    if (true) return error.SkipZigTest;
    const globals =
        \\ User :: struct { id: i32, name: string, age: i32 };
    ;
    const src =
        \\ User{ name: user_name, .. } := User{ id: 1, name: "Alice", age: 30 };
        \\ printf("User name=%s\n", user_name);
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "User name=Alice\n");
}

test "declarations: variant destructuring (tuple payload)" {
    const globals =
        \\ Result :: variant { Ok(i32), Err(string) };
    ;
    const src =
        \\ Result.Ok(value) := Result.Ok(42);
        \\ printf("Value=%d\n", value);
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Value=42\n");
}

test "declarations: variant destructuring (struct payload)" {
    const globals =
        \\ Event :: variant { Click { x: i32, y: i32 } };
    ;
    const src =
        \\ Event.Click{ x: click_x, y: click_y } := Event.Click{ x: 10, y: 20 };
        \\ printf("Click x=%d, y=%d\n", click_x, click_y);
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Click x=10, y=20\n");
}

test "declarations: nested tuple destructuring" {
    const src =
        \\ (a, (b, c)) := (1, (2, 3));
        \\ printf("a=%d, b=%d, c=%d\n", a, b, c);
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "a=1, b=2, c=3\n");
}

test "declarations: nested struct destructuring" {
    const globals =
        \\ Point :: struct { x: i32, y: i32 };
        \\ Rect :: struct { tl: Point, br: Point };
    ;
    const src =
        \\ Rect{ tl: Point{ x: tx, y: ty }, br: Point{ x: bx, y: by } } := Rect{ tl: Point{ x: 0, y: 0 }, br: Point{ x: 10, y: 10 } };
        \\ printf("tx=%d, ty=%d, bx=%d, by=%d\n", tx, ty, bx, by);
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "tx=0, ty=0, bx=10, by=10\n");
}

test "declarations: nested variant destructuring" {
    const globals =
        \\ Inner :: variant { A(i32) };
        \\ Outer :: variant { Wrap(Inner) };
    ;
    const src =
        \\ Outer.Wrap(Inner.A(val)) := Outer.Wrap(Inner.A(99));
        \\ printf("Nested variant value=%d\n", val);
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Nested variant value=99\n");
}
