const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "composite_types: basic struct definition and instantiation" {
    const globals =
        \\Point :: struct { x: i32, y: i32 }
    ;
    const src =
        \\p := Point{ x: 10, y: 20 }
        \\printf("Point: (%d, %d)\n", p.x, p.y)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Point: (10, 20)\n");
}

test "composite_types: struct default values" {
    const globals = "Point :: struct { x: i32 = 4, y: i32 = 2 }";
    const src =
        \\ p := Point{}
        \\ printf("Point: (%d, %d)\n", p.x, p.y)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Point: (4, 2)\n");
}

test "composite_types: struct update syntax" {
    if (true) return error.SkipZigTest;
    const globals =
        \\Point :: struct { x: i32, y: i32 }
    ;
    const src =
        \\p1 := Point{ x: 10, y: 20 }
        \\p2 := Point{ x: 5, ..p1 }
        \\printf("P2: (%d, %d)\n", p2.x, p2.y)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "P2: (5, 20)\n");
}

test "composite_types: nested structs" {
    const globals =
        \\Point :: struct { x: i32, y: i32 }
        \\Rect  :: struct { tl: Point, br: Point }
    ;
    const src =
        \\r := Rect{ tl: Point{ x: 0, y: 0 }, br: Point{ x: 10, y: 10 } }
        \\printf("Rect: (%d, %d) to (%d, %d)\n", r.tl.x, r.tl.y, r.br.x, r.br.y)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Rect: (0, 0) to (10, 10)\n");
}

test "composite_types: struct with mixed field types" {
    const globals =
        \\User :: struct { id: i32, name: string, active: bool }
    ;
    const src =
        \\u := User{ id: 1, name: "Alice", active: true }
        \\printf("User: %d, %s, %b\n", u.id, u.name, u.active)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "User: 1, Alice, 1\n");
}
