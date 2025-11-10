const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "expressions_operators: struct field access" {
    const globals =
        \\Point :: struct { x: i32, y: i32 }
    ;
    const src =
        \\p := Point{ x: 10, y: 20 }
        \\printf("Point x: %d\n", p.x)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Point x: 10\n");
}

test "expressions_operators: nested struct field access" {
    const globals =
        \\Point :: struct { x: i32, y: i32 }
        \\Rect  :: struct { tl: Point, br: Point }
    ;
    const src =
        \\r := Rect{ tl: Point{ x: 0, y: 0 }, br: Point{ x: 10, y: 10 } }
        \\printf("Rect tl.x: %d\n", r.tl.x)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Rect tl.x: 0\n");
}

test "expressions_operators: pointer struct field access" {
    const globals =
        \\Point :: struct { x: i32, y: i32 }
    ;
    const src =
        \\p_val := Point{ x: 10, y: 20 }
        \\p_ptr := &p_val
        \\printf("Pointer x: %d\n", p_ptr.x)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Pointer x: 10\n");
}

test "expressions_operators: array element access" {
    const src =
        \\arr := [10, 20, 30]
        \\printf("Array[1]: %d\n", arr[1])
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Array[1]: 20\n");
}

test "expressions_operators: nested array element access" {
    const src =
        \\matrix := [[1, 2], [3, 4]]
        \\printf("Matrix[0][1]: %d\n", matrix[0][1])
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Matrix[0][1]: 2\n");
}

test "expressions_operators: tuple element access" {
    const src =
        \\t := (100, "hello")
        \\printf("Tuple.0: %d\n", t.0)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Tuple.0: 100\n");
}

test "expressions_operators: nested tuple element access" {
    const src =
        \\t := (1, ("nested", 2.5))
        \\printf("Nested tuple.1.0: %s\n", t.1.0)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Nested tuple.1.0: nested\n");
}
