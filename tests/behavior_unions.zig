const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "composite_types: basic union definition and instantiation" {
    const globals =
        \\IntOrFloat :: union { i: i32, f: f32 }
    ;
    const src =
        \\u := IntOrFloat{ i: 123 }
        \\printf("Union as int: %d\n", u.i)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Union as int: 123\n");
}

test "composite_types: switching active union field" {
    const globals =
        \\IntOrFloat :: union { i: i32, f: f64 }
    ;
    const src =
        \\u := IntOrFloat{ i: 123 }
        \\u.f = 456.78
        \\printf("Union as float: %f\n", u.f)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Union as float: 456.780000\n");
}

test "composite_types: union with different field types" {
    const globals =
        \\Value :: union { b: bool, s: string }
    ;
    const src =
        \\v := Value{ b: true }
        \\printf("Union as bool: %b\n", v.b)
        \\v.s = "hello"
        \\printf("Union as string: %s\n", v.s)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Union as bool: 1\nUnion as string: hello\n");
}

