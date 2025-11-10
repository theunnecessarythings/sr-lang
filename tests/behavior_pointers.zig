const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "special_types: dereference operator" {
    const src =
        \\x := 10
        \\p := &x
        \\val := p.*
        \\printf("Dereferenced value: %d\n", val)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Dereferenced value: 10\n");
}

test "special_types: mutable pointer modification" {
    const globals =
        \\modify_int :: proc(ptr: *i32) {
        \\  ptr.* = 20
        \\}
    ;
    const src =
        \\x := 10
        \\modify_int(&x)
        \\printf("Modified x: %d\n", x)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Modified x: 20\n");
}

test "special_types: auto-dereferencing for field access" {
    const globals =
        \\Point :: struct { x: i32, y: i32 }
    ;
    const src =
        \\p_val := Point{ x: 10, y: 20 }
        \\p_ptr := &p_val
        \\printf("Accessed x via pointer: %d\n", p_ptr.x)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Accessed x via pointer: 10\n");
}
