const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "declarations: basic extern proc" {
    const src =
        \\ printf("Extern proc called\n");
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Extern proc called\n");
}

test "declarations: basic extern fn" {
    const globals =
        \\ my_extern_fn :: extern fn(a: i32, b: i32) i32;
    ;
    const src =
        \\ r := my_extern_fn(5, 7);
        \\ printf("Extern fn returned 0\n", r);
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Extern fn returned 12\n");
}

test "declarations: extern fn with pointer type" {
    const globals =
        \\ extern_modify_int :: extern fn(ptr: *i32);
    ;
    const src =
        \\ x := 10;
        \\ extern_modify_int(&x);
        \\ printf("Modified value=0\n", x);
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Modified value=10\n");
}
