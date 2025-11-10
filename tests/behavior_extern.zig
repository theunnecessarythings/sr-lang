const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

const alloc = std.testing.allocator;

test "declarations: basic extern proc" {
    const src =
        \\ printf("Extern proc called\n");
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Extern proc called\n");
}

test "declarations: basic extern fn" {
    behavior.link_lib = "out/test.so";
    defer behavior.link_lib = "-lm";
    const c_src =
        \\ int my_extern_fn(int a, int b) {
        \\   return a + b;
        \\ }
    ;
    try std.fs.cwd().writeFile(.{ .data = c_src, .sub_path = "out/test.c" });
    const compile_result = try std.process.Child.run(.{
        .allocator = alloc,
        .argv = &.{ "gcc", "-shared", "-o", "out/test.so", "out/test.c" },
        .max_output_bytes = 16 * 1024 * 1024,
    });
    defer alloc.free(compile_result.stdout);
    defer alloc.free(compile_result.stderr);

    const globals =
        \\ my_extern_fn :: extern proc(a: i32, b: i32) i32
    ;
    const src =
        \\ r := my_extern_fn(5, 7)
        \\ printf("Extern fn returned %d\n", r)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Extern fn returned 12\n");
}

test "declarations: extern fn with pointer type" {
    behavior.link_lib = "out/test.so";
    defer behavior.link_lib = "-lm";
    const c_src =
        \\ void extern_modify_int(int *a) {
        \\   *a = 10;
        \\ }
    ;
    try std.fs.cwd().writeFile(.{ .data = c_src, .sub_path = "out/test.c" });
    const compile_result = try std.process.Child.run(.{
        .allocator = alloc,
        .argv = &.{ "gcc", "-shared", "-o", "out/test.so", "out/test.c" },
        .max_output_bytes = 16 * 1024 * 1024,
    });
    defer alloc.free(compile_result.stdout);
    defer alloc.free(compile_result.stderr);

    const globals =
        \\ extern_modify_int :: extern proc(ptr: *i32);
    ;
    const src =
        \\ x := 10;
        \\ extern_modify_int(&x);
        \\ printf("Modified value=%d\n", x);
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Modified value=10\n");
}
