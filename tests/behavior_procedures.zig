const std = @import("std");
const behavior = @import("behavior.zig"); // Import the behavior.zig file

// Use the functions from behavior.zig
const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "declarations: basic procedure with parameters" {
    const globals =
        \\ print_sum :: proc(a: i32, b: i32) { printf("Sum=%d\n", a + b); }
    ;
    const src =
        \\ print_sum(10, 20);
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Sum=30\n");
}

test "declarations: procedure without parameters" {
    const globals =
        \\ print_hello :: proc() { printf("Hello\n"); }
    ;
    const src =
        \\ print_hello();
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Hello\n");
}

test "declarations: procedure with cold attribute" {
    const globals =
        \\ my_cold_proc :: @[cold] proc() { printf("Cold proc executed\n"); }
    ;
    const src =
        \\ my_cold_proc();
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Cold proc executed\n");
}
