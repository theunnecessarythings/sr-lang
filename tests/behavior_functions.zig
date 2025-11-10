const std = @import("std");
const behavior = @import("behavior.zig"); // Import the behavior.zig file

// Use the functions from behavior.zig
const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "declarations: basic function with parameters and return" {
    const globals =
        \\ add :: fn(a: i32, b: i32) i32 { return a + b; }
    ;
    const src =
        \\ r := add(5, 7);
        \\ printf("Result=%d\n", r);
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Result=12\n");
}

test "declarations: function without parameters" {
    const globals =
        \\ get_answer :: fn() i32 { return 42; }
    ;
    const src =
        \\ r := get_answer();
        \\ printf("Answer=%d\n", r);
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Answer=42\n");
}

test "declarations: function with multiple return statements" {
    const globals =
        \\ get_status :: fn(c: i32) string {
        \\   if c == 200 { return "OK"; }
        \\   if c == 404 { return "Not Found"; }
        \\   return "Unknown";
        \\ }
    ;
    const src =
        \\ printf("Status 200=%s, Status 404=%s, Status 500=%s\n", get_status(200), get_status(404), get_status(500));
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Status 200=OK, Status 404=Not Found, Status 500=Unknown\n");
}

test "declarations: recursive function" {
    const globals =
        \\ factorial :: fn(n: i64) i64 {
        \\   if n == 0 { return 1; }
        \\   return n * factorial(n - 1);
        \\ }
    ;
    const src =
        \\ printf("Factorial 5=%d\n", factorial(5));
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Factorial 5=120\n");
}

test "declarations: function with inline attribute" {
    const globals =
        \\ add_inline :: @[inline] fn(a: i32, b: i32) i32 { return a + b; }
    ;
    const src =
        \\ r := add_inline(10, 15);
        \\ printf("Result=%d\n", r);
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Result=25\n");
}
