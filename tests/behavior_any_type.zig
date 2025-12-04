const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "special_types: passing any to function" {
    const globals =
        \\calc :: proc(a: any, b: any) {
        \\    result := (a + b) * 100
        \\    printf("Result: %d\n", result.(i64))
        \\}
    ;

    const src =
        \\calc(123, 345)
        \\calc(3.1415, 2.71828)
    ;

    const code = getSource(globals, src);
    try runCompilerTest(code, "Result: 46800\nResult: 585\n");
}

test "special_types: type checking any with typeof" {
    const globals =
        \\process_any :: proc(val: any) {
        \\    match typeof(val) {
        \\        i64 => printf("It's an integer: %d\n", val),
        \\        string => printf("It's a string: %s\n", val),
        \\        _ => printf("Unknown type\n"),
        \\    }
        \\}
    ;

    const src =
        \\process_any(42)
        \\process_any("test")
    ;

    const code = getSource(globals, src);
    try runCompilerTest(code, "It's an integer: 42\nIt's a string: test\n");
}
