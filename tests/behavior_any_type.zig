const std = @import("std");
const behavior = @import("behavior.zig");

// Import functions from behavior.zig
const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "special_types: assign different types to any" {
    const src =
        \\x: any = 10;
        \\printf("Any as int: %d\\n", x);
        \\x = "hello";
        \\printf("Any as string: %s\\n", x);
        \\x = true;
        \\printf("Any as bool: %b\\n", x);
    ;

    const code = getSource("", src);
    try runCompilerTest(code, "Any as int: 10\nAny as string: hello\nAny as bool: true\n");
}

test "special_types: passing any to function" {
    const globals =
        \\print_any :: proc(val: any) {
        \\    printf("Value: %s\\n", val);
        \\};
    ;

    const src =
        \\print_any(123);
        \\print_any("world");
    ;

    const code = getSource(globals, src);
    try runCompilerTest(code, "Value: 123\nValue: world\n");
}

test "special_types: type checking any with typeof" {
    const globals =
        \\process_any :: proc(val: any) {
        \\    match typeof(val) {
        \\        i32 => printf("It's an integer: %d\\n", val),
        \\        string => printf("It's a string: %s\\n", val),
        \\        _ => printf("Unknown type\\n"),
        \\    }
        \\};
    ;

    const src =
        \\process_any(42);
        \\process_any("test");
    ;

    const code = getSource(globals, src);
    try runCompilerTest(code, "It's an integer: 42\nIt's a string: test\n");
}
