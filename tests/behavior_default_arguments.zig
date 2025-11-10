const std = @import("std");
const behavior = @import("behavior.zig");

// Import functions from behavior.zig
const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "functions_closures: function with one default argument" {
    const globals =
        \\greet :: proc(name: string, greeting: string = "Hello") {
        \\    printf("%s, %s!\n", greeting, name);
        \\};
    ;

    const src =
        \\greet("Alice");
        \\greet("Bob", "Hi");
    ;

    const code = getSource(globals, src);
    try runCompilerTest(code, "Hello, Alice!\nHi, Bob!\n");
}

test "functions_closures: function with multiple default arguments" {
    const globals =
        \\configure :: proc(name: string, id: i32 = 0, active: bool = true) {
        \\    printf("Name=%s, ID=%d, Active=%d\n", name, id, active);
        \\};
    ;

    const src =
        \\configure("UserA");
        \\configure("UserB", 10);
        \\configure("UserC", 20, false);
    ;

    const code = getSource(globals, src);
    try runCompilerTest(code, "Name=UserA, ID=0, Active=1\nName=UserB, ID=10, Active=1\nName=UserC, ID=20, Active=0\n");
}
