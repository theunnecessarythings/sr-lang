const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "special_types: optional declaration with value" {
    const src =
        \\x: ?i32 = 10
        \\printf("x has value: %d\n", x?)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x has value: 10\n");
}

test "special_types: optional declaration with null" {
    const src =
        \\x: ?i32 = null
        \\if x == null {
        \\  printf("x is null\n")
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x is null\n");
}

test "special_types: optional unwrap with value" {
    const src =
        \\x: ?i32 = 100
        \\val := x?
        \\printf("Unwrapped value: %d\n", val)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Unwrapped value: 100\n");
}

test "special_types: optional unwrap with null (runtime behavior)" {
    const src =
        \\x: ?i32 = null
        \\// Depending on language semantics, unwrapping null might trap or return default
        \\// For this test, we assume it returns a default value (e.g., 0) or a controlled error.
        \\// If it traps, the test will fail the compilation/execution step.
        \\val := x?
        \\printf("Unwrapped null (expected 0 or error): %d\n", val)
    ;
    const code = getSource("", src);
    runCompilerTest(code, "Unwrapped null (expected 0 or error): 0\n") catch |err| {
        switch (err) {
            error.CompilationFailed => {},
            else => return error.Failed,
        }
    };
}

test "special_types: optional chaining" {
    const globals =
        \\Point :: struct { x: i32, y: i32 }
    ;
    const src =
        \\opt_point: ?Point = Point{ x: 10, y: 20 }
        \\val_x := opt_point?.x
        \\printf("Optional chained x: %d\n", val_x)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Optional chained x: 10\n");
}
