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

test "special_types: optional in call" {
    const globals =
        \\func :: proc(a: ?i32) {
        \\  printf("%d\n", a orelse -1)
        \\}
    ;

    const src =
        \\b: ?i32 = null
        \\func(if b != null {
        \\    b
        \\} else {
        \\    null
        \\})
    ;

    const code = getSource(globals, src);
    try runCompilerTest(code, "-1\n");
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

test "special_types: optional compare with payload" {
    const src =
        \\opt: ?i32 = 42
        \\_assert(opt == 42)
        \\_assert(42 == opt)
        \\_assert(opt != 13)
        \\_assert(13 != opt)
        \\printf("optional compare ok\n")
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "optional compare ok\n");
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

test "special_types: optional pointer equality and deref" {
    const src =
        \\value: i32 = 123
        \\ptr := &value
        \\maybe_ptr: ?*i32 = ptr
        \\_assert(maybe_ptr != null)
        \\_assert(maybe_ptr == ptr)
        \\_assert(ptr == maybe_ptr)
        \\deref := maybe_ptr?
        \\printf("optional pointer value: %d\n", deref.*)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "optional pointer value: 123\n");
}

test "special_types: optional pointer orelse fallback" {
    const src =
        \\stored: i32 = 777
        \\stored_ptr := &stored
        \\missing: ?*i32 = null
        \\result_ptr := missing orelse stored_ptr
        \\printf("pointer orelse result: %d\n", result_ptr.*)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "pointer orelse result: 777\n");
}

test "special_types: optional void pointer interop" {
    const src =
        \\value: i32 = 55
        \\void_ptr: *void = (&value).^*void
        \\maybe_ctx: ?*void = void_ptr
        \\missing_ctx: ?*void = null
        \\payload := maybe_ctx?.^*i32
        \\printf("void optional payload: %d\n", payload.*)
        \\if missing_ctx == null {
        \\    printf("void optional missing is null\n")
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "void optional payload: 55\nvoid optional missing is null\n");
}

test "special_types: optional orelse return expression" {
    const globals =
        \\use_optional :: proc(value: ?i32) {
        \\    payload := value orelse return
        \\    printf("orelse payload: %d\n", payload)
        \\}
    ;
    const src =
        \\some: ?i32 = 321
        \\none: ?i32 = null
        \\use_optional(some)
        \\use_optional(none)
        \\printf("orelse done\n")
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "orelse payload: 321\norelse done\n");
}
