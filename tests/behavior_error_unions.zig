const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "error_handling: basic error union return (success)" {
    const globals =
        \\MyError :: error { Failed }
        \\might_succeed :: fn() MyError!i32 {
        \\  return 100
        \\}
    ;
    const src =
        \\r := might_succeed() catch 0
        \\printf("Result: %d\n", r)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Result: 100\n");
}

test "error_handling: basic error union return (error)" {
    const globals =
        \\MyError :: error { Failed }
        \\might_fail :: fn() MyError!i32 {
        \\  return MyError.Failed
        \\}
    ;
    const src =
        \\r := might_fail() catch 0
        \\printf("Result: %d\n", r)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Result: 0\n");
}

test "error_handling: error propagation (!) operator" {
    const globals =
        \\MyError :: error { InnerError }
        \\inner_func :: fn() MyError!i32 {
        \\  return MyError.InnerError
        \\}
        \\outer_func :: fn() MyError!i32 {
        \\  return inner_func()!
        \\}
    ;
    const src =
        \\outer_func() catch |err| {
        \\  if err == MyError.InnerError {
        \\    printf("Propagated error caught\n")
        \\  } else {
        \\    printf("Other error caught\n")
        \\  }
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Propagated error caught\n");
}

test "error_handling: expression" {
    const globals =
        \\MyError :: error { NotFound }
        \\get_value :: fn(found: bool) MyError!i32 {
        \\  if found {
        \\    return 50
        \\  } else {
        \\    return MyError.NotFound
        \\  }
        \\}
    ;
    const src =
        \\r1 := get_value(true) catch 0
        \\r2 := get_value(false) catch 0
        \\printf("Orelse results: %d, %d\n", r1, r2)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Orelse results: 50, 0\n");
}

test "error_handling: catch expression with error binding" {
    const globals =
        \\MyError :: error { SpecificError, OtherError }
        \\do_something :: fn(fail: bool) MyError!i32 {
        \\  if fail {
        \\    return MyError.SpecificError
        \\  } else {
        \\    return 10
        \\  }
        \\}
    ;
    const src =
        \\r := do_something(true) catch |err| {
        \\  if err == MyError.SpecificError {
        \\    printf("Caught specific error\n")
        \\    -1
        \\  } else {
        \\    printf("Caught other error\n")
        \\    -2
        \\  }
        \\}
        \\printf("Final result: %d\n", r)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Caught specific error\nFinal result: -1\n");
}
