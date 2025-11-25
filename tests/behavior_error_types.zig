const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "error_handling: basic error type definition" {
    const globals =
        \\MyError :: error { NotFound, PermissionDenied }
    ;
    const src =
        \\// Just defining it should be fine
        \\printf("Error type defined\n")
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Error type defined\n");
}

test "error_handling: returning error from procedure" {
    const globals =
        \\MyError :: error { NotFound, PermissionDenied }
        \\might_fail :: proc() MyError!void {
        \\  return MyError.NotFound
        \\}
    ;
    const src =
        \\might_fail() catch |err| {
        \\  if err == MyError.NotFound {
        \\    printf("Caught NotFound\n")
        \\  } else {
        \\    printf("Caught other error\n")
        \\  }
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Caught NotFound\n");
}

test "error_handling: returning error from function" {
    const globals =
        \\MyError :: error { InvalidInput }
        \\parse_int :: fn(s: string) MyError!i32 {
        \\  return MyError.InvalidInput
        \\}
    ;
    const src =
        \\parse_int("abc") catch |err| {
        \\  if err == MyError.InvalidInput {
        \\    printf("Caught InvalidInput\n")
        \\  } else {
        \\    printf("Caught other error\n")
        \\  }
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Caught InvalidInput\n");
}
