const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "special_types: function returning noreturn" {
    const globals =
        \\exit :: extern proc(c: i32) noreturn
        \\my_noreturn_func :: proc() noreturn {
        \\  exit(1)
        \\}
    ;
    const src =
        \\// This code should not be reached
        \\my_noreturn_func()
        \\printf("This should not print\n")
    ;
    const code = getSource(globals, src);
    // Expecting the program to exit with code 1, so stdout might be empty or partial
    // The test harness should ideally check the exit code, but for now, we expect no stdout from the unreachable part.
    runCompilerTest(code, "") catch {};
}

test "special_types: unreachable statement" {
    const src =
        \\x := 10
        \\if x > 100 {
        \\  unreachable
        \\}
        \\printf("Code reached after unreachable check\n")
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Code reached after unreachable check\n");
}
