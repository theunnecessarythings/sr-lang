const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "patterns: or-pattern with literals" {
    const src =
        \\x := 2
        \\result := match x {
        \\  1 | 2 => "One or Two",
        \\  3 => "Three",
        \\  _ => "Other",
        \\}
        \\printf("Result: %s\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: One or Two\n");
}

test "patterns: or-pattern with ranges" {
    const src =
        \\x := 7
        \\result := match x {
        \\  (0..=3) | (7..=10) => "In range",
        \\  _ => "Out of range",
        \\}
        \\printf("Result: %s\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: In range\n");
}

test "patterns: or-pattern with enum variants" {
    const globals =
        \\Status :: enum { Active, Inactive, Pending }
    ;
    const src =
        \\s := Status.Inactive
        \\result := match s {
        \\  Status.Active | Status.Pending => "Not Inactive",
        \\  Status.Inactive => "Inactive",
        \\}
        \\printf("Result: %s\n", result)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Result: Inactive\n");
}
