const std = @import("std");
const behavior = @import("behavior.zig"); // Import the behavior.zig file

// Use the functions from behavior.zig
const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "patterns: basic variable binding" {
    const src =
        \\x := 10
        \\result := match x {
        \\  y @ 10 => printf("Matched 10, bound to y=%d\n", y),
        \\  _ => printf("Other\n"),
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Matched 10, bound to y=10\n");
}

test "patterns: variable binding with sub-pattern (optional)" {
    const globals =
        \\Option :: variant { None, Some(i32) }
    ;
    const src =
        \\opt_val := Option.Some(42)
        \\match opt_val {
        \\  p @ Option.Some(val) => printf("Bound pattern: %d, Value: %d\n", p.0, val),
        \\  _ => printf("None\n"),
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Bound pattern: 1, Value: 42\n");
}

test "patterns: variable binding in if guard" {
    const src =
        \\x := 15
        \\result := match x {
        \\  y @ (10..20) if y % 2 != 0 => "Odd in range",
        \\  _ => "Other",
        \\}
        \\printf("Result: %s\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: Odd in range\n");
}
