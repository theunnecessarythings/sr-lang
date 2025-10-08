const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "patterns: basic tuple pattern" {
    const src =
        \\t := (1, 2)
        \\result := match t {
        \\  (1, 2) => "Matched (1, 2)",
        \\  _ => "Other",
        \\}
        \\printf("Result: %s\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: Matched (1, 2)\n");
}

test "patterns: tuple pattern with variable binding" {
    const src =
        \\t := (10, "hello")
        \\match t {
        \\  (num, text) => printf("Num: %d, Text: %s\n", num, text),
        \\  _ => printf("Other\n"),
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Num: 10, Text: hello\n");
}

test "patterns: tuple pattern with wildcard" {
    const src =
        \\t := (100, 200, 300)
        \\match t {
        \\  (x, _, z) => printf("X: %d, Z: %d\n", x, z),
        \\  _ => printf("Other\n"),
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "X: 100, Z: 300\n");
}

test "patterns: nested tuple patterns" {
    const src =
        \\t := (1, ("nested", true))
        \\match t {
        \\  (x, (s, b)) => printf("X: %d, S: %s, B: %b\n", x, s, b),
        \\  _ => printf("Other\n"),
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "X: 1, S: nested, B: 1\n");
}
