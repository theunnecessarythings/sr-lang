const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "patterns: match with integer literal" {
    const src =
        \\x := 5
        \\result := match x {
        \\  1 => "One",
        \\  5 => "Five",
        \\  _ => "Other",
        \\}
        \\printf("Result: %s\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: Five\n");
}

test "patterns: match with string literal" {
    if (true) return error.SkipZigTest;
    const src =
        \\s := "world"
        \\result := match s {
        \\  "hello" => "Greeting",
        \\  "world" => "Target",
        \\  _ => "Unknown",
        \\}
        \\printf("Result: %s\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: Target\n");
}

test "patterns: match with boolean literal" {
    const src =
        \\b := true
        \\result := match b {
        \\  true => "It's true",
        \\  false => "It's false",
        \\}
        \\printf("Result: %s\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: It's true\n");
}

test "patterns: match with character literal" {
    const src =
        \\c := 'B'
        \\result := match c {
        \\  'A' => "Char A",
        \\  'B' => "Char B",
        \\  _ => "Other Char",
        \\}
        \\printf("Result: %s\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: Char B\n");
}
