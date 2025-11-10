const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "patterns: basic array pattern" {
    const src =
        \\arr := [1, 2, 3]
        \\result := match arr {
        \\  [1, 2, 3] => "Matched [1, 2, 3]",
        \\  _ => "Other",
        \\}
        \\printf("Result: %s\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: Matched [1, 2, 3]\n");
}

test "patterns: array pattern with variable binding" {
    const src =
        \\arr := [10, 20, 30]
        \\match arr {
        \\  [x, y, z] => printf("X: %d, Y: %d, Z: %d\n", x, y, z),
        \\  _ => printf("Other\n"),
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "X: 10, Y: 20, Z: 30\n");
}

test "patterns: array pattern with wildcard" {
    const src =
        \\arr := [100, 200, 300]
        \\match arr {
        \\  [_, y, _] => printf("Y: %d\n", y),
        \\  _ => printf("Other\n"),
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Y: 200\n");
}

test "patterns: array pattern with head and rest" {
    const src =
        \\arr := [1, 2, 3, 4, 5]
        \\match arr {
        \\  [head, ..tail] => printf("Head: %d, Tail length: %d\n", head, tail.len),
        \\  _ => printf("Other\n"),
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Head: 1, Tail length: 4\n");
}

test "patterns: array pattern with multiple heads and rest" {
    const src =
        \\arr := [1, 2, 3, 4, 5]
        \\match arr {
        \\  [first, second, ..rest] => printf("First: %d, Second: %d, Rest length: %d\n", first, second, rest.len),
        \\  _ => printf("Other\n"),
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "First: 1, Second: 2, Rest length: 3\n");
}

