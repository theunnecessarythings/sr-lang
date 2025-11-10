const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "control_flow: basic if statement (true)" {
    const src =
        \\if true {
        \\  printf("If true\n")
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "If true\n");
}

test "control_flow: basic if statement (false)" {
    const src =
        \\if false {
        \\  printf("If false\n")
        \\}
        \\printf("After if false\n")
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "After if false\n");
}

test "control_flow: if-else statement (true branch)" {
    const src =
        \\if 10 > 5 {
        \\  printf("Greater\n")
        \\} else {
        \\  printf("Not greater\n")
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Greater\n");
}

test "control_flow: if-else statement (false branch)" {
    const src =
        \\if 5 > 10 {
        \\  printf("Greater\n")
        \\} else {
        \\  printf("Not greater\n")
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Not greater\n");
}

test "control_flow: if-else if-else chain" {
    const src =
        \\x := 10
        \\if x == 5 {
        \\  printf("Five\n")
        \\} else if x == 10 {
        \\  printf("Ten\n")
        \\} else {
        \\  printf("Other\n")
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Ten\n");
}

test "control_flow: if expression" {
    const src =
        \\x := 10
        \\result := if x > 5 {
        \\  100
        \\} else {
        \\  200
        \\}
        \\printf("Result: %d\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: 100\n");
}

test "control_flow: nested if-else" {
    const src =
        \\x := 10
        \\y := 20
        \\if x == 10 {
        \\  if y == 20 {
        \\    printf("Nested true\n")
        \\  } else {
        \\    printf("Nested false\n")
        \\  }
        \\} else {
        \\  printf("Outer false\n")
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Nested true\n");
}
