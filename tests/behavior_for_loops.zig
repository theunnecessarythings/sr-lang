const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "control_flow: range-based for loop (exclusive)" {
    const src =
        \\sum := 0
        \\for i in 0..3 { // 0, 1, 2
        \\  sum = sum + i.(i64)
        \\}
        \\printf("Sum: %d\n", sum)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Sum: 3\n");
}

test "control_flow: range-based for loop (inclusive)" {
    const src =
        \\sum := 0
        \\for i in 0..=3 { // 0, 1, 2, 3
        \\  sum = sum + i.(i64)
        \\}
        \\printf("Sum: %d\n", sum)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Sum: 6\n");
}

test "control_flow: iterator-based for loop over array" {
    const src =
        \\arr := [10, 20, 30]
        \\sum := 0
        \\for x in arr {
        \\  sum = sum + x
        \\}
        \\printf("Array sum: %d\n", sum)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Array sum: 60\n");
}

test "control_flow: for loop with break" {
    const src =
        \\sum := 0
        \\for i in 0..10 {
        \\  if i == 5 {
        \\    break
        \\  }
        \\  sum = sum + i.(i64)
        \\}
        \\printf("Sum before break: %d\n", sum)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Sum before break: 10\n"); // 0+1+2+3+4
}

test "control_flow: for loop with continue" {
    const src =
        \\sum := 0
        \\for i in 0..5 {
        \\  if i == 2 {
        \\    continue
        \\  }
        \\  sum = sum + i.(i64)
        \\}
        \\printf("Sum skipping 2: %d\n", sum)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Sum skipping 2: 8\n"); // 0+1+3+4
}

test "control_flow: nested for loops" {
    const src =
        \\count := 0
        \\for i in 0..2 {
        \\  for j in 0..2 {
        \\    count = count + 1
        \\  }
        \\}
        \\printf("Total count: %d\n", count)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Total count: 4\n");
}

