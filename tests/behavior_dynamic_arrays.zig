const std = @import("std");
const behavior = @import("behavior.zig");

// Import functions from behavior.zig
const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "composite_types: basic dynamic array creation" {
    const src =
        \\numbers: [dyn]i32 = [];
        \\printf("Initial length: %d\n", numbers.len);
    ;

    const code = getSource("", src);
    try runCompilerTest(code, "Initial length: 0\n");
}

test "composite_types: append elements to dynamic array" {
    const src =
        \\numbers: [dyn]i32 = [];
        \\numbers.append(10);
        \\numbers.append(20);
        \\printf("Length after append: %d\n", numbers.len);
        \\printf("First element: %d\n", numbers[0]);
    ;

    const code = getSource("", src);
    try runCompilerTest(code, "Length after append: 2\nFirst element: 10\n");
}

test "composite_types: dynamic array capacity" {
    const src =
        \\numbers: [dyn]i32 = [];
        \\numbers.append(1);
        \\numbers.append(2);
        \\numbers.append(3);
        \\// Capacity may vary by implementation but should always be >= len
        \\printf("Capacity >= Length: %b\n", numbers.capacity >= numbers.len);
    ;

    const code = getSource("", src);
    try runCompilerTest(code, "Capacity >= Length: 1\n");
}

test "composite_types: iterate dynamic array" {
    const src =
        \\numbers: [dyn]i32 = [];
        \\numbers.append(1);
        \\numbers.append(2);
        \\sum : i32 = 0;
        \\for n in numbers {
        \\    sum = sum + n;
        \\}
        \\printf("Sum of elements: %d\n", sum);
    ;

    const code = getSource("", src);
    try runCompilerTest(code, "Sum of elements: 3\n");
}
