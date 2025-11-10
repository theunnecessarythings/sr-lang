const std = @import("std");
const behavior = @import("behavior.zig");

// Import functions from behavior.zig
const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "composite_types: basic map creation" {
    const src =
        \\m: [string:i32] = ["one": 1, "two": 2];
        \\printf("Map size: %d\n", m.len);
    ;

    const code = getSource("", src);
    try runCompilerTest(code, "Map size: 2\n");
}

test "composite_types: accessing map elements" {
    const src =
        \\m: [string:i32] = ["one": 1, "two": 2];
        \\val := m["one"];
        \\printf("Value of 'one': %d\n", val);
    ;

    const code = getSource("", src);
    try runCompilerTest(code, "Value of 'one': 1\n");
}

test "composite_types: inserting and updating map elements" {
    const src =
        \\m: [string:i32] = ["one": 1];
        \\m["two"] = 2; // Insert
        \\m["one"] = 11; // Update
        \\printf("Map: one=%d, two=%d\n", m["one"], m["two"]);
    ;

    const code = getSource("", src);
    try runCompilerTest(code, "Map: one=11, two=2\n");
}

test "composite_types: removing map elements" {
    const src =
        \\m: [string:i32] = ["one": 1, "two": 2];
        \\m.remove("one");
        \\printf("Map size after remove: %d\n", m.len);
    ;

    const code = getSource("", src);
    try runCompilerTest(code, "Map size after remove: 1\n");
}
