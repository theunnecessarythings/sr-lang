const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "composite_types: basic slice creation" {
    const src =
        \\arr := [1, 2, 3, 4, 5]
        \\slice := arr[1..4] // Elements 2, 3, 4
        \\printf("Slice: %d, %d, %d\n", slice[0], slice[1], slice[2])
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Slice: 2, 3, 4\n");
}

test "composite_types: slice length" {
    const src =
        \\arr := [1, 2, 3, 4, 5]
        \\slice := arr[1..4]
        \\printf("Slice length: %d\n", slice.len)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Slice length: 3\n");
}

test "composite_types: modifying slice elements affects array" {
    const src =
        \\arr := [1, 2, 3, 4, 5]
        \\slice := arr[1..4]
        \\slice[0] = 99 // Modifies arr[1]
        \\printf(
        \\  "Array after slice modification: %d, %d, %d, %d, %d\n",
        \\  arr[0], arr[1], arr[2], arr[3], arr[4]
        \\)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Array after slice modification: 1, 99, 3, 4, 5\n");
}

test "composite_types: slice as function argument" {
    const globals =
        \\process_slice :: proc(s: []i32) {
        \\  printf("Slice elements: %d, %d\n", s[0], s[1])
        \\}
    ;
    const src =
        \\arr := [10, 20, 30, 40]
        \\process_slice(arr[1..3])
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Slice elements: 20, 30\n");
}

test "composite_types: slice of strings scalar indexing" {
    const globals =
        \\aa :: proc(a: []string) {
        \\    printf("arr len %d, %s\n", a.len, a[a.len - 1])
        \\    for str in a {
        \\        printf("%s", str)
        \\    }
        \\}
    ;
    const src =
        \\a := ["hello", "wordl", "where", "are", "you"]
        \\aa(a)
        \\aa(["hello", "world"])
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "arr len 5, you\nhellowordlwhereareyouarr len 2, world\nhelloworld");
}

