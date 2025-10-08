const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "composite_types: basic tuple definition" {
    const src =
        \\t := (1, "hello", true)
        \\printf("Tuple: (%d, %s, %b)\n", t.0, t.1, t.2)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Tuple: (1, hello, 1)\n");
}

test "composite_types: accessing tuple elements" {
    const src =
        \\t := (10, 20, 30)
        \\first := t.0
        \\second := t.1
        \\printf("First: %d, Second: %d\n", first, second)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "First: 10, Second: 20\n");
}

test "composite_types: nested tuples" {
    const src =
        \\t := (1, ("nested", 2.5), true)
        \\printf("Nested: %d, %s, %f, %b\n", t.0, t.1.0, t.1.1, t.2)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Nested: 1, nested, 2.500000, 1\n");
}

// test "composite_types: tuple as function argument" {
//     const globals =
//         \\process_tuple :: proc(t: (i32, string)) {
//         \\  printf("Processed: %d, %s\n", t.0, t.1)
//         \\}
//     ;
//     const src =
//         \\process_tuple((100, "world"))
//     ;
//     const code = getSource(globals, src);
//     try runCompilerTest(code, "Processed: 100, world\n");
// }

// test "composite_types: function returning tuple" {
//     const globals =
//         \\create_tuple :: fn() (i32, bool) {
//         \\  return (42, true)
//         \\}
//     ;
//     const src =
//         \\t := create_tuple()
//         \\printf("Returned: %d, %b\n", t.0, t.1)
//     ;
//     const code = getSource(globals, src);
//     try runCompilerTest(code, "Returned: 42, 1\n");
// }
