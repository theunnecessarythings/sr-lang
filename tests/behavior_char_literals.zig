const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "literals: basic character" {
    const src =
        \\c := 'A'
        \\printf("c=%c\n", c)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "c=A\n");
}

test "literals: escaped newline character" {
    const src =
        \\c := '\n'
        \\printf("c=%c\n", c)
    ;
    const code = getSource("", src);
    // Printing a newline character with %c inserts a newline *before* the trailing \n,
    // so the output is two line breaks after "c=".
    try runCompilerTest(code, "c=\n\n");
}

test "literals: escaped single quote character" {
    const src =
        \\c := '\''
        \\printf("c=%c\n", c)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "c='\n");
}

test "literals: escaped backslash character" {
    const src =
        \\c := '\\'
        \\printf("c=%c\n", c)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "c=\\\n");
}
