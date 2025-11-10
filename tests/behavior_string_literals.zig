const std = @import("std");
const behavior = @import("behavior.zig"); // Import the behavior.zig file

// Use the functions from behavior.zig
const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "literals: basic string" {
    const src =
        \\s := "Hello"
        \\printf("s=%s\n", s)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "s=Hello\n");
}

test "literals: string with newline escape" {
    const src =
        \\s := "Line1\nLine2"
        \\printf("s=%s\n", s)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "s=Line1\nLine2\n");
}

test "literals: string with tab escape" {
    const src =
        \\s := "Col1\tCol2"
        \\printf("s=%s\n", s)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "s=Col1\tCol2\n");
}

test "literals: string with double quote escape" {
    const src =
        \\s := "He said \"Hello\""
        \\printf("s=%s\n", s)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "s=He said \"Hello\"\n");
}

test "literals: raw string" {
    const src =
        \\s := r"No\nEscapes"
        \\printf("s=%s\n", s)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "s=No\nEscapes\n");
}

test "literals: hashed raw string" {
    const src =
        \\s := r#"Hash \" inside\n"#
        \\printf("s=%s\n", s)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "s=Hash \" inside\n\n");
}
