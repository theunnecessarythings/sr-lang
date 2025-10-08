const std = @import("std");
const behavior = @import("behavior.zig"); // Import the behavior.zig file

// Use the functions from behavior.zig
const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "literals: true boolean" {
    const src =
        \\ x := true;
        \\ printf("x=%b\n", x);
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=1\n");
}

test "literals: false boolean" {
    const src =
        \\ x := false;
        \\ printf("x=%b\n", x);
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=0\n");
}

test "literals: boolean in conditional" {
    const src =
        \\ if true { printf("True branch\n"); } else { printf("False branch\n"); }
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "True branch\n");
}

test "literals: boolean expression (and)" {
    const src =
        \\ x := true and false;
        \\ printf("x=%b\n", x);
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=0\n");
}

test "literals: boolean expression (not)" {
    const src =
        \\ x := !true;
        \\ printf("x=%b\n", x);
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=0\n");
}
