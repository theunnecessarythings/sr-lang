const std = @import("std");
const behavior = @import("behavior.zig"); // Import the behavior.zig file

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "expressions_operators: simple assignment" {
    const src =
        \\x := 10
        \\y := x + 5
        \\printf("y=%d\n", y)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "y=15\n");
}

test "expressions_operators: add assignment (integer)" {
    const src =
        \\x := 10
        \\x += 5
        \\printf("x=%d\n", x)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=15\n");
}

test "expressions_operators: subtract assignment (float)" {
    const src =
        \\x := 10.5
        \\x -= 2.0
        \\printf("x=%f\n", x)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=8.500000\n");
}

test "expressions_operators: multiply assignment (integer)" {
    const src =
        \\x := 5
        \\x *= 3
        \\printf("x=%d\n", x)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=15\n");
}

test "expressions_operators: divide assignment (float)" {
    const src =
        \\x := 10.0
        \\x /= 2.5
        \\printf("x=%f\n", x)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=4.000000\n");
}

test "expressions_operators: modulo assignment (integer)" {
    const src =
        \\x := 10
        \\x %= 3
        \\printf("x=%d\n", x)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=1\n");
}
