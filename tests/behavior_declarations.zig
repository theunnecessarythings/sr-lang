const std = @import("std");
const behavior = @import("behavior.zig"); // Import the behavior.zig file

// Use the functions from behavior.zig
const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "declarations: inferred variable (i32)" {
    const src =
        \\ x := 10
        \\ printf("x=%d\n", x)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=10\n");
}

test "declarations: inferred variable (f32)" {
    const src =
        \\ y := 3.14
        \\ printf("y=%f\n", y)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "y=3.140000\n");
}

test "declarations: inferred variable (bool)" {
    const src =
        \\ b := true
        \\ printf("b=%b\n", b)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "b=1\n");
}

test "declarations: inferred variable (string)" {
    const src =
        \\ s := "hello"
        \\ printf("s=%s\n", s)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "s=hello\n");
}

test "declarations: typed variable (i32) with initialization" {
    const src =
        \\ x: i32 = 20
        \\ printf("x=%d\n", x)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=20\n");
}

test "declarations: typed variable (f64) with initialization" {
    const src =
        \\ y: f64 = 2.71
        \\ printf("y=%f\n", y)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "y=2.710000\n");
}

test "declarations: typed variable (bool) with initialization" {
    const src =
        \\ b: bool = false
        \\ printf("b=%b\n", b)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "b=0\n");
}

test "declarations: typed variable (string) with initialization" {
    const src =
        \\ s: string = "world"
        \\ printf("s=%s\n", s)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "s=world\n");
}

test "declarations: constant (i32)" {
    const src =
        \\ MY_CONST :: 100
        \\ printf("MY_CONST=%d\n", MY_CONST)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "MY_CONST=100\n");
}

test "declarations: constant (string)" {
    const src =
        \\ GREETING :: "Hi there"
        \\ printf("GREETING=%s\n", GREETING)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "GREETING=Hi there\n");
}

test "declarations: variable reassignment" {
    const src =
        \\ x := 10
        \\ printf("x_initial=%d\n", x)
        \\ x = 20
        \\ printf("x_reassigned=%d\n", x)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x_initial=10\nx_reassigned=20\n");
}

test "declarations: local scope variable" {
    const src =
        \\ outer_x := 5
        \\ {
        \\   inner_x := 15
        \\   printf("inner_x=%d\n", inner_x)
        \\ }
        \\ printf("outer_x=%d\n", outer_x)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "inner_x=15\nouter_x=5\n");
}

test "declarations: typed variable without initialization (undefined)" {
    const src =
        \\ x: i32 = undefined
        \\ printf("x=%d\n", x)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=0\n");
}
