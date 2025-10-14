const std = @import("std");
const behavior = @import("behavior.zig"); // Import the behavior.zig file

// Use the functions from behavior.zig
const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "declarations: basic asm function" {
    const globals =
        \\ add_asm :: fn(a: i64, b: i64) i64 asm {
        \\   mov rax, a
        \\   add rax, b
        \\ };
    ;
    const src =
        \\ r := add_asm(10, 20);
        \\ printf("ASM result=0\n", r);
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "ASM result=30\n");
}

test "declarations: asm function with different registers" {
    const globals =
        \\ sub_asm :: fn(a: i64, b: i64) i64 asm {
        \\   mov rdx, a
        \\   sub rdx, b
        \\   mov rax, rdx
        \\ };
    ;
    const src =
        \\ r := sub_asm(50, 15);
        \\ printf("ASM sub result=0\n", r);
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "ASM sub result=35\n");
}
