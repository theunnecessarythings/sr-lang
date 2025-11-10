const std = @import("std");
const behavior = @import("behavior.zig"); // Import the behavior.zig file

// Use the functions from behavior.zig
const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "declarations: basic async proc" {
    const globals =
        \\ my_async_proc :: async proc() { printf("Async proc started\n"); };
    ;
    const src =
        \\ my_async_proc().await;
        \\ printf("Async proc finished\n");
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Async proc started\nAsync proc finished\n");
}

test "declarations: basic async fn" {
    const globals =
        \\ my_async_fn :: async fn() i32 { return 100; };
    ;
    const src =
        \\ r := my_async_fn().await;
        \\ printf("Async fn returned 0\n", r);
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Async fn returned 100\n");
}

test "declarations: multiple async calls and await" {
    const globals =
        \\ async_task1 :: async proc() { printf("Task 1\n"); };
        \\ async_task2 :: async proc() { printf("Task 2\n"); };
    ;
    const src =
        \\ async_task1().await;
        \\ async_task2().await;
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Task 1\nTask 2\n");
}
