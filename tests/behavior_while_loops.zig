const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "control_flow: basic while loop" {
    const src =
        \\i := 0
        \\while i < 3 {
        \\  printf("Loop iteration: %d\n", i)
        \\  i = i + 1
        \\}
        \\printf("Loop finished\n")
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Loop iteration: 0\nLoop iteration: 1\nLoop iteration: 2\nLoop finished\n");
}

test "control_flow: while loop with break" {
    const src =
        \\i := 0
        \\while true {
        \\  if i == 2 {
        \\    break
        \\  }
        \\  printf("Loop iteration: %d\n", i)
        \\  i = i + 1
        \\}
        \\printf("Loop finished\n")
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Loop iteration: 0\nLoop iteration: 1\nLoop finished\n");
}

test "control_flow: while loop with continue" {
    const src =
        \\i := 0
        \\count := 0
        \\while i < 5 {
        \\  i = i + 1
        \\  if i == 3 {
        \\    continue
        \\  }
        \\  printf("Processing: %d\n", i)
        \\  count = count + 1
        \\}
        \\printf("Processed count: %d\n", count)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Processing: 1\nProcessing: 2\nProcessing: 4\nProcessing: 5\nProcessed count: 4\n");
}

test "control_flow: nested while loops" {
    const src =
        \\i := 0
        \\j := 0
        \\while i < 2 {
        \\  j = 0
        \\  while j < 2 {
        \\    printf("i=%d, j=%d\n", i, j)
        \\    j = j + 1
        \\  }
        \\  i = i + 1
        \\}
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "i=0, j=0\ni=0, j=1\ni=1, j=0\ni=1, j=1\n");
}
