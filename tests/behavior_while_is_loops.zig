const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "control_flow: while is with optional" {
    const globals =
        \\Option :: variant { None, Some(i32) }
    ;
    const src =
        \\maybe_value := Option.Some(42)
        \\result := 0
        \\while is Option.Some(x) := maybe_value {
        \\  result = x
        \\  maybe_value = Option.None // Exit loop
        \\}
        \\printf("While is result=%d\n", result)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "While is result=42\n");
}

test "control_flow: while is with variant and payload" {
    const globals =
        \\Event :: variant { End, Data(string) }
    ;
    const src =
        \\event_stream := Event.Data("first")
        \\while is Event.Data(msg) := event_stream {
        \\  printf("Received: %s\n", msg)
        \\  event_stream = Event.End // Simulate end of stream
        \\}
        \\printf("Stream ended\n")
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Received: first\nStream ended\n");
}

test "control_flow: while is with break" {
    const globals =
        \\Option :: variant { None, Some(i32) }
    ;
    const src =
        \\maybe_value := Option.Some(10)
        \\count : i32 = 0
        \\while is Option.Some(x) := maybe_value {
        \\  count = count + x
        \\  if count > 10 {
        \\    break
        \\  }
        \\  maybe_value = Option.None // Ensure loop terminates
        \\}
        \\printf("Final count: %d\n", count)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Final count: 10\n");
}

