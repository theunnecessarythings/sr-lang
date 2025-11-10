const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "patterns: match with if guard on literal" {
    const src =
        \\x := 10
        \\result := match x {
        \\  y if y > 5 => "Greater than 5",
        \\  _ => "Not greater than 5",
        \\}
        \\printf("Result: %s\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: Greater than 5\n");
}

test "patterns: match with if guard and variable binding" {
    const src =
        \\x := 15
        \\result := match x {
        \\  y @ (10..20) if y % 2 != 0 => "Odd in range",
        \\  _ => "Other",
        \\}
        \\printf("Result: %s\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Result: Odd in range\n");
}

test "patterns: match with if guard on variant payload" {
    const globals =
        \\User  :: struct { id: i32, name: string }
        \\Event :: variant { Login(User), Logout }
    ;
    const src =
        \\e := Event.Login(User{ id: 101, name: "Bob" })
        \\match e {
        \\  Event.Login(u) if u.id > 100 => printf("High ID login: %s\n", u.name),
        \\  _ => printf("Other event\n"),
        \\}
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "High ID login: Bob\n");
}

