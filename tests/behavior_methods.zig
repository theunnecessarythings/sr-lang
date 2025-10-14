const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "methods: value and pointer receivers" {
    const globals =
        \\Point :: struct { x: i32, y: i32 }
        \\Point.distance :: fn(self: Point) i32 { return self.x + self.y }
        \\Point.translate :: fn(self: *Point, dx: i32, dy: i32) void {
        \\  self.x = self.x + dx
        \\  self.y = self.y + dy
        \\}
    ;
    const src =
        \\p := Point{ x: 3, y: 4 }
        \\printf("distance=%d\\n", p.distance())
        \\ptr := &p
        \\ptr.translate(2, -1)
        \\printf("point=%d,%d\\n", p.x, p.y)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "distance=7\npoint=5,3\n");
}
