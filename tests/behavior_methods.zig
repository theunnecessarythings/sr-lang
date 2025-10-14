const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "methods: static, value, pointer, and const receivers" {
    const globals =
        \\Point :: struct { x: i32, y: i32 }
        \\Point.origin :: fn() Point { return Point{ x: 0, y: 0 } }
        \\Point.distance :: fn(self: Point) i32 { return self.x + self.y }
        \\Point.translate :: fn(self: *Point, dx: i32, dy: i32) void {
        \\  self.x = self.x + dx
        \\  self.y = self.y + dy
        \\}
        \\Point.sum :: fn(self: *const Point) i32 { return self.x + self.y }
    ;
    const src =
        \\p := Point.origin()
        \\printf("origin=%d,%d\n", p.x, p.y)
        \\p.translate(3, 4)
        \\printf("distance=%d\n", p.distance())
        \\printf("sum=%d\n", p.sum())
        \\ptr := &p
        \\ptr.translate(-1, 2)
        \\printf("final=%d,%d\n", p.x, p.y)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "origin=0,0\ndistance=7\nsum=7\nfinal=2,6\n");
}
