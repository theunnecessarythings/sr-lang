const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "methods: static, value, pointer, and const receivers" {
    const globals =
        \\Point :: struct { x: i32, y: i32 }
        \\Point.origin :: fn() Point { return Point{ x: 0, y: 0 } }
        \\Point.distance :: proc(self: Point) i32 { return self.x + self.y }
        \\Point.translate :: proc(self: *Point, dx: i32, dy: i32) void {
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

test "methods: enum value receiver" {
    const globals =
        \\Color :: enum { Red, Blue }
        \\Color.describe :: fn(self: Color) i32 { return 1 }
    ;
    const src =
        \\main :: proc () i32 {
        \\  value := Color.Red.describe()
        \\  printf("%d\n", value)
        \\  return value
        \\ }
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "1\n");
}

test "methods: imported multi-segment access" {
    const import_dir = "out/import_method_chain";
    _ = std.fs.cwd().deleteTree(import_dir) catch {};
    try std.fs.cwd().makePath(import_dir);
    defer std.fs.cwd().deleteTree(import_dir) catch {};

    {
        var file = try std.fs.cwd().createFile("out/import_method_chain/io.sr", .{ .truncate = true });
        defer file.close();
        const io_src =
            \\package io
            \\Vec2 :: struct { x: i32, y: i32 }
            \\Vec2.init :: fn(x: i32, y: i32) Vec2 { return Vec2{ x: x, y: y } }
        ;
        try file.writeAll(io_src);
    }

    const globals =
        \\io :: import "import_method_chain/io.sr"
    ;
    const src =
        \\vec := io.Vec2.init(11, 42)
        \\printf("Vec2=%d,%d\n", vec.x, vec.y)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Vec2=11,42\n");
}
