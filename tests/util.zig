const std = @import("std");
const compiler = @import("compiler");
const lexer = compiler.lexer;
const ArrayList = std.array_list.Managed;

pub fn readFileAlloc(alloc: std.mem.Allocator, path: []const u8) ![]u8 {
    var f = try std.fs.cwd().openFile(path, .{});
    defer f.close();
    return try f.readToEndAlloc(alloc, std.math.maxInt(usize));
}

pub fn writeFile(alloc: std.mem.Allocator, path: []const u8, bytes: []const u8) !void {
    _ = alloc;
    var f = try std.fs.cwd().createFile(path, .{ .truncate = true });
    defer f.close();
    try f.writeAll(bytes);
}

pub fn assertEqSlices(comptime T: type, a: []const T, b: []const T, msg: []const u8) !void {
    if (!std.mem.eql(T, a, b)) {
        std.debug.print("{s}\n--- a ---\n{s}\n--- b ---\n{s}\n", .{ msg, a, b });
        return error.AssertionFailed;
    }
}

pub fn dumpTokens(alloc: std.mem.Allocator, toks: []const lexer.Token) ![]u8 {
    var list = ArrayList(u8).init(alloc);
    var w = list.writer();
    for (toks) |t| try w.print("{s}@[{d},{d}]\n", .{ @tagName(t.kind), t.loc.start, t.loc.end });
    return list.toOwnedSlice();
}

pub fn normalizeNewlines(buf: []u8) void {
    std.mem.replaceScalar(u8, buf, '\r', '\n');
}
