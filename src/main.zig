const std = @import("std");
const compiler = @import("compiler");

pub fn main() !void {
    var args = std.process.args();
    const exec = args.next();

    const filename = args.next() orelse {
        std.debug.print("Usage: {s} <source_file>\n", .{exec.?});
        return;
    };

    var file = try std.fs.cwd().openFile(filename, .{});
    const source = try file.readToEndAlloc(std.heap.page_allocator, (try file.stat()).size);
    defer std.heap.page_allocator.free(source);
    std.debug.print("Compiling {s}...\n", .{filename});
}
