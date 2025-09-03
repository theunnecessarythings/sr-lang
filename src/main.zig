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

    var lexer = compiler.lexer.Tokenizer.init(try std.heap.page_allocator.dupeZ(u8, source));
    while (true) {
        const token = lexer.next();
        std.debug.print("{s}({}, {})\n", .{ @tagName(token.tag), token.loc.start, token.loc.end });
        if (token.tag == .eof) break;
    }
}
