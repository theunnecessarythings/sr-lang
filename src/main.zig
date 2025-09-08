const std = @import("std");
const compiler = @import("compiler");

pub fn main() !void {
    var args = std.process.args();
    const exec = args.next();

    const filename = args.next() orelse {
        std.debug.print("Usage: {s} <source_file>\n", .{exec.?});
        return;
    };

    const allocator = std.heap.page_allocator;

    var file = try std.fs.cwd().openFile(filename, .{});
    const source = try file.readToEndAlloc(allocator, (try file.stat()).size);
    const source0 = try allocator.dupeZ(u8, source);
    defer allocator.free(source0);
    defer allocator.free(source);
    std.debug.print("Compiling {s}...\n", .{filename});

    var lexer = compiler.lexer.Tokenizer.init(source0);
    while (true) {
        const token = lexer.next();
        std.debug.print(
            "{any} -> `{s}`\n",
            .{ token.tag, source0[token.loc.start..token.loc.end] },
        );
        if (token.tag == .eof) break;
    }

    var parser = compiler.parser.Parser.init(allocator, source0);
    const ast = try parser.parse();

    var buffer: [1024]u8 = undefined;
    var writer = std.fs.File.stdout().writer(&buffer);
    var out = &writer.interface;
    var printer = compiler.ast.AstPrinter.init(out);
    try printer.print(&ast);
    try out.flush();
}
