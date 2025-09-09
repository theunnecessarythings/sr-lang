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

    // Initialize diagnostics collector and parser
    var diags = compiler.diagnostics.Diagnostics.init(allocator);
    defer diags.deinit();

    var parser = compiler.parser.Parser.init(allocator, source0, &diags);
    const ast = try parser.parse();

    var buffer: [1024]u8 = undefined;
    var writer = std.fs.File.stdout().writer(&buffer);
    var out = &writer.interface;
    var printer = compiler.ast.AstPrinter.init(out);
    try printer.print(&ast);
    try out.flush();

    // Emit diagnostics after parsing
    var err_buf: [1024]u8 = undefined;
    var err_writer = std.fs.File.stderr().writer(&err_buf);
    try diags.emitStyled(source0, &err_writer.interface, filename, true);
    try err_writer.interface.flush();
}
