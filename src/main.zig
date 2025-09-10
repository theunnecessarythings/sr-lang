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
    var cst_program = try parser.parse();

    // Run checker/desugarer stage
    // Run pipeline: lower (with future desugaring), bind, check, type
    var pl = compiler.pipeline.Pipeline.init(allocator, &diags);
    var result = try pl.run(&cst_program);

    // Print AST, HIR, and Symbols for visibility
    var buffer: [1024]u8 = undefined;
    var writer = std.fs.File.stdout().writer(&buffer);
    var out = &writer.interface;
    var cst_printer = compiler.cst.CstPrinter.init(out);
    try cst_printer.print(&cst_program);
    var ast_printer = compiler.ast.AstPrinter.init(out);
    try ast_printer.print(&result.hir);
    var sym_printer = compiler.symbols.SymPrinter.init(out);
    if (result.binder) |b| {
        var binder_mut = b;
        try sym_printer.printTop(&binder_mut.symtab);
    }
    try out.flush();

    // Emit diagnostics after parsing
    var err_buf: [1024]u8 = undefined;
    var err_writer = std.fs.File.stderr().writer(&err_buf);
    try diags.emitStyled(source0, &err_writer.interface, filename, true);
    try err_writer.interface.flush();
}
