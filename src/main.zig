const std = @import("std");
const compiler = @import("compiler");

pub fn main() !void {
    var args = std.process.args();
    const exec = args.next();

    var emit_mlir: bool = false;
    var run_mlir: bool = false;
    var mlir_path: ?[]const u8 = null;
    var filename: ?[]const u8 = null;

    while (args.next()) |arg| {
        if (std.mem.eql(u8, arg, "--emit-mlir")) {
            emit_mlir = true;
            mlir_path = args.next();
        } else if (std.mem.eql(u8, arg, "--run-mlir")) {
            run_mlir = true;
        } else {
            filename = arg;
            break;
        }
    }

    var file_arg: []const u8 = undefined;
    file_arg = filename orelse {
        std.debug.print("Usage: {s} [--emit-mlir <out.mlir>] <source_file>\n", .{exec.?});
        return;
    };

    const allocator = std.heap.page_allocator;

    var file = try std.fs.cwd().openFile(file_arg, .{});
    const source = try file.readToEndAlloc(allocator, (try file.stat()).size);
    const source0 = try allocator.dupeZ(u8, source);
    defer allocator.free(source0);
    defer allocator.free(source);
    std.debug.print("Compiling {s}...\n", .{file_arg});

    // Initialize diagnostics collector and parser
    var diags = compiler.diagnostics.Diagnostics.init(allocator);
    defer diags.deinit();

    var parser = compiler.parser.Parser.init(allocator, source0, &diags);
    var cst_program = try parser.parse();

    // Run checker/desugarer stage
    // Run pipeline: lower (with future desugaring), bind, check, type
    var pl = compiler.pipeline.Pipeline.init(allocator, &diags);
    var result = pl.run(&cst_program) catch |err| {
        // Emit diagnostics after parsing
        var err_buf: [1024]u8 = undefined;
        var err_writer = std.fs.File.stderr().writer(&err_buf);
        try diags.emitStyled(source0, &err_writer.interface, file_arg, true);
        try err_writer.interface.flush();
        return err;
    };

    // Print AST, HIR, and Symbols for visibility
    var buffer: [1024]u8 = undefined;
    var writer = std.fs.File.stdout().writer(&buffer);
    var out = &writer.interface;
    var cst_printer = compiler.cst.CstPrinter.init(out);
    try cst_printer.print(&cst_program);
    var ast_printer = compiler.ast.AstPrinter.init(out);
    if (result.type_info) |ti| {
        ast_printer.withTypes(&ti.arena, &ti.expr_types, &ti.decl_types);
    }
    try ast_printer.print(&result.hir);
    var sym_printer = compiler.symbols.SymPrinter.init(out);
    if (result.binder) |b| {
        var binder_mut = b;
        try sym_printer.printTop(&binder_mut.symtab);
    }
    try out.flush();
    var tir_printer = compiler.tir.Printer.init(out, &result.type_info.?.arena);
    try tir_printer.printModule(&result.module);
    try out.flush();

    // Emit diagnostics after parsing
    var err_buf: [1024]u8 = undefined;
    var err_writer = std.fs.File.stderr().writer(&err_buf);
    try diags.emitStyled(source0, &err_writer.interface, file_arg, true);
    try err_writer.interface.flush();

    compiler.compile.run();
}
