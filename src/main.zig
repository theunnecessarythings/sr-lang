const std = @import("std");
const compiler = @import("compiler");

const Colors = struct {
    pub const reset = "\x1b[0m";
    pub const bold = "\x1b[1m";
    pub const red = "\x1b[31m";
    pub const yellow = "\x1b[33m";
    pub const blue = "\x1b[34m";
    pub const cyan = "\x1b[36m";
    pub const green = "\x1b[32m";
};

const CliArgs = struct {
    subcommand: Subcommand,
    filename: ?[]const u8 = null,
    output_path: ?[]const u8 = null,
    emit_mlir: bool = false,
    run_mlir: bool = false,
    no_color: bool = false,
    verbose: bool = false,

    const Subcommand = enum {
        compile,
        run,
        check,
        ast,
        tir,
        help,
        unknown,
    };
};

// Function to print usage information
fn printUsage(writer: anytype, exec_name: []const u8) !void {
    try writer.print(
        "{s}Usage:{s} {s} <command> [options] <file>\n" ++
            "\n" ++
            "{s}Commands:{s}\n" ++
            "  {s}compile{s} <file>      Compile a source file to an executable.\n" ++
            "  {s}run{s} <file>         Compile and immediately run a source file.\n" ++
            "  {s}check{s} <file>        Parse and perform semantic checks on a source file.\n" ++
            "  {s}ast{s} <file>         Print the Abstract Syntax Tree (AST) of a source file.\n" ++
            "  {s}tir{s} <file>         Print the Typed Intermediate Representation (TIR) of a source file.\n" ++
            "  {s}help{s}               Display this help message.\n" ++
            "\n" ++
            "{s}Options:{s}\n" ++
            "  {s}--output{s} <path>    Specify the output path for compiled executables.\n" ++
            "  {s}--emit-mlir{s}        Emit MLIR IR to stdout during compilation.\n" ++
            "  {s}--run-mlir{s}         Run MLIR JIT after compilation (for testing).\n" ++
            "  {s}--no-color{s}         Disable colored output for diagnostics.\n" ++
            "  {s}--verbose{s}          Enable verbose output.\n" ++
            "\n",
        .{
            Colors.bold,  Colors.reset, exec_name,
            Colors.bold,  Colors.reset, Colors.cyan,
            Colors.reset, Colors.cyan,  Colors.reset,
            Colors.cyan,  Colors.reset, Colors.cyan,
            Colors.reset, Colors.cyan,  Colors.reset,
            Colors.cyan,  Colors.reset, Colors.bold,
            Colors.reset, Colors.cyan,  Colors.reset,
            Colors.cyan,  Colors.reset, Colors.cyan,
            Colors.reset, Colors.cyan,  Colors.reset,
            Colors.cyan,  Colors.reset,
        },
    );
    try writer.flush();
}

fn process_file(
    allocator: std.mem.Allocator,
    filename: []const u8,
    cli_args: *CliArgs,
    err_writer: anytype,
    out_writer: anytype,
) !void {
    var file = try std.fs.cwd().openFile(filename, .{});
    const source = try file.readToEndAlloc(allocator, (try file.stat()).size);
    const source0 = try allocator.dupeZ(u8, source);
    defer allocator.free(source0);
    defer allocator.free(source);

    if (cli_args.verbose) {
        try err_writer.print("Compiling {s}...\n", .{filename});
    }

    var diags = compiler.diagnostics.Diagnostics.init(allocator);
    defer diags.deinit();

    var parser = compiler.parser.Parser.init(allocator, source0, &diags);
    var cst_program = try parser.parse();

    // For 'check' command, stop after semantic checks
    if (cli_args.subcommand == .check) {
        var lower_pass = compiler.lower.Lower.init(allocator, &diags);
        var hir = try lower_pass.run(&cst_program);

        var chk = compiler.checker.Checker.init(allocator, &diags);
        defer chk.deinit();
        try chk.run(&hir);
        var printer = compiler.ast.AstPrinter.init(out_writer);
        try printer.print(&hir);
        try out_writer.flush();

        try diags.emitStyled(source0, err_writer, filename, !cli_args.no_color);
        if (diags.anyErrors()) {
            return error.CompilationFailed;
        }
        try err_writer.print("{s}Checks passed for {s}.{s}\n", .{ Colors.green, filename, Colors.reset });
        return;
    }

    // For 'ast' command, print AST and exit
    if (cli_args.subcommand == .ast) {
        var lower_pass = compiler.lower.Lower.init(allocator, &diags);
        var hir = try lower_pass.run(&cst_program);
        var ast_printer = compiler.ast.AstPrinter.init(out_writer);
        try ast_printer.print(&hir);
        try out_writer.flush();
        return;
    }

    // For 'tir' command, print TIR and exit
    if (cli_args.subcommand == .tir) {
        var lower_pass = compiler.lower.Lower.init(allocator, &diags);
        var hir = try lower_pass.run(&cst_program);

        var chk = compiler.checker.Checker.init(allocator, &diags);
        defer chk.deinit();
        try chk.run(&hir);
        var typer = compiler.infer.Typer.init(allocator, &diags);
        const type_info = try allocator.create(compiler.infer.TypeInfo);
        type_info.* = typer.run(&hir) catch {
            try diags.addError(cst_program.decls.items[0].loc, "type inference failed", .{});
            try diags.emitStyled(source0, err_writer, filename, !cli_args.no_color);
            return error.CompilationFailed;
        };
        defer {
            type_info.deinit();
            allocator.destroy(type_info);
        }

        var tir_lowerer: compiler.lower_tir.LowerTir = undefined;
        try tir_lowerer.init(allocator, &type_info.arena, &type_info.expr_types, &type_info.decl_types);
        var mod = tir_lowerer.run(&hir) catch {
            try diags.addError(cst_program.decls.items[0].loc, "lowering to TIR failed", .{});
            try diags.emitStyled(source0, err_writer, filename, !cli_args.no_color);
            return error.CompilationFailed;
        };
        defer mod.deinit();

        var tir_printer = compiler.tir.Printer.init(out_writer, &type_info.arena);
        try tir_printer.printModule(&mod);
        return;
    }

    // Full compilation pipeline for 'compile' and 'run'
    var pl = compiler.pipeline.Pipeline.init(allocator, &diags);
    var result = pl.run(&cst_program) catch |err| {
        try diags.emitStyled(source0, err_writer, filename, !cli_args.no_color);
        return err; // Propagate pipeline errors
    };
    defer {
        // Deinit pipeline result components
        // result.hir.deinit();

        if (result.type_info) |type_info| {
            type_info.deinit();
            allocator.destroy(type_info);
        }
        result.module.deinit();
        result.gen.?.deinit();
    }

    try diags.emitStyled(source0, err_writer, filename, !cli_args.no_color);
    if (diags.anyErrors()) {
        return error.CompilationFailed;
    }

    if (cli_args.verbose) {
        try err_writer.print("{s}Compilation successful for {s}.{s}\n", .{ Colors.green, filename, Colors.reset });
    }

    // If 'run' command, execute the compiled binary
    if (cli_args.subcommand == .run) {
        const output_path = cli_args.output_path orelse "zig-out/output_program"; // Default from compile.zig
        var run_argv = [_][]const u8{output_path};
        var child = std.process.Child.init(run_argv[0..], allocator);
        if (cli_args.verbose) {
            try err_writer.print("{s}Running {s}...{s}\n", .{ Colors.blue, output_path, Colors.reset });
        }
        _ = try child.spawnAndWait();
    }
}

pub fn main() !void {
    const gpa = std.heap.page_allocator;
    var args_iter = std.process.args();
    const exec_name = args_iter.next().?;

    var cli_args: CliArgs = .{ .subcommand = .unknown };
    var filename_found = false;

    var buffer: [1024]u8 = undefined;
    var err = std.fs.File.stderr().writer(&buffer);
    var writer = &err.interface;

    while (args_iter.next()) |arg| {
        if (std.mem.startsWith(u8, arg, "--")) {
            if (std.mem.eql(u8, arg, "--output")) {
                cli_args.output_path = args_iter.next().?;
            } else if (std.mem.eql(u8, arg, "--emit-mlir")) {
                cli_args.emit_mlir = true;
            } else if (std.mem.eql(u8, arg, "--run-mlir")) {
                cli_args.run_mlir = true;
            } else if (std.mem.eql(u8, arg, "--no-color")) {
                cli_args.no_color = true;
            } else if (std.mem.eql(u8, arg, "--verbose")) {
                cli_args.verbose = true;
            } else {
                // Unknown option
                try writer.print("{s}Error:{s} Unknown option '{s}'\n", .{ Colors.red, Colors.reset, arg });
                try printUsage(writer, exec_name);
                std.process.exit(1);
            }
        } else {
            // Positional argument - should be subcommand or filename
            if (cli_args.subcommand == .unknown) {
                if (std.mem.eql(u8, arg, "compile")) {
                    cli_args.subcommand = .compile;
                } else if (std.mem.eql(u8, arg, "run")) {
                    cli_args.subcommand = .run;
                } else if (std.mem.eql(u8, arg, "check")) {
                    cli_args.subcommand = .check;
                } else if (std.mem.eql(u8, arg, "ast")) {
                    cli_args.subcommand = .ast;
                } else if (std.mem.eql(u8, arg, "tir")) {
                    cli_args.subcommand = .tir;
                } else if (std.mem.eql(u8, arg, "help")) {
                    cli_args.subcommand = .help;
                } else {
                    // Assume it's a filename if no subcommand yet
                    cli_args.filename = arg;
                    filename_found = true;
                }
            } else if (!filename_found) {
                cli_args.filename = arg;
                filename_found = true;
            } else {
                // Too many positional arguments
                try writer.print("{s}Error:{s} Too many arguments.\n", .{ Colors.red, Colors.reset });
                try printUsage(writer, exec_name);
                std.process.exit(1);
            }
        }
    }

    var out_buf: [1024]u8 = undefined;
    var out = std.fs.File.stdout().writer(&out_buf);
    const out_writer = &out.interface;

    switch (cli_args.subcommand) {
        .unknown => {
            if (cli_args.filename) |filename| {
                // If only a filename is provided without a subcommand, default to 'compile'
                cli_args.subcommand = .compile;
                try process_file(gpa, filename, &cli_args, writer, out_writer);
            } else {
                try printUsage(writer, exec_name);
                std.process.exit(1);
            }
        },
        .help => {
            try printUsage(out_writer, exec_name);
        },
        .compile, .run, .check, .ast, .tir => {
            if (cli_args.filename == null) {
                try writer.print("{s}Error:{s} Missing source file for '{s}' command.\n", .{ Colors.red, Colors.reset, @tagName(cli_args.subcommand) });
                try printUsage(writer, exec_name);
                std.process.exit(1);
            }
            try process_file(gpa, cli_args.filename.?, &cli_args, writer, out_writer);
        },
    }
}
