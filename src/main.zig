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
        lex,
        unknown,
        repl,
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

fn repl(
    allocator: std.mem.Allocator,
    err_writer: anytype,
    out_writer: anytype,
) !void {
    try err_writer.print("{s}Welcome to the REPL! Type your code and press Ctrl-D to evaluate.{s}\n", .{ Colors.green, Colors.reset });
    var in_buf: [4096]u8 = undefined;

    var stdin = std.fs.File.stdin().readerStreaming(&in_buf);
    var source_lines = std.ArrayList([]const u8){};
    defer source_lines.deinit(allocator);

    var interner = compiler.ast.StringInterner.init(allocator);
    defer interner.deinit();

    while (true) {
        try err_writer.print("{s}>>> {s}", .{ Colors.blue, Colors.reset });
        try err_writer.flush();
        const line = stdin.interface.takeDelimiterExclusive('\n') catch |err| switch (err) {
            error.EndOfStream => break, // clean EOF
            else => return err,
        };
        if (line.len == 0) continue; // Ignore empty lines
        try source_lines.append(allocator, try allocator.dupe(u8, line));
        try source_lines.append(allocator, "\n");
    }
    const source = try std.mem.concatWithSentinel(allocator, u8, source_lines.items, 0);
    std.debug.print("{s}Input source:{s}\n{s}\n", .{ Colors.bold, Colors.reset, source });
    var tokens = std.array_list.Managed(compiler.lexer.Token).init(allocator);
    defer tokens.deinit();
    var lexer = compiler.lexer.Tokenizer.init(source, .semi);
    while (true) {
        const token = lexer.next();
        try tokens.append(token);
        if (token.tag == .eof) break;
    }
    for (tokens.items) |t| {
        const lexeme = source[t.loc.start..t.loc.end];
        try out_writer.print("{}({},{}) `{s}`\n", .{ t.tag, t.loc.start, t.loc.end, lexeme });
    }
    try out_writer.flush();
    defer allocator.free(source);
    var diags = compiler.diagnostics.Diagnostics.init(allocator);
    defer diags.deinit();
    var parser = compiler.parser.Parser.init(allocator, source, &diags, &interner);
    var cst_program = try parser.parse();

    var cst_printer = compiler.cst.DodPrinter.init(
        out_writer,
        &cst_program.exprs,
        &cst_program.pats,
    );
    std.debug.print(
        "{s}Concrete Syntax Tree (CST){s}\n",
        .{ Colors.bold, Colors.green },
    );
    try cst_printer.printProgram(&cst_program.program);

    var lower_pass = compiler.lower.Lower.init(allocator, &cst_program, &diags);
    var hir = try lower_pass.run();
    // print AST
    var ast_printer = compiler.ast.AstPrinter.init(
        out_writer,
        &hir.exprs,
        &hir.stmts,
        &hir.pats,
    );
    std.debug.print(
        "{s}Abstract Syntax Tree (AST){s}\n",
        .{ Colors.bold, Colors.cyan },
    );
    try ast_printer.printUnit(&hir.unit);
    try out_writer.flush();
    var chk = compiler.checker.Checker.init(allocator, &diags, &hir);
    defer chk.deinit();
    defer chk.type_info.deinit();
    try chk.run();
    // print Diagnostics
    try diags.emitStyled(source, err_writer, "REPL Input", true);
    if (diags.anyErrors()) {
        // Do not proceed to TIR/codegen if semantic errors were found
        return;
    }

    var lower_tir = compiler.lower_tir.LowerTir.init(allocator, &chk.type_info, &interner);
    defer lower_tir.deinit();
    var tir = try lower_tir.run(&hir);
    defer tir.deinit();
    var tir_printer = compiler.tir.TirPrinter.init(out_writer, &tir);
    std.debug.print(
        "{s}Typed Intermediate Representation (TIR){s}\n",
        .{ Colors.bold, Colors.yellow },
    );
    try tir_printer.print();

    try out_writer.flush();

    const ctx = compiler.compile.initMLIR(allocator);

    // mlir codegen
    var codegen = compiler.mlir_codegen.MlirCodegen.init(allocator, ctx);
    defer codegen.deinit();
    var mlir_module = codegen.emitModule(&tir, tir.type_store) catch {
        try err_writer.print("{s}Error:{s} MLIR code generation failed.\n", .{ Colors.red, Colors.reset });
        return error.CompilationFailed;
    };
    std.debug.print(
        "{s}{s}MLIR Module\n",
        .{ Colors.bold, Colors.green },
    );
    const op = mlir_module.getOperation();
    op.dump();
    std.debug.print("{s}\n", .{Colors.reset});

    try compiler.compile.run_passes(&codegen.ctx, &mlir_module, true);
}

fn process_file(
    allocator: std.mem.Allocator,
    filename: []const u8,
    cli_args: *CliArgs,
    err_writer: anytype,
    out_writer: anytype,
    link_args: []const []const u8,
) !void {
    var file = try std.fs.cwd().openFile(filename, .{});
    const source = try file.readToEndAlloc(allocator, (try file.stat()).size);
    const source0 = try allocator.dupeZ(u8, source);
    defer allocator.free(source0);
    defer allocator.free(source);
    var interner = compiler.ast.StringInterner.init(allocator);
    defer interner.deinit();

    if (cli_args.verbose) {
        try err_writer.print("Compiling {s}...\n", .{filename});
    }

    if (cli_args.subcommand == .lex) {
        var lexer = compiler.lexer.Tokenizer.init(source0, .semi);
        while (true) {
            const token = lexer.next();
            if (token.tag == .eof) break;
            const lexeme = source0[token.loc.start..token.loc.end];
            try out_writer.print("{}({},{}) `{s}`\n", .{ token.tag, token.loc.start, token.loc.end, lexeme });
        }
        try out_writer.flush();
        return;
    }

    var diags = compiler.diagnostics.Diagnostics.init(allocator);
    defer diags.deinit();

    var parser = compiler.parser.Parser.init(allocator, source0, &diags, &interner);
    var cst_program = try parser.parse();

    // For 'check' command, stop after semantic checks
    if (cli_args.subcommand == .check) {
        var lower_pass = compiler.lower.Lower.init(allocator, &cst_program, &diags);
        var hir = try lower_pass.run();

        var chk = compiler.checker.Checker.init(allocator, &diags, &hir);
        defer chk.deinit();
        // Provide import resolver for module-aware type checking
        var res = compiler.import_resolver.ImportResolver.init(allocator, &diags);
        defer res.deinit();
        const base_dir = std.fs.path.dirname(filename) orelse ".";
        chk.setImportResolver(&res, base_dir);
        try chk.run();
        var printer = compiler.ast.AstPrinter.init(out_writer, &hir.exprs, &hir.stmts, &hir.pats);
        try printer.printUnit(&hir.unit);
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
        var lower_pass = compiler.lower.Lower.init(allocator, &cst_program, &diags);
        var hir = try lower_pass.run();
        var ast_printer = compiler.ast.AstPrinter.init(
            out_writer,
            &hir.exprs,
            &hir.stmts,
            &hir.pats,
        );
        try ast_printer.printUnit(&hir.unit);
        try out_writer.flush();
        return;
    }

    // For 'tir' command, print TIR and exit
    if (cli_args.subcommand == .tir) {
        var lower_pass = compiler.lower.Lower.init(allocator, &cst_program, &diags);
        var hir = try lower_pass.run();

        var chk = compiler.checker.Checker.init(allocator, &diags, &hir);
        defer chk.deinit();
        try chk.run();

        // If checker reported errors, emit and stop before lowering to TIR
        try diags.emitStyled(source0, err_writer, filename, !cli_args.no_color);
        if (diags.anyErrors()) {
            return error.CompilationFailed;
        }

        var lower_tir = compiler.lower_tir.LowerTir.init(allocator, &chk.type_info, &interner);
        defer lower_tir.deinit();
        var tir = try lower_tir.run(&hir);
        defer tir.deinit();
        var tir_printer = compiler.tir.TirPrinter.init(out_writer, &tir);
        try tir_printer.print();
        try out_writer.flush();

        return;
    }

    // Full compilation pipeline for 'compile' and 'run'
    var pl = compiler.pipeline.Pipeline.init(allocator, &diags);
    var parser2 = compiler.parser.Parser.init(allocator, source0, &diags, &interner);
    var cst_program_v2 = try parser2.parse();
    // Use new pipeline that resolves imports and appends codegen
    // Base dir is the directory of the input filename for relative imports
    const base_dir = std.fs.path.dirname(filename) orelse ".";
    var result = pl.runWithImports(&cst_program_v2, base_dir, link_args) catch |err| {
        try diags.emitStyled(source0, err_writer, filename, !cli_args.no_color);
        return err; // Propagate pipeline errors
    };
    defer {
        result.module.deinit();
        result.gen.deinit();
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

    var link_args_list: std.ArrayList([]const u8) = .empty;
    defer link_args_list.deinit(gpa);

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
                } else if (std.mem.eql(u8, arg, "lex")) {
                    cli_args.subcommand = .lex;
                } else if (std.mem.eql(u8, arg, "help")) {
                    cli_args.subcommand = .help;
                } else if (std.mem.eql(u8, arg, "repl")) {
                    cli_args.subcommand = .repl;
                } else {
                    // Assume it's a filename if no subcommand yet
                    cli_args.filename = arg;
                    filename_found = true;
                }
            } else if (!filename_found) {
                cli_args.filename = arg;
                filename_found = true;
            } else {
                // Treat additional args as linker args if they look like -l/-L or -Wl,
                if (std.mem.startsWith(u8, arg, "-l") or std.mem.startsWith(u8, arg, "-L") or std.mem.startsWith(u8, arg, "-Wl,")) {
                    try link_args_list.append(gpa, arg);
                } else if (std.mem.eql(u8, arg, "-l") or std.mem.eql(u8, arg, "-L")) {
                    if (args_iter.next()) |next| {
                        const combined = try std.fmt.allocPrint(gpa, "{s}{s}", .{ arg, next });
                        try link_args_list.append(gpa, combined);
                    } else {
                        try writer.print("{s}Error:{s} Missing value after '{s}'.\n", .{ Colors.red, Colors.reset, arg });
                        std.process.exit(1);
                    }
                } else {
                    // Unknown extra arg, keep warning but continue
                    try writer.print("{s}Warning:{s} Ignoring extra argument '{s}'.\n", .{ Colors.yellow, Colors.reset, arg });
                }
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
                try process_file(gpa, filename, &cli_args, writer, out_writer, link_args_list.items);
            } else {
                try printUsage(writer, exec_name);
                std.process.exit(1);
            }
        },
        .help => {
            try printUsage(out_writer, exec_name);
        },
        .compile, .run, .check, .ast, .tir, .lex => {
            if (cli_args.filename == null) {
                try writer.print("{s}Error:{s} Missing source file for '{s}' command.\n", .{ Colors.red, Colors.reset, @tagName(cli_args.subcommand) });
                try printUsage(writer, exec_name);
                std.process.exit(1);
            }
            try process_file(gpa, cli_args.filename.?, &cli_args, writer, out_writer, link_args_list.items);
        },
        .repl => try repl(gpa, writer, out_writer),
    }
}
