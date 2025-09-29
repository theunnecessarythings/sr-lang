const std = @import("std");
const lib = @import("compiler");

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
        pretty_print,
        json_ast,
        server,
    };
};

// Function to print usage information
fn printUsage(writer: anytype, exec_name: []const u8) !void {
    try writer.print(
        "{s}Usage:{s} {s} <command> [options] <file>\n\n",
        .{ Colors.bold, Colors.reset, exec_name },
    );

    try writer.print(
        "{s}Commands:{s}\n",
        .{ Colors.bold, Colors.reset },
    );
    try writer.print("  {s}compile{s} <file>      Compile a source file to an executable.\n", .{ Colors.cyan, Colors.reset });
    try writer.print("  {s}run{s} <file>         Compile and immediately run a source file.\n", .{ Colors.cyan, Colors.reset });
    try writer.print("  {s}check{s} <file>        Parse and perform semantic checks on a source file.\n", .{ Colors.cyan, Colors.reset });
    try writer.print("  {s}ast{s} <file>         Print the Abstract Syntax Tree (AST) of a source file.\n", .{ Colors.cyan, Colors.reset });
    try writer.print("  {s}tir{s} <file>         Print the Typed Intermediate Representation (TIR) of a source file.\n", .{ Colors.cyan, Colors.reset });
    try writer.print("  {s}pretty-print{s} <file>  Format and print the source file.\n", .{ Colors.cyan, Colors.reset });
    try writer.print("  {s}json-ast{s} <file>      Print the Abstract Syntax Tree (AST) of a source file as JSON.\n", .{ Colors.cyan, Colors.reset });
    try writer.print("  {s}server{s}             Run a server for AST Explorer.\n", .{ Colors.cyan, Colors.reset });
    try writer.print("  {s}help{s}               Display this help message.\n\n", .{ Colors.cyan, Colors.reset });

    try writer.print(
        "{s}Options:{s}\n",
        .{ Colors.bold, Colors.reset },
    );
    try writer.print("  {s}--output{s} <path>    Specify the output path for compiled executables.\n", .{ Colors.cyan, Colors.reset });
    try writer.print("  {s}--emit-mlir{s}        Emit MLIR IR to stdout during compilation.\n", .{ Colors.cyan, Colors.reset });
    try writer.print("  {s}--run-mlir{s}         Run MLIR JIT after compilation (for testing).\n", .{ Colors.cyan, Colors.reset });
    try writer.print("  {s}--no-color{s}         Disable colored output for diagnostics.\n", .{ Colors.cyan, Colors.reset });
    try writer.print("  {s}--verbose{s}          Enable verbose output.\n\n", .{ Colors.cyan, Colors.reset });
    try writer.flush();
}

fn repl(
    allocator: std.mem.Allocator,
    err_writer: anytype,
    out_writer: anytype,
) !void {
    try err_writer.print("{s}Welcome to the REPL! Type your code and press Ctrl-D to evaluate.{s}\n", .{ Colors.green, Colors.reset });
    var context = lib.compile.Context.init(allocator);
    defer context.deinit();

    var pipeline = lib.pipeline.Pipeline.init(allocator, &context);

    var in_buf: [4096]u8 = undefined;

    var stdin = std.fs.File.stdin().readerStreaming(&in_buf);
    var source_lines = std.ArrayList([]const u8){};
    defer source_lines.deinit(allocator);

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

    const result = try pipeline.runWithImports(source, &.{}, .jit); // Run the pipeline

    // Print results based on the 'result' struct
    if (result.cst) |cst_program| {
        var cst_printer = lib.cst.DodPrinter.init(out_writer, &cst_program.exprs, &cst_program.pats);
        std.debug.print("{s}Concrete Syntax Tree (CST){s}\n", .{ Colors.bold, Colors.green });
        try cst_printer.printProgram(&cst_program.program);
    }
    if (result.ast) |hir| {
        var ast_printer = lib.ast.AstPrinter.init(out_writer, &hir.exprs, &hir.stmts, &hir.pats);
        std.debug.print("{s}Abstract Syntax Tree (AST){s}\n", .{ Colors.bold, Colors.cyan });
        try ast_printer.printUnit(&hir.unit);
    }
    if (result.tir) |tir_mod| {
        var tir_printer = lib.tir.TirPrinter.init(out_writer, &tir_mod);
        std.debug.print("{s}Typed Intermediate Representation (TIR){s}\n", .{ Colors.bold, Colors.yellow });
        try tir_printer.print();
    }
    if (result.mlir_module) |mlir_module| {
        std.debug.print("{s}{s}MLIR Module\n", .{ Colors.bold, Colors.green });
        var op = mlir_module.getOperation();
        op.dump();
        std.debug.print("{s}\n", .{Colors.reset});
    }
    try out_writer.flush();
    defer allocator.free(source);
}

fn server(
    allocator: std.mem.Allocator,
    err_writer: anytype,
) !void {
    // Listen on localhost:8080 (can tweak if needed)
    const addr = try std.net.Address.parseIp4("127.0.0.1", 8000);
    var tcp = try addr.listen(.{ .reuse_address = true });
    defer tcp.deinit();

    std.debug.print("AST server listening on http://127.0.0.1:8000\n", .{});

    accept_loop: while (true) {
        const conn = tcp.accept() catch |e| {
            std.debug.print("accept error: {s}\n", .{@errorName(e)});
            continue :accept_loop;
        };
        defer conn.stream.close();

        // HTTP over the accepted TCP stream (Zig 0.15.1 style: operate on I/O streams)
        var recv_buf: [4096]u8 = undefined;
        var send_buf: [4096]u8 = undefined;
        var conn_reader = conn.stream.reader(&recv_buf);
        var conn_writer = conn.stream.writer(&send_buf);
        var http = std.http.Server.init(conn_reader.interface(), &conn_writer.interface);

        request_loop: while (http.reader.state == .ready) {
            var req = http.receiveHead() catch |err| switch (err) {
                error.HttpConnectionClosing => break :request_loop,
                else => {
                    std.debug.print("receiveHead error: {s}\n", .{@errorName(err)});
                    break :request_loop;
                },
            };

            // Basic CORS / preflight support
            if (req.head.method == .OPTIONS) {
                try req.respond("", .{
                    .status = .no_content,
                    .extra_headers = &.{
                        .{ .name = "access-control-allow-origin", .value = "*" },
                        .{ .name = "access-control-allow-headers", .value = "content-type" },
                        .{ .name = "access-control-allow-methods", .value = "POST, OPTIONS" },
                    },
                });
                continue :request_loop;
            }

            if (req.head.method != .POST) {
                try req.respond("Only POST is supported\n", .{
                    .status = .method_not_allowed,
                    .extra_headers = &.{
                        .{ .name = "content-type", .value = "text/plain; charset=utf-8" },
                        .{ .name = "access-control-allow-origin", .value = "*" },
                    },
                });
                continue :request_loop;
            }

            // Read request body (source text)
            var body_reader_buf: [4096]u8 = undefined;
            var body_reader = req.readerExpectNone(&body_reader_buf);
            const content_length = req.head.content_length orelse {
                std.debug.print("Missing Content-Length\n", .{});
                try req.respond("Missing Content-Length\n", .{
                    .status = .length_required,
                    .extra_headers = &.{
                        .{ .name = "content-type", .value = "text/plain; charset=utf-8" },
                        .{ .name = "access-control-allow-origin", .value = "*" },
                    },
                });
                continue :request_loop;
            };

            const body = body_reader.readAlloc(allocator, content_length) catch |e| {
                std.debug.print("read body error: {s}\n", .{@errorName(e)});
                try req.respond("Failed to read body\n", .{
                    .status = .bad_request,
                    .extra_headers = &.{
                        .{ .name = "content-type", .value = "text/plain; charset=utf-8" },
                        .{ .name = "access-control-allow-origin", .value = "*" },
                    },
                });
                continue :request_loop;
            };
            defer allocator.free(body);

            // Null-terminate for the compiler pipeline
            const source = try allocator.dupeZ(u8, body);
            defer allocator.free(source);

            var context = lib.compile.Context.init(allocator);
            defer context.deinit();

            var pipeline = lib.pipeline.Pipeline.init(allocator, &context); // Create pipeline here

            const result = try pipeline.runWithImports(source, &.{}, .ast); // Run the pipeline to AST

            // If there are diagnostics, emit them to stderr and return 400
            if (context.diags.anyErrors()) {
                try context.diags.emitStyled(source, &context, err_writer, "request", true);
                try req.respond("Semantic errors\n", .{
                    .status = .bad_request,
                    .extra_headers = &.{
                        .{ .name = "content-type", .value = "text/plain; charset=utf-8" },
                        .{ .name = "access-control-allow-origin", .value = "*" },
                    },
                });
                continue :request_loop;
            }

            // Print HIR as JSON into an allocating writer buffer
            var json_buf: std.Io.Writer.Allocating = .init(allocator);
            defer json_buf.deinit();

            var json_printer = lib.json_printer.JsonPrinter.init(
                &json_buf.writer,
                &result.ast.?.exprs, // Use result.ast
                &result.ast.?.stmts, // Use result.ast
                &result.ast.?.pats, // Use result.ast
            );
            try json_printer.printUnit(&result.ast.?.unit); // Use result.ast

            const json = try json_buf.toOwnedSlice();
            defer allocator.free(json);

            // Respond with JSON
            try req.respond(json, .{
                .status = .ok,
                .extra_headers = &.{
                    .{ .name = "content-type", .value = "application/json" },
                    .{ .name = "access-control-allow-origin", .value = "*" },
                },
            });
        }
    }
}

fn process_file(
    allocator: std.mem.Allocator,
    filename: []const u8,
    cli_args: *CliArgs,
    err_writer: anytype,
    out_writer: anytype,
    link_args: []const []const u8,
) !void {
    var compiler_ctx = lib.compile.Context.init(allocator);
    var pipeline = lib.pipeline.Pipeline.init(allocator, &compiler_ctx);

    if (cli_args.verbose) {
        try err_writer.print("Compiling {s}...\n", .{filename});
    }
    const result = try pipeline.runWithImports(filename, link_args, switch (cli_args.subcommand) {
        .compile => .exec,
        .run => .run,
        .check => .check,
        .ast => .ast,
        .tir => .tir,
        .lex => .lex,
        .pretty_print => .ast,
        .json_ast => .ast,
        else => unreachable,
    });

    // For 'check' command, stop after semantic checks
    if (cli_args.subcommand == .check) {
        const hir = result.ast.?;
        var printer = lib.ast.AstPrinter.init(out_writer, &hir.exprs, &hir.stmts, &hir.pats);
        try printer.printUnit(&hir.unit);
        try out_writer.flush();
        return;
    }
    if (cli_args.subcommand == .ast) {
        const hir = result.ast.?;
        var ast_printer = lib.ast.AstPrinter.init(
            out_writer,
            &hir.exprs,
            &hir.stmts,
            &hir.pats,
        );
        try ast_printer.printUnit(&hir.unit);
        try out_writer.flush();
        return;
    }

    // For 'pretty-print' command, print formatted code and exit
    if (cli_args.subcommand == .pretty_print) {
        const hir = result.ast.?;
        var code_printer = lib.ast.CodePrinter.init(
            out_writer,
            &hir.exprs,
            &hir.stmts,
            &hir.pats,
        );
        try code_printer.printUnit(&hir.unit);
        try out_writer.flush();
        return;
    }

    // For 'json-ast' command, print AST as JSON and exit
    if (cli_args.subcommand == .json_ast) {
        const hir = result.ast.?;
        var json_printer = lib.json_printer.JsonPrinter.init(
            out_writer,
            &hir.exprs,
            &hir.stmts,
            &hir.pats,
        );
        try json_printer.printUnit(&hir.unit);
        try out_writer.flush();
        return;
    }

    // For 'tir' command, print TIR and exit
    if (cli_args.subcommand == .tir) {
        const tir = result.tir.?;
        var tir_printer = lib.tir.TirPrinter.init(out_writer, &tir);
        try tir_printer.print();
        try out_writer.flush();

        return;
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
                } else if (std.mem.eql(u8, arg, "json-ast")) {
                    cli_args.subcommand = .json_ast;
                } else if (std.mem.eql(u8, arg, "server")) {
                    cli_args.subcommand = .server;
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
        .compile, .run, .check, .ast, .tir, .lex, .pretty_print, .json_ast => {
            if (cli_args.filename == null) {
                try writer.print("{s}Error:{s} Missing source file for '{s}' command.\n", .{ Colors.red, Colors.reset, @tagName(cli_args.subcommand) });
                try printUsage(writer, exec_name);
                std.process.exit(1);
            }
            process_file(gpa, cli_args.filename.?, &cli_args, writer, out_writer, link_args_list.items) catch |e| {
                try writer.flush();
                return e;
            };
        },
        .repl => try repl(gpa, writer, out_writer),
        .server => try server(gpa, writer),
    }
}
