const std = @import("std");
const lib = @import("compiler");
const lsp = @import("lsp.zig");

const Colors = struct {
    pub const reset = "\x1b[0m";
    pub const bold = "\x1b[1m";
    pub const red = "\x1b[31m";
    pub const yellow = "\x1b[33m";
    pub const blue = "\x1b[34m";
    pub const cyan = "\x1b[36m";
    pub const green = "\x1b[32m";
};

const ProgressContext = struct {
    writer: *std.io.Writer,
    use_colors: bool,
    prev_line_length: usize,
};

fn reportProgress(ctx: ?*anyopaque, stage: lib.pipeline.ProgressStage, index: usize, total: usize) void {
    if (ctx) |c| {
        const p: *ProgressContext = @ptrCast(@alignCast(c));
        var buf: [128]u8 = undefined;
        const line = std.fmt.bufPrint(&buf, "[{d}/{d}] {s}", .{ index, total, lib.pipeline.stageName(stage) }) catch return;
        _ = p.writer.write("\r") catch {};
        if (p.use_colors) {
            _ = p.writer.print("\x1b[2K{s}{s}{s}{s}", .{ Colors.cyan, Colors.bold, line, Colors.reset }) catch {};
        } else {
            _ = p.writer.write(line) catch {};
            if (p.prev_line_length > line.len) {
                var pad: [64]u8 = undefined;
                @memset(&pad, ' ');
                var rem = p.prev_line_length - line.len;
                while (rem > 0) {
                    const n = @min(rem, pad.len);
                    _ = p.writer.write(pad[0..n]) catch {};
                    rem -= n;
                }
            }
            p.prev_line_length = line.len;
        }
        p.writer.flush() catch {};
    }
}

fn finalizeProgress(ctx: *ProgressContext, finalized: *bool, keep_line: bool) void {
    if (finalized.*) return;
    _ = ctx.writer.write(if (keep_line) "\n" else "\r\x1b[2K") catch {};
    _ = ctx.writer.flush() catch {};
    finalized.* = true;
}

const CliArgs = struct {
    subcommand: Subcommand = .unknown,
    filename: ?[]const u8 = null,
    output_path: ?[]const u8 = null,
    emit_tir: bool = false,
    emit_mlir: bool = false,
    run_mlir: bool = false,
    no_color: bool = false,
    verbose: bool = false,
    debug_info: bool = false,
    optimization_level: ?[]const u8 = null,
    tir_prune_unused: bool = true,
    tir_warn_unused: bool = false,

    const Subcommand = enum { compile, run, check, ast, cst, tir, tir_liveness, help, lex, interpret, mlir, mlir_passes, llvm_passes, test_mode, unknown, repl, pretty_print, json_ast, server, lsp, format };
};

fn printUsage(writer: anytype, exec: []const u8) !void {
    const b = Colors.bold;
    const r = Colors.reset;
    const c = Colors.cyan;
    try writer.print("{s}Usage:{s} {s} <command> [options] <file>\n\n", .{ b, r, exec });
    try writer.print("{s}Commands:{s}\n", .{ b, r });
    try writer.print("  {s}compile{s}       Compile a source file to an executable.\n", .{ c, r });
    try writer.print("  {s}run{s}           Compile and immediately run a source file.\n", .{ c, r });
    try writer.print("  {s}test{s}          Compile and run all test declarations.\n", .{ c, r });
    try writer.print("  {s}check{s}         Perform semantic checks.\n", .{ c, r });
    try writer.print("  {s}ast{s}           Print Abstract Syntax Tree (AST).\n", .{ c, r });
    try writer.print("  {s}cst{s}           Print Concrete Syntax Tree (CST).\n", .{ c, r });
    try writer.print("  {s}tir{s}           Print Typed IR (TIR).\n", .{ c, r });
    try writer.print("  {s}tir-liveness{s}  Dump TIR liveness analysis.\n", .{ c, r });
    try writer.print("  {s}interpret{s}     Run comptime interpreter.\n", .{ c, r });
    try writer.print("  {s}mlir{s}          Print MLIR representation.\n", .{ c, r });
    try writer.print("  {s}mlir_passes{s}   Run MLIR passes and print.\n", .{ c, r });
    try writer.print("  {s}llvm_passes{s}   Run LLVM passes and print.\n", .{ c, r });
    try writer.print("  {s}pretty-print{s}  Format and print source.\n", .{ c, r });
    try writer.print("  {s}format{s}        Reformat source in-place.\n", .{ c, r });
    try writer.print("  {s}json-ast{s}      Print AST as JSON.\n", .{ c, r });
    try writer.print("  {s}server{s}        Run AST Explorer server.\n", .{ c, r });
    try writer.print("  {s}lsp{s}           Start Language Server.\n", .{ c, r });
    try writer.print("  {s}help{s}          Display this message.\n\n", .{ c, r });
    try writer.print("{s}Options:{s}\n", .{ b, r });
    try writer.print("  {s}--output{s} <path>        Output path.\n", .{ c, r });
    try writer.print("  {s}--emit-tir{s}             Emit TIR to stdout.\n", .{ c, r });
    try writer.print("  {s}--emit-mlir{s}            Emit MLIR to stdout.\n", .{ c, r });
    try writer.print("  {s}--run-mlir{s}             Run MLIR JIT.\n", .{ c, r });
    try writer.print("  {s}--no-color{s}             Disable colors.\n", .{ c, r });
    try writer.print("  {s}--verbose{s}              Enable verbose output.\n", .{ c, r });
    try writer.print("  {s}--debug{s}                Enable debug info.\n", .{ c, r });
    try writer.print("  {s}--tir-prune-unused{s}     Prune unused TIR.\n", .{ c, r });
    try writer.print("  {s}--tir-warn-unused{s}      Warn on unused TIR.\n", .{ c, r });
    try writer.print("  {s}-O<level>{s}              Optimization level (0,1,2,3,s,z).\n\n", .{ c, r });
    try writer.flush();
}

fn repl(gpa: std.mem.Allocator, err_w: anytype, out_w: anytype) !void {
    try err_w.print("{s}Welcome to the REPL! Type code, Ctrl-D to evaluate.{s}\n", .{ Colors.green, Colors.reset });
    var ctx = lib.compile.Context.init(gpa);
    defer ctx.deinit();
    var pipeline = lib.pipeline.Pipeline.init(gpa, &ctx);
    var buf: [4096]u8 = undefined;
    var stdin = std.fs.File.stdin().readerStreaming(&buf);
    var lines = std.ArrayList([]const u8){};
    defer lines.deinit(gpa);

    while (true) {
        try err_w.print("{s}>>> {s}", .{ Colors.blue, Colors.reset });
        try err_w.flush();
        const line = stdin.interface.takeDelimiterExclusive('\n') catch |e| if (e == error.EndOfStream) break else return e;
        if (line.len == 0) continue;
        try lines.append(gpa, try gpa.dupe(u8, line));
        try lines.append(gpa, "\n");
    }
    const src = try std.mem.concatWithSentinel(gpa, u8, lines.items, 0);
    defer gpa.free(src);
    std.debug.print("{s}Input:{s}\n{s}\n", .{ Colors.bold, Colors.reset, src });

    const res = try pipeline.run(src, &.{}, .repl, null, null);
    const main_pkg = res.compilation_unit.?.packages.getPtr("main") orelse return error.NoMainPackage;
    var ent = main_pkg.sources.entries.get(0).value;

    var cst_p = lib.cst.DodPrinter.init(out_w, &ent.cst.?.exprs, &ent.cst.?.pats);
    std.debug.print("{s}CST{s}\n", .{ Colors.bold, Colors.green });
    try cst_p.printProgram(&ent.cst.?.program);
    var ast_p = lib.ast.AstPrinter.init(out_w, &ent.ast.?.exprs, &ent.ast.?.stmts, &ent.ast.?.pats);
    std.debug.print("{s}AST{s}\n", .{ Colors.bold, Colors.cyan });
    try ast_p.printUnit(&ent.ast.?.unit);
    var tir_p = lib.tir.TirPrinter.init(out_w, ent.tir.?);
    std.debug.print("{s}TIR{s}\n", .{ Colors.bold, Colors.yellow });
    try tir_p.print();
    if (res.mlir_module) |m| {
        std.debug.print("{s}MLIR{s}\n", .{ Colors.bold, Colors.green });
        m.getOperation().dump();
    }
    std.debug.print("{s}\n", .{Colors.reset});
    try out_w.flush();
}

fn server(allocator: std.mem.Allocator, _: anytype) !void {
    const addr = try std.net.Address.parseIp4("127.0.0.1", 8000);
    var tcp = try addr.listen(.{ .reuse_address = true });
    defer tcp.deinit();
    std.debug.print("AST server on http://127.0.0.1:8000\n", .{});

    while (true) {
        var conn = tcp.accept() catch continue;
        defer conn.stream.close();
        var rbuf: [4096]u8 = undefined;
        var wbuf: [4096]u8 = undefined;
        var reader = conn.stream.reader(&rbuf);
        var writer = conn.stream.writer(&wbuf);
        var http = std.http.Server.init(reader.interface(), &writer.interface);
        while (http.reader.state == .ready) {
            var req = http.receiveHead() catch break;
            if (req.head.method == .OPTIONS) {
                try req.respond("", .{ .status = .no_content, .extra_headers = &.{ .{ .name = "access-control-allow-origin", .value = "*" }, .{ .name = "access-control-allow-headers", .value = "content-type" } } });
                continue;
            }
            if (req.head.method != .POST) {
                try req.respond("Only POST\n", .{ .status = .method_not_allowed });
                continue;
            }
            var bbuf: [4096]u8 = undefined;
            const len = req.head.content_length orelse {
                try req.respond("No Length\n", .{ .status = .length_required });
                continue;
            };
            const body = req.readerExpectNone(&bbuf).readAlloc(allocator, len) catch {
                try req.respond("Read Fail\n", .{ .status = .bad_request });
                continue;
            };
            defer allocator.free(body);
            const src = try allocator.dupeZ(u8, body);
            defer allocator.free(src);

            var ctx = lib.compile.Context.init(allocator);
            defer ctx.deinit();
            var pipe = lib.pipeline.Pipeline.init(allocator, &ctx);
            const res = try pipe.run(src, &.{}, .ast, null, null);

            if (ctx.diags.anyErrors()) {
                try req.respond("Errors\n", .{ .status = .bad_request, .extra_headers = &.{.{ .name = "access-control-allow-origin", .value = "*" }} });
                continue;
            }
            var jbuf = std.Io.Writer.Allocating.init(allocator);
            defer jbuf.deinit();
            const ast = res.compilation_unit.?.packages.getPtr("main").?.sources.entries.get(0).value.ast.?;
            var jp = lib.json_printer.JsonPrinter.init(&jbuf.writer, &ast.exprs, &ast.stmts, &ast.pats);
            try jp.printUnit(&ast.unit);
            const json = try jbuf.toOwnedSlice();
            defer allocator.free(json);
            try req.respond(json, .{ .status = .ok, .extra_headers = &.{ .{ .name = "content-type", .value = "application/json" }, .{ .name = "access-control-allow-origin", .value = "*" } } });
        }
    }
}

fn process_file(ctx: *lib.compile.Context, alloc: std.mem.Allocator, file: []const u8, args: *CliArgs, err_w: anytype, out_w: anytype, link: []const []const u8) !void {
    var abuf: [std.fs.max_path_bytes]u8 = undefined;
    const abs_path = std.fs.cwd().realpath(file, &abuf) catch file;

    if (args.subcommand == .format or args.subcommand == .pretty_print) {
        const src = try std.fs.cwd().readFileAlloc(alloc, abs_path, 10 << 20);
        defer alloc.free(src);
        const zsrc = try std.mem.concatWithSentinel(alloc, u8, &.{src}, 0);
        defer alloc.free(zsrc);
        const fmt = try lib.formatter.formatSource(alloc, zsrc, abs_path);
        defer alloc.free(fmt);
        if (args.subcommand == .pretty_print) {
            try out_w.writeAll(fmt);
            try out_w.flush();
        } else {
            var f = try std.fs.cwd().createFile(abs_path, .{ .truncate = true });
            defer f.close();
            try f.writeAll(fmt);
        }
        return;
    }

    var pipe = lib.pipeline.Pipeline.init(alloc, ctx);
    pipe.tir_prune_unused = args.tir_prune_unused;
    pipe.tir_warn_unused = args.tir_warn_unused;
    pipe.debug_info = args.debug_info;
    lib.codegen.enable_debug_info = args.debug_info;

    var prog_ctx = ProgressContext{ .writer = err_w, .use_colors = !args.no_color, .prev_line_length = 0 };
    var prog_rep = lib.pipeline.ProgressReporter{ .callback = reportProgress, .context = &prog_ctx };
    var prog_done = false;
    const use_prog = (args.subcommand == .compile or args.subcommand == .run) and !args.verbose;
    const prog_ptr = if (use_prog) &prog_rep else null;

    if (args.verbose) try err_w.print("Compiling {s}...\n", .{abs_path});

    const mode: lib.pipeline.Pipeline.Mode = switch (args.subcommand) {
        .compile => .compile,
        .run => .run,
        .test_mode => .test_mode,
        .check => .check,
        .ast, .pretty_print, .json_ast => .ast,
        .cst => .parse,
        .tir => .tir,
        .tir_liveness => .tir_liveness,
        .lex => .lex,
        .mlir => .mlir,
        .interpret => .interpret,
        .mlir_passes => .passes,
        .llvm_passes => .llvm_passes,
        else => unreachable,
    };

    const res = pipe.run(abs_path, link, mode, prog_ptr, args.optimization_level) catch |e| {
        if (use_prog) finalizeProgress(&prog_ctx, &prog_done, true);
        if (ctx.diags.anyErrors()) try ctx.diags.emitStyled(ctx, err_w, !args.no_color);
        return e;
    };
    if (use_prog) finalizeProgress(&prog_ctx, &prog_done, false);

    if (args.emit_tir) {
        for (ctx.compilation_unit.packages.values()) |pkg| for (pkg.sources.values()) |e| if (e.tir) |t| {
            var tp = lib.tir.TirPrinter.init(out_w, t);
            tp.print() catch {};
        };
        try out_w.flush();
    }

    switch (args.subcommand) {
        .check => if (ctx.diags.count() > 0) try ctx.diags.emitStyled(ctx, err_w, !args.no_color),
        .ast => {
            for (res.compilation_unit.?.packages.values()) |pkg| {
                for (pkg.sources.values()) |e| {
                    var p = lib.ast.AstPrinter.init(out_w, &e.ast.?.exprs, &e.ast.?.stmts, &e.ast.?.pats);
                    try p.printUnit(&e.ast.?.unit);
                }
            }
            try out_w.flush();
        },
        .cst => {
            for (res.compilation_unit.?.packages.values()) |pkg| {
                for (pkg.sources.values()) |*e| {
                    var p = lib.cst.DodPrinter.init(out_w, &e.cst.?.exprs, &e.cst.?.pats);
                    try p.printProgram(&e.cst.?.program);
                }
            }
            try out_w.flush();
        },
        .json_ast => {
            for (res.compilation_unit.?.packages.values()) |pkg| {
                for (pkg.sources.values()) |e| {
                    var p = lib.json_printer.JsonPrinter.init(out_w, &e.ast.?.exprs, &e.ast.?.stmts, &e.ast.?.pats);
                    try p.printUnit(&e.ast.?.unit);
                }
            }
            try out_w.flush();
        },
        .tir => {
            for (res.compilation_unit.?.packages.values()) |pkg| for (pkg.sources.values()) |e| if (e.tir) |t| {
                var p = lib.tir.TirPrinter.init(out_w, t);
                try p.print();
            };
            try out_w.flush();
        },
        .run => lib.compile.run(),
        .test_mode => {
            const status = lib.compile.runWithStatus() catch {
                try err_w.print("{s}Error:{s} Test harness failed.\n", .{ Colors.red, Colors.reset });
                return;
            };
            const fails: usize = @intCast(status);
            try out_w.print("{s}tests:{s} {d} passed; {d} failed\n", .{ Colors.bold, Colors.reset, if (fails > res.test_count) 0 else res.test_count - fails, fails });
            if (status != 0) std.process.exit(status);
        },
        else => {},
    }
    if (ctx.diags.count() > 0 and args.subcommand != .check) try ctx.diags.emitStyled(ctx, err_w, !args.no_color);
    if (args.verbose) try err_w.print("{s}Success: {s}.{s}\n", .{ Colors.green, file, Colors.reset });
}

pub fn main() !void {
    const gpa = std.heap.page_allocator;
    var iter = std.process.args();
    const exec = iter.next().?;
    var args = CliArgs{};
    var link = std.ArrayList([]const u8){};
    defer link.deinit(gpa);

    const cmds = std.StaticStringMap(CliArgs.Subcommand).initComptime(.{
        .{ "compile", .compile },
        .{ "run", .run },
        .{ "test", .test_mode },
        .{ "check", .check },
        .{ "ast", .ast },
        .{ "cst", .cst },
        .{ "tir", .tir },
        .{ "tir-liveness", .tir_liveness },
        .{ "mlir", .mlir },
        .{ "mlir_passes", .mlir_passes },
        .{ "llvm_passes", .llvm_passes },
        .{ "interpret", .interpret },
        .{ "pretty-print", .pretty_print },
        .{ "format", .format },
        .{ "lex", .lex },
        .{ "help", .help },
        .{ "repl", .repl },
        .{ "json-ast", .json_ast },
        .{ "server", .server },
        .{ "lsp", .lsp },
    });

    var obuf: [1024]u8 = undefined;
    var ebuf: [1024]u8 = undefined;
    var stdout = std.fs.File.stdout().writer(&obuf);
    var stderr = std.fs.File.stderr().writer(&ebuf);
    const out_w = &stdout.interface;
    const err_w = &stderr.interface;

    while (iter.next()) |arg| {
        if (std.mem.startsWith(u8, arg, "--")) {
            if (std.mem.eql(u8, arg, "--output")) args.output_path = iter.next().? else if (std.mem.eql(u8, arg, "--emit-tir")) args.emit_tir = true else if (std.mem.eql(u8, arg, "--emit-mlir")) args.emit_mlir = true else if (std.mem.eql(u8, arg, "--run-mlir")) args.run_mlir = true else if (std.mem.eql(u8, arg, "--no-color")) args.no_color = true else if (std.mem.eql(u8, arg, "--tir-prune-unused")) args.tir_prune_unused = true else if (std.mem.eql(u8, arg, "--tir-warn-unused")) args.tir_warn_unused = true else if (std.mem.eql(u8, arg, "--verbose")) args.verbose = true else if (std.mem.eql(u8, arg, "--debug")) args.debug_info = true else {
                try err_w.print("{s}Error:{s} Unknown '{s}'\n", .{ Colors.red, Colors.reset, arg });
                try printUsage(err_w, exec);
                std.process.exit(1);
            }
        } else if (std.mem.startsWith(u8, arg, "-O")) {
            args.optimization_level = if (arg.len > 2) arg[2..] else iter.next();
        } else if (std.mem.startsWith(u8, arg, "-l") or std.mem.startsWith(u8, arg, "-L") or std.mem.startsWith(u8, arg, "-Wl,")) {
            if (arg.len == 2) {
                if (iter.next()) |n| try link.append(gpa, try std.fmt.allocPrint(gpa, "{s}{s}", .{ arg, n }));
            } else try link.append(gpa, arg);
        } else if (std.mem.endsWith(u8, arg, ".o") or std.mem.endsWith(u8, arg, ".a") or std.mem.endsWith(u8, arg, ".so")) {
            try link.append(gpa, arg);
        } else if (cmds.get(arg)) |cmd| {
            args.subcommand = cmd;
        } else {
            args.filename = arg;
        }
    }

    if (args.subcommand == .unknown) {
        if (args.filename) |_| args.subcommand = .compile else {
            try printUsage(err_w, exec);
            std.process.exit(1);
        }
    }
    if (args.subcommand == .help) {
        try printUsage(out_w, exec);
        return;
    }
    if (args.subcommand == .repl) {
        try repl(gpa, err_w, out_w);
        return;
    }
    if (args.subcommand == .server) {
        try server(gpa, err_w);
        return;
    }
    if (args.subcommand == .lsp) {
        try lsp.run(gpa);
        return;
    }

    if (args.filename == null) {
        try err_w.print("{s}Error:{s} Missing file for '{s}'\n", .{ Colors.red, Colors.reset, @tagName(args.subcommand) });
        std.process.exit(1);
    }

    var ctx = lib.compile.Context.init(gpa);
    defer ctx.deinit();
    process_file(&ctx, gpa, args.filename.?, &args, err_w, out_w, link.items) catch |e| {
        if (ctx.diags.anyErrors()) try ctx.diags.emitStyled(&ctx, err_w, !args.no_color);
        return e;
    };
}
