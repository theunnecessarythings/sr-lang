const compiler = @import("compiler");
const std = @import("std");
const lexer = compiler.lexer;
const parser = compiler.parser;
const diagnostics = compiler.diagnostics;
const lower = compiler.lower_to_ast;
const ast = compiler.ast;
const checker = compiler.checker;
const SymbolStore = compiler.symbols.SymbolStore;

fn testLexer(data: []const u8) !void {
    const source0 = try std.heap.page_allocator.dupeZ(u8, data);
    defer std.heap.page_allocator.free(source0);
    var tokenizer = lexer.Tokenizer.init(source0, 0, .semi);
    var tokenization_failed = false;
    while (true) {
        const token = tokenizer.next();

        // Property: token end location after start location (or equal)
        try std.testing.expect(token.loc.end >= token.loc.start);

        switch (token.tag) {
            .invalid => {
                tokenization_failed = true;

                // Property: invalid token always ends at newline or eof
                try std.testing.expect(source0[token.loc.end] == '\n' or source0[token.loc.end] == 0);
            },
            .eof => {
                // Property: EOF token is always 0-length at end of source.
                try std.testing.expectEqual(source0.len, token.loc.start);
                try std.testing.expectEqual(source0.len, token.loc.end);
                break;
            },
            else => continue,
        }
    }

    if (source0.len > 0) for (source0, source0[1..][0..source0.len]) |cur, next| {
        // Property: No null byte allowed except at end.
        if (cur == 0) {
            try std.testing.expect(tokenization_failed);
        }
        // Property: No ASCII control characters other than \n and \t are allowed.
        if (std.ascii.isControl(cur) and cur != '\n' and cur != '\t' and cur != '\r') {
            try std.testing.expect(tokenization_failed);
        }
        // Property: All '\r' must be followed by '\n'.
        if (cur == '\r' and next != '\n') {
            try std.testing.expect(tokenization_failed);
        }
    };
}

pub export fn fuzz_lexer(ptr: [*]const u8, len: usize) callconv(.c) void {
    const data = ptr[0..len];
    _ = testLexer(data) catch |err| {
        std.debug.panic("lexer failed: {}\n", .{err});
    };
}

fn testParser(data: []const u8) !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const gpa = arena.allocator();

    var context = compiler.compile.Context.init(gpa); // Create context
    defer context.deinit();

    const source0 = try gpa.dupeZ(u8, data);
    // diags and interner are now part of context, no need to create separately

    var parser_mod = parser.Parser.init(gpa, source0, 0, context.diags, &context); // Pass file_id and context
    var tree = parser_mod.parse() catch |err| switch (err) {
        error.UnexpectedToken => {
            try std.testing.expect(context.diags.anyErrors()); // Use context.diags
            return;
        },
        error.OutOfMemory => std.debug.panic("parser OOM", .{}),
        else => std.debug.panic("parser failed: {}", .{err}),
    };
    defer tree.deinit();

    // if (context.diags.anyErrors()) return; // Use context.diags

    try std.testing.expectEqual(lexer.Token.Tag.eof, parser_mod.cur.tag);
}

pub export fn fuzz_parser(ptr: [*]const u8, len: usize) callconv(.c) void {
    const data = ptr[0..len];
    _ = testParser(data) catch |err| {
        std.debug.panic("parser failed: {}\n", .{err});
    };
}

fn testLower(data: []const u8) !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const gpa = arena.allocator();

    var context = compiler.compile.Context.init(gpa); // Create context
    defer context.deinit();

    const source0 = try gpa.dupeZ(u8, data);
    // diags and interner are now part of context, no need to create separately

    var parser_mod = parser.Parser.init(gpa, source0, 0, context.diags, &context); // Pass file_id and context
    var tree = parser_mod.parse() catch |err| switch (err) {
        error.UnexpectedToken => return, // invalid input is fine for fuzzing
        error.OutOfMemory => std.debug.panic("parser OOM", .{}),
        else => std.debug.panic("parser failed: {}", .{err}),
    };
    defer tree.deinit();

    var lower_mod = try lower.Lower.init(gpa, &tree, &context, 0); // Pass context
    var a = try (&lower_mod).run();
    defer a.deinit();

    var buffer: [1024]u8 = undefined;
    var sink = std.fs.File.stdout().writer(&buffer);
    const writer = &sink.interface;
    var printer = ast.AstPrinter.init(writer, &a.exprs, &a.stmts, &a.pats);
    try printer.printUnit(&a.unit);
}

pub export fn fuzz_lower(ptr: [*]const u8, len: usize) callconv(.c) void {
    const data = ptr[0..len];
    _ = testLower(data) catch |err| {
        std.debug.panic("lower failed: {}\n", .{err});
    };
}

fn testChecker(data: []const u8) !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const gpa = arena.allocator();

    var context = compiler.compile.Context.init(gpa); // Create context
    defer context.deinit();

    // Create a dummy pipeline for the checker
    var pipeline = compiler.pipeline.Pipeline.init(gpa, &context);

    const source0 = try gpa.dupeZ(u8, data);
    // diags and interner are now part of context, no need to create separately

    var parser_mod = parser.Parser.init(gpa, source0, 0, context.diags, &context); // Pass file_id and context
    var c = parser_mod.parse() catch |err| switch (err) {
        error.UnexpectedToken => return, // invalid input is fine for fuzzing
        error.OutOfMemory => std.debug.panic("parser OOM", .{}),
        else => std.debug.panic("parser failed: {}", .{err}),
    };
    defer c.deinit();

    var lower_mod = try lower.Lower.init(gpa, &c, &context, 0); // Pass context
    var a = try (&lower_mod).run();
    defer a.deinit();

    var ctx = checker.Checker.CheckerContext{ .symtab = SymbolStore.init(gpa) };
    var chk = checker.Checker.init(gpa, &context, &pipeline); // Pass context and pipeline
    defer chk.deinit();
    try chk.runAst(a, &ctx);
}

pub export fn fuzz_checker(ptr: [*]const u8, len: usize) callconv(.c) void {
    const data = ptr[0..len];
    _ = testChecker(data) catch |err| {
        std.debug.panic("checker failed: {}\n", .{err});
    };
}
