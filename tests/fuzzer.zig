const compiler = @import("compiler");
const std = @import("std");
const lexer = compiler.lexer;
const parser_v2 = compiler.parser_v2;
const diagnostics = compiler.diagnostics;

fn testLexer(data: []const u8) !void {
    const source0 = try std.heap.page_allocator.dupeZ(u8, data);
    defer std.heap.page_allocator.free(source0);
    var tokenizer = lexer.Tokenizer.init(source0, .semi);
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

    const source0 = try gpa.dupeZ(u8, data);
    var diags = diagnostics.Diagnostics.init(gpa);
    defer diags.deinit();

    var parser = parser_v2.Parser.init(gpa, source0, &diags);
    var tree = parser.parse() catch |err| switch (err) {
        error.UnexpectedToken => {
            try std.testing.expect(diags.anyErrors());
            return;
        },
        error.OutOfMemory => std.debug.panic("parser OOM", .{}),
        else => std.debug.panic("parser failed: {}", .{err}),
    };
    defer tree.deinit();

    // if (diags.anyErrors()) return;

    try std.testing.expectEqual(lexer.Token.Tag.eof, parser.cur.tag);
}

pub export fn fuzz_parser(ptr: [*]const u8, len: usize) callconv(.c) void {
    const data = ptr[0..len];
    _ = testParser(data) catch |err| {
        std.debug.panic("parser failed: {}\n", .{err});
    };
}
