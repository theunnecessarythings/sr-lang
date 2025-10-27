const std = @import("std");
const lib = @import("compiler");
const json = std.json;

pub fn run(gpa: std.mem.Allocator) !void {
    var in_buf: [64 * 1024]u8 = undefined;
    var out_buf: [64 * 1024]u8 = undefined;
    var in_r = std.fs.File.stdin().readerStreaming(&in_buf);
    var out_w = std.fs.File.stdout().writerStreaming(&out_buf);
    const In: *std.Io.Reader = &in_r.interface;
    const Out: *std.Io.Writer = &out_w.interface;

    while (true) {
        var hdr = try readHeaders(gpa, In);
        defer gpa.free(hdr.buf);

        const cl = try parseContentLength(hdr.buf[0..hdr.body_start]);
        var body = try gpa.alloc(u8, cl);
        defer gpa.free(body);

        const prefix = hdr.buf[hdr.body_start..];
        var off: usize = 0;
        if (prefix.len != 0) {
            const to_copy = @min(prefix.len, body.len);
            @memcpy(body[0..to_copy], prefix[0..to_copy]);
            off = to_copy;
        }

        try readExact(In, body[off..]);

        const Request = struct {
            jsonrpc: []const u8,
            method: []const u8,
            id: ?u64 = null,
            params: ?json.Value = null,
        };

        var parsed = json.parseFromSlice(Request, gpa, body, .{ .ignore_unknown_fields = true }) catch |e| {
            std.debug.print("[lsp] json parse error: {s}\n", .{@errorName(e)});
            continue;
        };
        defer parsed.deinit();
        const req = parsed.value;

        // --- dispatch ---
        if (std.mem.eql(u8, req.method, "initialize")) {
            try respondInitialize(Out, gpa, req.id orelse 0);
        } else if (std.mem.eql(u8, req.method, "initialized")) {
            // no-op
        } else if (std.mem.eql(u8, req.method, "shutdown")) {
            try writeJson(Out, gpa, .{ .jsonrpc = "2.0", .id = req.id orelse 0, .result = null });
        } else if (std.mem.eql(u8, req.method, "exit")) {
            return;
        } else if (std.mem.eql(u8, req.method, "textDocument/didOpen")) {
            if (req.params) |p| try onDidOpen(Out, gpa, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/didChange")) {
            if (req.params) |p| try onDidChange(Out, gpa, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/hover")) {
            if (req.params) |p| try onHover(Out, gpa, req.id orelse 0, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/completion")) {
            try respondCompletion(Out, gpa, req.id orelse 0);
        } else {
            if (req.id) |rid| try writeJson(Out, gpa, .{ .jsonrpc = "2.0", .id = rid, .result = null });
        }
    }
}

const HeaderRead = struct {
    buf: []u8, // header bytes + possibly some of the body already read
    body_start: usize, // index within buf where the body begins
};

fn readHeaders(A: std.mem.Allocator, In: *std.Io.Reader) !HeaderRead {
    var acc = std.ArrayList(u8){};
    errdefer acc.deinit(A);

    var tmp: [4096]u8 = undefined;

    while (true) {
        var b = [_][]u8{tmp[0..]};
        const n = try In.readVec(&b);
        if (n == 0) return error.EndOfStream;
        try acc.appendSlice(A, tmp[0..n]);

        if (findHeaderEnd(acc.items)) |start| {
            // split position is start (index after the terminator)
            const buf = try acc.toOwnedSlice(A);
            return HeaderRead{ .buf = buf, .body_start = start };
        }

        // very defensive cap for pathological clients
        if (acc.items.len > 1 * 1024 * 1024) return error.ResourceExhausted;
    }
}

fn findHeaderEnd(buf: []const u8) ?usize {
    if (std.mem.indexOf(u8, buf, "\r\n\r\n")) |i| return i + 4;
    if (std.mem.indexOf(u8, buf, "\n\n")) |i| return i + 2;
    return null;
}

fn parseContentLength(header_bytes: []const u8) !usize {
    // Split on LF; trim trailing CR; case-insensitive key match
    var it = std.mem.splitScalar(u8, header_bytes, '\n');
    var seen = false;
    var content_len: usize = 0;

    while (it.next()) |line_raw| {
        const line = std.mem.trimRight(u8, line_raw, "\r");
        if (line.len == 0) continue;
        if (std.ascii.startsWithIgnoreCase(line, "content-length:")) {
            const after = std.mem.trim(u8, line["content-length:".len..], " \t");
            content_len = try std.fmt.parseInt(usize, after, 10);
            seen = true;
        }
    }
    if (!seen) return error.Invalid;
    return content_len;
}

fn readExact(in: *std.Io.Reader, dest: []u8) !void {
    var off: usize = 0;
    while (off < dest.len) {
        var b = [_][]u8{dest[off..]};
        const n = try in.readVec(&b);
        if (n == 0) return error.EndOfStream;
        off += n;
    }
}

// ================== JSON send helpers ==================
fn sendMessage(out: *std.Io.Writer, payload: []const u8) !void {
    try out.print("Content-Length: {d}\r\n\r\n", .{payload.len});
    try out.writeAll(payload);
    try out.flush();
}

fn writeJson(out: *std.Io.Writer, gpa: std.mem.Allocator, value: anytype) !void {
    var allocw = std.Io.Writer.Allocating.init(gpa);
    defer allocw.deinit();
    var s = json.Stringify{ .writer = &allocw.writer, .options = .{ .whitespace = .minified } };
    try s.write(value);
    try sendMessage(out, allocw.written());
}

// ================== LSP handlers ==================

fn respondInitialize(out: *std.Io.Writer, gpa: std.mem.Allocator, id: u64) !void {
    const Caps = struct {
        textDocumentSync: u32 = 1, // Full sync (simple)
        hoverProvider: bool = true,
        completionProvider: struct { triggerCharacters: []const []const u8 } = .{ .triggerCharacters = &.{"."} },
        positionEncoding: []const u8 = "utf-16",
    };
    const Resp = struct {
        jsonrpc: []const u8 = "2.0",
        id: u64,
        result: struct {
            capabilities: Caps = .{},
            serverInfo: struct { name: []const u8 = "test_lsp", version: []const u8 = "0.1.0" } = .{},
        } = .{},
    };
    try writeJson(out, gpa, Resp{ .id = id });
}

fn onDidOpen(out: *std.Io.Writer, gpa: std.mem.Allocator, params: json.Value) !void {
    const P = struct {
        textDocument: struct { uri: []const u8, text: []const u8 },
    };
    var p = try json.parseFromValue(P, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();
    try publishDiagnostics(out, gpa, p.value.textDocument.uri, p.value.textDocument.text);
}

fn onDidChange(out: *std.Io.Writer, gpa: std.mem.Allocator, params: json.Value) !void {
    const P = struct {
        textDocument: struct { uri: []const u8 },
        contentChanges: []const struct { text: []const u8 },
    };
    var p = try json.parseFromValue(P, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();
    if (p.value.contentChanges.len == 0) return;
    try publishDiagnostics(out, gpa, p.value.textDocument.uri, p.value.contentChanges[0].text);
}

fn onHover(out: *std.Io.Writer, gpa: std.mem.Allocator, id: u64, params: json.Value) !void {
    _ = params; // toy
    const Resp = struct {
        jsonrpc: []const u8 = "2.0",
        id: u64,
        result: ?struct { contents: struct { kind: []const u8 = "markdown", value: []const u8 } } = null,
    };
    try writeJson(out, gpa, Resp{ .id = id, .result = .{ .contents = .{ .value = "**hover**: test_lsp" } } });
}

fn respondCompletion(out: *std.Io.Writer, gpa: std.mem.Allocator, id: u64) !void {
    const Item = struct { label: []const u8, kind: u32 = 14, detail: []const u8 = "test_lsp" };
    const Resp = struct { jsonrpc: []const u8 = "2.0", id: u64, result: []const Item };
    const items = [_]Item{ .{ .label = "hello" }, .{ .label = "world" } };
    try writeJson(out, gpa, Resp{ .id = id, .result = &items });
}

fn publishDiagnostics(out: *std.Io.Writer, gpa: std.mem.Allocator, uri: []const u8, text: []const u8) !void {
    const Pos = struct { line: u32, character: u32 };
    const Range = struct { start: Pos, end: Pos };
    const Diag = struct {
        range: Range,
        severity: u32 = 2,
        message: []const u8 = "Avoid 'foo'",
        source: []const u8 = "test_lsp",
    };

    var list = std.ArrayList(Diag){};
    defer list.deinit(gpa);

    var line: u32 = 0;
    var col: u32 = 0;
    var i: usize = 0;
    while (i < text.len) : (i += 1) {
        const c = text[i];
        if (c == '\n') {
            line += 1;
            col = 0;
            continue;
        }
        if (i + 3 <= text.len and std.mem.eql(u8, text[i .. i + 3], "foo")) {
            try list.append(gpa, .{ .range = .{ .start = .{ .line = line, .character = col }, .end = .{ .line = line, .character = col + 3 } } });
            i += 2;
            col += 3;
        } else {
            col += 1;
        }
    }

    const Msg = struct {
        jsonrpc: []const u8 = "2.0",
        method: []const u8 = "textDocument/publishDiagnostics",
        params: struct { uri: []const u8, diagnostics: []const Diag },
    };
    try writeJson(out, gpa, Msg{ .params = .{ .uri = uri, .diagnostics = list.items } });
}
