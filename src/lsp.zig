const std = @import("std");
const lib = @import("compiler");
const json = std.json;
const ast = lib.ast;
const types = lib.types;
const package_mod = lib.package;

const default_source = "sr-lang";

const Loc = lib.lexer.Token.Loc;
const Severity = lib.diagnostics.Severity;

const LspPosition = struct {
    line: u32,
    character: u32,
};

const LspRange = struct {
    start: LspPosition,
    end: LspPosition,
};

const RelatedInformation = struct {
    location: struct {
        uri: []const u8,
        range: LspRange,
    },
    message: []u8,
};

const LspDiagnostic = struct {
    range: LspRange,
    severity: ?u32 = null,
    source: []const u8 = default_source,
    message: []u8,
    code: ?[]u8 = null,
    relatedInformation: ?[]RelatedInformation = null,
};

const HoverInfo = struct {
    message: []u8,
    range: LspRange,
};

const DocumentStore = struct {
    gpa: std.mem.Allocator,
    map: std.StringHashMapUnmanaged(Document) = .{},

    const Document = struct { text: []u8 };

    fn init(gpa: std.mem.Allocator) DocumentStore {
        return .{ .gpa = gpa };
    }

    fn deinit(self: *DocumentStore) void {
        var it = self.map.iterator();
        while (it.next()) |entry| {
            self.gpa.free(entry.key_ptr.*);
            self.gpa.free(entry.value_ptr.text);
        }
        self.map.deinit(self.gpa);
    }

    fn set(self: *DocumentStore, uri: []const u8, text: []const u8) !void {
        const dup_text = try self.gpa.dupe(u8, text);
        errdefer self.gpa.free(dup_text);

        if (self.map.getPtr(uri)) |doc| {
            self.gpa.free(doc.text);
            doc.text = dup_text;
            return;
        }

        const dup_uri = try self.gpa.dupe(u8, uri);
        errdefer self.gpa.free(dup_uri);
        try self.map.put(self.gpa, dup_uri, .{ .text = dup_text });
    }

    fn get(self: *DocumentStore, uri: []const u8) ?[]u8 {
        if (self.map.getPtr(uri)) |doc| {
            return doc.text;
        }
        return null;
    }

    fn remove(self: *DocumentStore, uri: []const u8) void {
        if (self.map.fetchRemove(uri)) |kv| {
            self.gpa.free(kv.key);
            self.gpa.free(kv.value.text);
        }
    }
};

pub fn run(gpa: std.mem.Allocator) !void {
    var in_buf: [64 * 1024]u8 = undefined;
    var out_buf: [64 * 1024]u8 = undefined;
    var in_r = std.fs.File.stdin().readerStreaming(&in_buf);
    var out_w = std.fs.File.stdout().writerStreaming(&out_buf);
    const In: *std.Io.Reader = &in_r.interface;
    const Out: *std.Io.Writer = &out_w.interface;
    var docs = DocumentStore.init(gpa);
    defer docs.deinit();

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
            if (req.params) |p| try onDidOpen(Out, gpa, &docs, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/didChange")) {
            if (req.params) |p| try onDidChange(Out, gpa, &docs, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/didClose")) {
            if (req.params) |p| try onDidClose(Out, gpa, &docs, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/hover")) {
            if (req.params) |p| try onHover(Out, gpa, &docs, req.id orelse 0, p);
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
            serverInfo: struct { name: []const u8 = "sr_lsp", version: []const u8 = "0.1.0" } = .{},
        } = .{},
    };
    try writeJson(out, gpa, Resp{ .id = id });
}

fn onDidOpen(out: *std.Io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, params: json.Value) !void {
    const P = struct {
        textDocument: struct { uri: []const u8, text: []const u8 },
    };
    var p = try json.parseFromValue(P, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();
    try docs.set(p.value.textDocument.uri, p.value.textDocument.text);
    try publishDiagnostics(out, gpa, docs, p.value.textDocument.uri);
}

fn onDidChange(out: *std.Io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, params: json.Value) !void {
    const P = struct {
        textDocument: struct { uri: []const u8 },
        contentChanges: []const struct { text: []const u8 },
    };
    var p = try json.parseFromValue(P, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();
    if (p.value.contentChanges.len == 0) return;
    try docs.set(p.value.textDocument.uri, p.value.contentChanges[0].text);
    try publishDiagnostics(out, gpa, docs, p.value.textDocument.uri);
}

fn onDidClose(out: *std.Io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, params: json.Value) !void {
    const P = struct {
        textDocument: struct { uri: []const u8 },
    };
    var p = try json.parseFromValue(P, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();
    const uri = p.value.textDocument.uri;
    docs.remove(uri);
    const Msg = struct {
        jsonrpc: []const u8 = "2.0",
        method: []const u8 = "textDocument/publishDiagnostics",
        params: struct { uri: []const u8, diagnostics: []const LspDiagnostic },
    };
    const empty_diags = [_]LspDiagnostic{};
    try writeJson(out, gpa, Msg{ .params = .{ .uri = uri, .diagnostics = &empty_diags } });
}

fn onHover(out: *std.Io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, id: u64, params: json.Value) !void {
    const P = struct {
        textDocument: struct { uri: []const u8 },
        position: struct { line: u32, character: u32 },
    };
    var p = try json.parseFromValue(P, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();

    const uri = p.value.textDocument.uri;
    const text = docs.get(uri) orelse {
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
        return;
    };

    const offset = positionToOffset(text, p.value.position.line, p.value.position.character);
    const hover_info = try computeHover(gpa, uri, text, offset);

    const Resp = struct {
        jsonrpc: []const u8 = "2.0",
        id: u64,
        result: ?struct {
            contents: struct { kind: []const u8 = "markdown", value: []const u8 },
            range: LspRange,
        } = null,
    };

    if (hover_info) |info| {
        defer gpa.free(info.message);
        try writeJson(out, gpa, Resp{
            .id = id,
            .result = .{
                .contents = .{ .value = info.message },
                .range = info.range,
            },
        });
    } else {
        try writeJson(out, gpa, Resp{ .id = id, .result = null });
    }
}

fn respondCompletion(out: *std.Io.Writer, gpa: std.mem.Allocator, id: u64) !void {
    const Item = struct { label: []const u8, kind: u32 = 14, detail: []const u8 = "test_lsp" };
    const Resp = struct { jsonrpc: []const u8 = "2.0", id: u64, result: []const Item };
    const items = [_]Item{ .{ .label = "hello" }, .{ .label = "world" } };
    try writeJson(out, gpa, Resp{ .id = id, .result = &items });
}

fn publishDiagnostics(out: *std.Io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, uri: []const u8) !void {
    const text_mut = docs.get(uri) orelse {
        const Msg = struct {
            jsonrpc: []const u8 = "2.0",
            method: []const u8 = "textDocument/publishDiagnostics",
            params: struct { uri: []const u8, diagnostics: []const LspDiagnostic },
        };
        const empty_diags = [_]LspDiagnostic{};
        try writeJson(out, gpa, Msg{ .params = .{ .uri = uri, .diagnostics = &empty_diags } });
        return;
    };
    const text: []const u8 = text_mut;

    var context = lib.compile.Context.init(gpa);
    defer context.deinit();

    const path = try fileUriToPath(gpa, uri);
    defer gpa.free(path);

    const file_id = try context.source_manager.setVirtualSourceByPath(path, text);
    var pipeline = lib.pipeline.Pipeline.init(gpa, &context);

    _ = pipeline.run(path, &.{}, .check) catch |err| switch (err) {
        error.ParseFailed, error.TypeCheckFailed, error.LoweringFailed, error.TirLoweringFailed, error.TooManyErrors => {},
        else => {
            std.debug.print("[lsp] pipeline error: {s}\n", .{@errorName(err)});
        },
    };

    var diags = std.ArrayList(LspDiagnostic){};
    defer {
        for (diags.items) |diag| {
            gpa.free(diag.message);
            if (diag.code) |code_bytes| gpa.free(code_bytes);
            if (diag.relatedInformation) |rel_slice| {
                for (rel_slice) |rel| {
                    gpa.free(rel.message);
                }
                gpa.free(rel_slice);
            }
        }
        diags.deinit(gpa);
    }

    for (context.diags.messages.items) |message| {
        if (message.loc.file_id != file_id) continue;

        const msg_text = context.diags.messageToOwnedSlice(gpa, message) catch |err| {
            std.debug.print("[lsp] failed to render diagnostic: {s}\n", .{@errorName(err)});
            continue;
        };

        var diag = LspDiagnostic{
            .range = locToRange(text, message.loc),
            .severity = severityToLsp(message.severity),
            .message = msg_text,
        };

        diag.code = std.fmt.allocPrint(gpa, "{s}", .{@tagName(message.code)}) catch |err| {
            std.debug.print("[lsp] failed to format diagnostic code: {s}\n", .{@errorName(err)});
            gpa.free(diag.message);
            continue;
        };

        var related = std.ArrayList(RelatedInformation){};
        defer related.deinit(gpa);

        for (message.notes.items) |note| {
            const note_loc = note.loc orelse continue;
            if (note_loc.file_id != file_id) continue;

            const note_msg = context.diags.noteToOwnedSlice(gpa, note) catch |err| {
                std.debug.print("[lsp] failed to render note: {s}\n", .{@errorName(err)});
                continue;
            };

            try related.append(gpa, .{
                .location = .{ .uri = uri, .range = locToRange(text, note_loc) },
                .message = note_msg,
            });
        }

        if (related.items.len != 0) {
            diag.relatedInformation = related.toOwnedSlice(gpa) catch |err| {
                std.debug.print("[lsp] failed to materialize related information: {s}\n", .{@errorName(err)});
                for (related.items) |rel| {
                    gpa.free(rel.message);
                }
                gpa.free(diag.code.?);
                gpa.free(diag.message);
                diag.relatedInformation = null;
                continue;
            };
        }

        try diags.append(gpa, diag);
    }

    const Msg = struct {
        jsonrpc: []const u8 = "2.0",
        method: []const u8 = "textDocument/publishDiagnostics",
        params: struct { uri: []const u8, diagnostics: []const LspDiagnostic },
    };
    try writeJson(out, gpa, Msg{ .params = .{ .uri = uri, .diagnostics = diags.items } });
}

fn fileUriToPath(gpa: std.mem.Allocator, uri: []const u8) ![]u8 {
    if (!std.mem.startsWith(u8, uri, "file://")) {
        return gpa.dupe(u8, uri);
    }

    var rest = uri["file://".len..];

    if (rest.len >= 2 and rest[0] == '/' and rest[1] == '/') {
        rest = rest[2..];
    }

    if (std.mem.indexOfScalar(u8, rest, '/')) |idx| {
        rest = rest[idx..];
    } else {
        rest = "";
    }

    var out_buf = std.ArrayList(u8){};
    errdefer out_buf.deinit(gpa);

    var i: usize = 0;
    while (i < rest.len) : (i += 1) {
        const ch = rest[i];
        if (ch == '%' and i + 2 < rest.len) {
            if (hexDigit(rest[i + 1])) |hi| {
                if (hexDigit(rest[i + 2])) |lo| {
                    try out_buf.append(gpa, hi << 4 | lo);
                    i += 2;
                    continue;
                }
            }
        }

        try out_buf.append(gpa, ch);
    }

    if (out_buf.items.len == 0) {
        try out_buf.append(gpa, '/');
    }

    return out_buf.toOwnedSlice(gpa);
}

fn hexDigit(c: u8) ?u8 {
    return switch (c) {
        '0'...'9' => c - '0',
        'a'...'f' => c - 'a' + 10,
        'A'...'F' => c - 'A' + 10,
        else => null,
    };
}

fn locToRange(text: []const u8, loc: Loc) LspRange {
    const start_idx = clampOffset(text, loc.start);
    const raw_end = if (loc.end > loc.start) loc.end else loc.start;
    const end_idx = clampOffset(text, raw_end);

    return .{
        .start = offsetToPosition(text, start_idx),
        .end = offsetToPosition(text, end_idx),
    };
}

fn clampOffset(text: []const u8, offset: usize) usize {
    if (offset > text.len) return text.len;
    return offset;
}

fn offsetToPosition(text: []const u8, offset: usize) LspPosition {
    var line: u32 = 0;
    var col: u32 = 0;

    var i: usize = 0;
    while (i < offset and i < text.len) : (i += 1) {
        switch (text[i]) {
            '\n' => {
                line += 1;
                col = 0;
            },
            '\r' => {
                line += 1;
                col = 0;
                if (i + 1 < offset and text[i + 1] == '\n') {
                    i += 1;
                }
            },
            else => col += 1,
        }
    }

    return .{ .line = line, .character = col };
}

fn severityToLsp(sev: Severity) ?u32 {
    return switch (sev) {
        .err => 1,
        .warning => 2,
        .note => 3,
    };
}

fn computeHover(gpa: std.mem.Allocator, uri: []const u8, text: []const u8, offset_in: usize) !?HoverInfo {
    var context = lib.compile.Context.init(gpa);
    defer context.deinit();

    const path = try fileUriToPath(gpa, uri);
    defer gpa.free(path);

    const offset = if (offset_in > text.len) text.len else offset_in;
    const file_id = try context.source_manager.setVirtualSourceByPath(path, text);
    var pipeline = lib.pipeline.Pipeline.init(gpa, &context);

    _ = pipeline.run(path, &.{}, .check) catch |err| switch (err) {
        error.ParseFailed, error.TypeCheckFailed, error.LoweringFailed, error.TirLoweringFailed, error.TooManyErrors => return null,
        else => {
            std.debug.print("[lsp] hover pipeline error: {s}\n", .{@errorName(err)});
            return null;
        },
    };
    if (context.diags.anyErrors()) return null;

    const ast_unit = findAstForFile(&context.compilation_unit, file_id) orelse return null;
    const expr_id = findExprAt(ast_unit, offset) orelse return null;
    const loc = exprLoc(ast_unit, expr_id);
    const type_id = getExprType(ast_unit, expr_id) orelse return null;

    var msg_builder = std.Io.Writer.Allocating.init(gpa);
    defer msg_builder.deinit();
    try msg_builder.writer.print("```sr\n", .{});
    try context.type_store.fmt(type_id, &msg_builder.writer);
    try msg_builder.writer.print("\n```", .{});
    const message = try msg_builder.toOwnedSlice();

    return HoverInfo{
        .message = message,
        .range = locToRange(text, loc),
    };
}

fn findAstForFile(unit: *package_mod.CompilationUnit, file_id: u32) ?*ast.Ast {
    var pkg_iter = unit.packages.iterator();
    while (pkg_iter.next()) |pkg| {
        var source_iter = pkg.value_ptr.sources.iterator();
        while (source_iter.next()) |entry| {
            if (entry.value_ptr.file_id == file_id) {
                if (entry.value_ptr.ast) |ast_unit| return ast_unit;
                return null;
            }
        }
    }
    return null;
}

fn findExprAt(ast_unit: *ast.Ast, offset: usize) ?ast.ExprId {
    const kinds = ast_unit.exprs.index.kinds.items;
    var best: ?ast.ExprId = null;
    var best_span: usize = std.math.maxInt(usize);

    var i: usize = 0;
    while (i < kinds.len) : (i += 1) {
        const expr_id = ast.ExprId.fromRaw(@intCast(i));
        const loc = exprLoc(ast_unit, expr_id);
        const start = loc.start;
        const end = if (loc.end > loc.start) loc.end else loc.start + 1;
        if (offset < start or offset >= end) continue;
        const span = end - start;
        if (span < best_span) {
            best_span = span;
            best = expr_id;
        }
    }
    return best;
}

fn exprLoc(ast_unit: *ast.Ast, expr_id: ast.ExprId) Loc {
    const kinds = ast_unit.exprs.index.kinds.items;
    const kind = kinds[expr_id.toRaw()];
    return switch (kind) {
        inline else => |k| blk: {
            const row = ast_unit.exprs.get(k, expr_id);
            break :blk ast_unit.exprs.locs.get(row.loc);
        },
    };
}

fn getExprType(ast_unit: *ast.Ast, expr_id: ast.ExprId) ?types.TypeId {
    const idx = expr_id.toRaw();
    if (idx >= ast_unit.type_info.expr_types.items.len) return null;
    return ast_unit.type_info.expr_types.items[idx];
}

fn positionToOffset(text: []const u8, target_line: u32, target_character: u32) usize {
    var line: u32 = 0;
    var idx: usize = 0;
    var last_line_start: usize = 0;

    while (idx < text.len and line < target_line) : (idx += 1) {
        const c = text[idx];
        if (c == '\n') {
            line += 1;
            last_line_start = idx + 1;
        } else if (c == '\r') {
            line += 1;
            last_line_start = idx + 1;
            if (idx + 1 < text.len and text[idx + 1] == '\n') idx += 1;
        }
    }

    if (line != target_line) return text.len;

    idx = last_line_start;
    var character: u32 = 0;
    while (idx < text.len and character < target_character) : (idx += 1) {
        const c = text[idx];
        if (c == '\n') break;
        if (c == '\r') {
            if (idx + 1 < text.len and text[idx + 1] == '\n') {
                idx += 1;
            }
            break;
        }
        character += 1;
    }

    return idx;
}
