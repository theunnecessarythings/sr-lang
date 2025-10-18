const std = @import("std");
const lib = @import("compiler");

const JsonValue = std.json.Value;

const Document = struct {
    uri: []u8,
    path: []u8,
    text: []u8,
    version: ?i64 = null,

    fn deinit(self: *Document, allocator: std.mem.Allocator) void {
        allocator.free(self.uri);
        allocator.free(self.path);
        allocator.free(self.text);
    }
};

const Position = struct {
    line: usize,
    character: usize,
};

pub fn run(allocator: std.mem.Allocator, err_writer: *std.io.Writer, out_writer: *std.io.Writer) !void {
    var server = Server{
        .gpa = allocator,
        .err_writer = err_writer,
        .out_writer = out_writer,
        .documents = .empty,
    };
    defer server.deinit();

    try server.loop();
}

const Server = struct {
    gpa: std.mem.Allocator,
    err_writer: *std.io.Writer,
    out_writer: *std.io.Writer,
    documents: std.ArrayList(Document),
    shutdown_requested: bool = false,
    running: bool = true,

    fn deinit(self: *Server) void {
        for (self.documents.items) |*doc| {
            doc.deinit(self.gpa);
        }
        self.documents.deinit(self.gpa);
    }

    fn loop(self: *Server) !void {
        var in_buf: [4096]u8 = undefined;
        var stdin = std.fs.File.stdin().readerStreaming(&in_buf);

        while (self.running) {
            const message_opt = try self.readMessage(&stdin.interface);
            if (message_opt == null) break;
            const message = message_opt.?;
            defer self.gpa.free(message);
            self.handleMessage(message) catch |err| {
                _ = self.err_writer.print("LSP error: {s}\n", .{@errorName(err)}) catch {};
            };
        }
    }

    fn readMessage(self: *Server, reader: anytype) !?[]u8 {
        var buffer: [1024]u8 = undefined;
        var hp = std.http.HeadParser{};
        const size = hp.feed(&buffer);
        const header = buffer[0..size];

        var content_length: ?usize = null;
        var lines = std.mem.splitSequence(u8, header, "\r\n");
        while (lines.next()) |line| {
            if (line.len == 0) continue;
            const trimmed = std.mem.trim(u8, line, " \t");
            if (trimmed.len == 0) continue;
            const prefix = "Content-Length:";
            if (std.mem.startsWith(u8, trimmed, prefix)) {
                const value_slice = std.mem.trim(u8, trimmed[prefix.len..], " \t");
                content_length = try std.fmt.parseInt(usize, value_slice, 10);
            }
        }

        const length = content_length orelse return error.MissingContentLength;
        const body = try self.gpa.alloc(u8, length);
        if (length != 0) {
            try reader.readSliceAll(body);
        }
        return body;
    }

    fn handleMessage(self: *Server, message: []u8) !void {
        var tree = try std.json.parseFromSlice(JsonValue, self.gpa, message, .{});
        defer tree.deinit();
        const root = tree.value;
        if (root != .object) return;
        const obj = root.object;

        const method_ptr = obj.get("method") orelse return;
        if (method_ptr != .string) return;
        const method = method_ptr.string;

        var params_ptr = obj.get("params");
        const id_ptr = obj.get("id");

        if (std.mem.eql(u8, method, "initialize")) {
            if (id_ptr) |id| {
                try self.handleInitialize(id, if (params_ptr) |*p| p else null);
            }
            return;
        }
        if (std.mem.eql(u8, method, "initialized")) {
            return;
        }
        if (std.mem.eql(u8, method, "shutdown")) {
            if (id_ptr) |id| {
                try self.handleShutdown(id);
            }
            return;
        }
        if (std.mem.eql(u8, method, "exit")) {
            self.handleExit();
            return;
        }
        if (std.mem.eql(u8, method, "textDocument/didOpen")) {
            if (params_ptr) |p| try self.handleDidOpen(p);
            return;
        }
        if (std.mem.eql(u8, method, "textDocument/didChange")) {
            if (params_ptr) |p| try self.handleDidChange(p);
            return;
        }
        if (std.mem.eql(u8, method, "textDocument/didClose")) {
            if (params_ptr) |p| try self.handleDidClose(p);
            return;
        }
        if (std.mem.eql(u8, method, "textDocument/didSave")) {
            if (params_ptr) |p| try self.handleDidSave(p);
            return;
        }

        if (id_ptr) |id| {
            try self.sendMethodNotFound(id);
        }
    }

    fn handleInitialize(self: *Server, id_value: JsonValue, params: ?*JsonValue) !void {
        _ = params;
        var payload = std.ArrayList(u8){};
        defer payload.deinit(self.gpa);
        var writer = payload.writer(self.gpa);
        try writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
        var buff: [100]u8 = undefined;
        var iface = writer.adaptToNewApi(&buff).new_interface;
        try std.json.Stringify.value(id_value, .{}, &iface);
        try writer.writeAll(",\"result\":{\"capabilities\":{\"textDocumentSync\":{\"openClose\":true,\"change\":1},\"positionEncoding\":\"utf-8\"}}}");
        try self.sendPayload(payload.items);
    }

    fn handleShutdown(self: *Server, id_value: JsonValue) !void {
        self.shutdown_requested = true;
        var payload = std.ArrayList(u8){};
        defer payload.deinit(self.gpa);
        var writer = payload.writer(self.gpa);
        try writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
        var buff: [100]u8 = undefined;
        var iface = writer.adaptToNewApi(&buff).new_interface;
        try std.json.Stringify.value(id_value, .{}, &iface);
        try writer.writeAll(",\"result\":null}");
        try self.sendPayload(payload.items);
    }

    fn handleExit(self: *Server) void {
        self.running = false;
    }

    fn handleDidOpen(self: *Server, params: JsonValue) !void {
        if (params != .object) return;
        const params_obj = params.object;
        const text_doc_ptr = params_obj.get("textDocument") orelse return;
        if (text_doc_ptr != .object) return;
        const text_doc = text_doc_ptr.object;

        const uri_ptr = text_doc.get("uri") orelse return;
        if (uri_ptr != .string) return;
        const uri = uri_ptr.string;

        const text_ptr = text_doc.get("text") orelse return;
        if (text_ptr != .string) return;
        const text_value = text_ptr.string;

        const version = if (text_doc.getPtr("version")) |ver| parseVersion(ver) else null;

        const text_copy = try self.gpa.dupe(u8, text_value);
        var cleanup_text = true;
        defer if (cleanup_text) self.gpa.free(text_copy);

        const path = try self.uriToPath(uri);
        var cleanup_path = true;
        defer if (cleanup_path) self.gpa.free(path);

        const doc = try self.upsertDocument(uri, path, text_copy, version);
        cleanup_text = false;
        cleanup_path = false;
        try self.publishDocumentDiagnostics(doc);
    }

    fn handleDidChange(self: *Server, params: JsonValue) !void {
        if (params != .object) return;
        const params_obj = params.object;
        const text_doc_ptr = params_obj.get("textDocument") orelse return;
        if (text_doc_ptr != .object) return;
        const text_doc = text_doc_ptr.object;

        const uri_ptr = text_doc.get("uri") orelse return;
        if (uri_ptr != .string) return;
        const uri = uri_ptr.string;

        const version = if (text_doc.getPtr("version")) |ver| parseVersion(ver) else null;

        const changes_ptr = params_obj.get("contentChanges") orelse return;
        if (changes_ptr != .array) return;
        const changes = changes_ptr.array.items;
        if (changes.len == 0) return;
        const change_value = changes[changes.len - 1];
        if (change_value != .object) return;
        const change_obj = change_value.object;
        const text_ptr = change_obj.get("text") orelse return;
        if (text_ptr != .string) return;
        const text_value = text_ptr.string;

        const text_copy = try self.gpa.dupe(u8, text_value);
        var cleanup_text = true;
        defer if (cleanup_text) self.gpa.free(text_copy);

        if (self.findDocumentIndex(uri)) |idx| {
            var doc = &self.documents.items[idx];
            self.gpa.free(doc.text);
            doc.text = text_copy;
            doc.version = version;
            cleanup_text = false;
            try self.publishDocumentDiagnostics(doc);
        } else {
            const path = try self.uriToPath(uri);
            var cleanup_path = true;
            defer if (cleanup_path) self.gpa.free(path);
            const doc = try self.upsertDocument(uri, path, text_copy, version);
            cleanup_path = false;
            cleanup_text = false;
            try self.publishDocumentDiagnostics(doc);
        }
    }

    fn handleDidClose(self: *Server, params: JsonValue) !void {
        if (params != .object) return;
        const params_obj = params.object;
        const text_doc_ptr = params_obj.get("textDocument") orelse return;
        if (text_doc_ptr != .object) return;
        const text_doc = text_doc_ptr.object;
        const uri_ptr = text_doc.get("uri") orelse return;
        if (uri_ptr != .string) return;
        const uri = uri_ptr.string;

        self.removeDocument(uri);
        try self.sendEmptyDiagnostics(uri);
    }

    fn handleDidSave(self: *Server, params: JsonValue) !void {
        if (params != .object) return;
        const params_obj = params.object;
        const text_doc_ptr = params_obj.get("textDocument") orelse return;
        if (text_doc_ptr != .object) return;
        const text_doc = text_doc_ptr.object;
        const uri_ptr = text_doc.get("uri") orelse return;
        if (uri_ptr != .string) return;
        const uri = uri_ptr.string;

        var new_text: ?[]u8 = null;
        if (params_obj.get("text")) |text_ptr| {
            if (text_ptr == .string) {
                new_text = try self.gpa.dupe(u8, text_ptr.string);
            }
        }
        defer if (new_text) |text_copy| self.gpa.free(text_copy);

        if (self.findDocumentIndex(uri)) |idx| {
            var doc = &self.documents.items[idx];
            if (new_text) |text_copy| {
                self.gpa.free(doc.text);
                doc.text = text_copy;
                new_text = null;
            }
            try self.publishDocumentDiagnostics(doc);
        }
    }

    fn upsertDocument(self: *Server, uri: []const u8, path: []u8, text: []u8, version: ?i64) !*Document {
        if (self.findDocumentIndex(uri)) |idx| {
            var doc = &self.documents.items[idx];
            self.gpa.free(doc.path);
            self.gpa.free(doc.text);
            doc.path = path;
            doc.text = text;
            doc.version = version;
            return doc;
        }
        const uri_copy = try self.gpa.dupe(u8, uri);
        errdefer self.gpa.free(uri_copy);
        try self.documents.append(self.gpa, .{ .uri = uri_copy, .path = path, .text = text, .version = version });
        return &self.documents.items[self.documents.items.len - 1];
    }

    fn removeDocument(self: *Server, uri: []const u8) void {
        if (self.findDocumentIndex(uri)) |idx| {
            var removed = self.documents.swapRemove(idx);
            removed.deinit(self.gpa);
        }
    }

    fn findDocumentIndex(self: *Server, uri: []const u8) ?usize {
        for (self.documents.items, 0..) |doc, idx| {
            if (std.mem.eql(u8, doc.uri, uri)) return idx;
        }
        return null;
    }

    fn publishDocumentDiagnostics(self: *Server, doc: *Document) !void {
        var context = lib.compile.Context.init(self.gpa);
        defer context.deinit();

        const file_id = try context.source_manager.setVirtualSourceByPath(doc.path, doc.text);

        var pipeline = lib.pipeline.Pipeline.init(self.gpa, &context);
        const result_opt: ?lib.pipeline.Result = blk: {
            const res = pipeline.runWithImports(doc.path, &.{}, .check) catch |err| {
                if (context.diags.count() == 0) {
                    return err;
                }
                break :blk null;
            };
            break :blk res;
        };

        if (result_opt) |res| {
            if (res.type_info) |ti| {
                if (!context.module_graph.ownsTypeInfo(ti)) {
                    ti.deinit();
                    self.gpa.destroy(ti);
                }
            }
        }

        try self.sendDiagnosticsForFile(doc, &context, file_id);
    }

    fn sendDiagnosticsForFile(self: *Server, doc: *Document, context: *lib.compile.Context, file_id: u32) !void {
        var payload = std.ArrayList(u8){};
        defer payload.deinit(self.gpa);
        var writer = payload.writer(self.gpa);
        try writer.writeAll("{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{\"uri\":");
        var buff: [100]u8 = undefined;
        var iface = writer.adaptToNewApi(&buff).new_interface;
        try std.json.Stringify.value(doc.uri, .{}, &iface);
        try writer.writeAll(",\"diagnostics\":[");

        var first = true;
        for (context.diags.messages.items) |message| {
            if (message.loc.file_id != file_id) continue;
            if (!first) try writer.writeByte(',');
            first = false;

            const text_slice = doc.text;
            const start_offset = if (message.loc.start <= text_slice.len) message.loc.start else text_slice.len;
            const raw_end = if (message.loc.end <= text_slice.len) message.loc.end else text_slice.len;
            const end_offset = if (raw_end < start_offset) start_offset else raw_end;
            const start_pos = Server.computePosition(text_slice, start_offset);
            const end_pos = Server.computePosition(text_slice, end_offset);

            try writer.writeAll("{\"range\":{\"start\":{\"line\":");
            try writer.print("{d},\"character\":{d}}}", .{ start_pos.line, start_pos.character });
            try writer.writeAll(",\"end\":{\"line\":");
            try writer.print("{d},\"character\":{d}}}", .{ end_pos.line, end_pos.character });
            try writer.writeAll(",\"severity\":");
            try writer.print("{d}", .{severityToLsp(message.severity)});
            try writer.writeAll(",\"source\":\"sr-lang\",\"code\":");
            try std.json.Stringify.value(@tagName(message.code), .{}, &iface);
            try writer.writeAll(",\"message\":");

            const base_message = try context.diags.messageToOwnedSlice(self.gpa, message);
            defer self.gpa.free(base_message);
            var final_message = base_message;
            var owned_message: ?[]u8 = null;

            if (message.notes.items.len != 0) {
                var combined = std.ArrayList(u8){};
                defer combined.deinit(self.gpa);
                try combined.appendSlice(self.gpa, base_message);
                for (message.notes.items) |note| {
                    const note_text = try context.diags.noteToOwnedSlice(self.gpa, note);
                    try combined.appendSlice(self.gpa, "\nNote: ");
                    try combined.appendSlice(self.gpa, note_text);
                    self.gpa.free(note_text);
                }
                owned_message = try combined.toOwnedSlice(self.gpa);
                final_message = owned_message.?;
            }

            try std.json.Stringify.value(final_message, .{}, &iface);
            if (owned_message) |owned| {
                self.gpa.free(owned);
            }

            try writer.writeAll("}");
        }

        try writer.writeAll("]}}");
        try self.sendPayload(payload.items);
    }

    fn sendEmptyDiagnostics(self: *Server, uri: []const u8) !void {
        var payload = std.ArrayList(u8){};
        defer payload.deinit(self.gpa);
        var writer = payload.writer(self.gpa);
        try writer.writeAll("{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{\"uri\":");
        var buff: [100]u8 = undefined;
        var iface = writer.adaptToNewApi(&buff).new_interface;
        try std.json.Stringify.value(uri, .{}, &iface);
        try writer.writeAll(",\"diagnostics\":[]}}");
        try self.sendPayload(payload.items);
    }

    fn sendPayload(self: *Server, payload: []const u8) !void {
        try self.out_writer.print("Content-Length: {d}\r\n\r\n", .{payload.len});
        try self.out_writer.writeAll(payload);
        try self.out_writer.flush();
    }

    fn severityToLsp(sev: lib.diagnostics.Severity) u8 {
        return switch (sev) {
            .err => 1,
            .warning => 2,
            .note => 3,
        };
    }

    fn parseVersion(value: *JsonValue) ?i64 {
        return switch (value.*) {
            .integer => value.integer,
            else => null,
        };
    }

    fn uriToPath(self: *Server, uri: []const u8) ![]u8 {
        const prefix = "file://";
        if (!std.mem.startsWith(u8, uri, prefix)) return error.InvalidUri;
        const remainder = uri[prefix.len..];
        var path_part = remainder;
        if (path_part.len > 0 and path_part[0] != '/') {
            if (std.mem.indexOfScalar(u8, path_part, '/')) |idx| {
                path_part = path_part[idx..];
            } else {
                path_part = "";
            }
        }
        if (path_part.len == 0) return error.InvalidUri;
        return try self.decodeUriPath(path_part);
    }

    fn decodeUriPath(self: *Server, encoded: []const u8) ![]u8 {
        var builder = std.ArrayList(u8){};
        defer builder.deinit(self.gpa);
        var i: usize = 0;
        while (i < encoded.len) {
            const c = encoded[i];
            if (c == '%') {
                if (i + 2 >= encoded.len) return error.InvalidUri;
                const value = try decodeHexPair(encoded[i + 1], encoded[i + 2]);
                try builder.append(self.gpa, value);
                i += 3;
            } else {
                try builder.append(self.gpa, c);
                i += 1;
            }
        }
        return builder.toOwnedSlice(self.gpa);
    }

    fn decodeHexPair(hi: u8, lo: u8) !u8 {
        const high = try decodeHexDigit(hi);
        const low = try decodeHexDigit(lo);
        return (high << 4) | low;
    }

    fn decodeHexDigit(c: u8) !u8 {
        return switch (c) {
            '0'...'9' => c - '0',
            'A'...'F' => c - 'A' + 10,
            'a'...'f' => c - 'a' + 10,
            else => error.InvalidUri,
        };
    }

    fn computePosition(text: []const u8, offset: usize) Position {
        var line: usize = 0;
        var last_line_start: usize = 0;
        var index: usize = 0;
        const limit = if (offset > text.len) text.len else offset;
        while (index < limit) {
            const c = text[index];
            if (c == '\n') {
                line += 1;
                last_line_start = index + 1;
            } else if (c == '\r') {
                line += 1;
                if (index + 1 < limit and text[index + 1] == '\n') {
                    index += 1;
                }
                last_line_start = index + 1;
            }
            index += 1;
        }
        const character = limit - last_line_start;
        return .{ .line = line, .character = character };
    }

    fn sendMethodNotFound(self: *Server, id_value: JsonValue) !void {
        var payload = std.ArrayList(u8){};
        defer payload.deinit(self.gpa);
        var writer = payload.writer(self.gpa);
        try writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
        var buff: [100]u8 = undefined;
        var iface = writer.adaptToNewApi(&buff).new_interface;
        try std.json.Stringify.value(id_value, .{}, &iface);
        try writer.writeAll(",\"error\":{\"code\":-32601,\"message\":\"Method not found\"}}");
        try self.sendPayload(payload.items);
    }
};
