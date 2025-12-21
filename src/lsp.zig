const std = @import("std");
const lib = @import("compiler");
const json = std.json;
const ast = lib.ast;
const types = lib.types;
const package_mod = lib.package;

const default_source = "sr-lang";

const Loc = lib.lexer.Token.Loc;
const Severity = lib.diagnostics.Severity;

/// Cached semantic/AST data for a document version.
const AnalysisCache = struct {
    gpa: std.mem.Allocator,
    map: std.StringHashMapUnmanaged(Entry) = .{},

    const Entry = struct {
        version: u64,
        context: lib.compile.Context,
        path: []const u8,
        file_id: u32,
        ast_unit: ?*ast.Ast,
        resolution_map: std.AutoArrayHashMap(u32, Symbol),

        fn deinit(self: *Entry, gpa: std.mem.Allocator) void {
            self.resolution_map.deinit();
            gpa.free(self.path);
            self.context.deinit();
        }
    };

    fn init(gpa: std.mem.Allocator) AnalysisCache {
        return .{ .gpa = gpa };
    }

    fn deinit(self: *AnalysisCache) void {
        var it = self.map.iterator();
        while (it.next()) |entry| {
            self.gpa.free(entry.key_ptr.*);
            const value_ptr = @constCast(entry.value_ptr);
            value_ptr.deinit(self.gpa);
        }
        self.map.deinit(self.gpa);
    }

    fn remove(self: *AnalysisCache, uri: []const u8) void {
        if (self.map.fetchRemove(uri)) |kv| {
            self.gpa.free(kv.key);
            var val = kv.value;
            val.deinit(self.gpa);
        }
    }

    fn ensure(self: *AnalysisCache, uri: []const u8, doc: *const DocumentStore.Document) !?*Entry {
        if (self.map.getPtr(uri)) |entry| {
            if (entry.version == doc.version) {
                return entry;
            }
        }

        // Only remove if the version is stale or it doesn't exist
        self.remove(uri);

        var context: lib.compile.Context = .init(self.gpa);
        errdefer context.deinit();

        const path = try fileUriToPath(self.gpa, uri);
        errdefer self.gpa.free(path);

        const file_id = try context.source_manager.setVirtualSourceByPath(path, doc.text);
        var pipeline: lib.pipeline.Pipeline = .init(self.gpa, &context);

        _ = pipeline.run(path, &.{}, .check, null, null) catch |err| switch (err) {
            error.ParseFailed,
            error.TypeCheckFailed,
            error.LoweringFailed,
            error.TirLoweringFailed,
            error.TooManyErrors,
            => {},
            else => {
                std.debug.print("[lsp] pipeline error: {s}\n", .{@errorName(err)});
            },
        };

        const ast_unit_opt = findAstForFile(&context.compilation_unit, file_id);
        var resolution_map: std.AutoArrayHashMap(u32, Symbol) = undefined;
        if (ast_unit_opt) |ast_unit| {
            resolution_map = try buildResolutionMap(self.gpa, ast_unit);
        } else {
            resolution_map = .init(self.gpa);
        }
        errdefer resolution_map.deinit();

        const entry = Entry{
            .version = doc.version,
            .context = context,
            .path = path,
            .file_id = file_id,
            .ast_unit = ast_unit_opt,
            .resolution_map = resolution_map,
        };

        const dup_uri = try self.gpa.dupe(u8, uri);
        errdefer self.gpa.free(dup_uri);
        try self.map.put(self.gpa, dup_uri, entry);
        return self.map.getPtr(uri);
    }
};

/// Line/character pair that identifies a position inside a text buffer.
const LspPosition = struct {
    /// Zero-based line number.
    line: u32,
    /// Zero-based column offset within the line.
    character: u32,
};

/// Inclusive range on a text document defined by two positions.
const LspRange = struct {
    /// Start position of the range.
    start: LspPosition,
    /// End position (exclusive) for the range.
    end: LspPosition,
};

/// Represents a text replacement inside a document.
const TextEdit = struct {
    /// Range covered by the edit.
    range: LspRange,
    /// Replacement text that should be inserted.
    newText: []const u8,
};

const emptyTextEdits: []const TextEdit = &[_]TextEdit{};

/// Supplemental diagnostic locations reported alongside the main diagnostic.
const RelatedInformation = struct {
    /// Location and URI describing the related range.
    location: struct {
        /// Document URI where the related issue resides.
        uri: []const u8,
        /// Range within `uri` that the related issue covers.
        range: LspRange,
    },
    /// Message describing the related issue.
    message: []u8,
};

/// LSP diagnostic payload describing an issue in a document.
const LspDiagnostic = struct {
    /// Range where the diagnostic applies.
    range: LspRange,
    /// Optional severity (see LSP spec).
    severity: ?u32 = null,
    /// Source label for this diagnostic.
    source: []const u8 = default_source,
    /// Human-readable diagnostic message.
    message: []u8,
    /// Optional diagnostic code identifier.
    code: ?[]u8 = null,
    /// Additional related diagnostic locations.
    relatedInformation: ?[]RelatedInformation = null,
};

/// Data carried when responding to hover requests.
const HoverInfo = struct {
    /// Hover text rendered in the editor.
    message: []u8,
    /// Range associated with the hover.
    range: LspRange,
};

const TextDocumentIdentifier = struct { uri: []const u8 };
const VersionedTextDocumentIdentifier = struct { uri: []const u8, version: u64 };
const TextDocumentParams = struct { textDocument: TextDocumentIdentifier };
const TextDocumentPositionParams = struct {
    textDocument: TextDocumentIdentifier,
    position: LspPosition,
};
const ReferenceParams = struct {
    textDocument: TextDocumentIdentifier,
    position: LspPosition,
    context: struct { includeDeclaration: bool },
};
const DocumentSymbolParams = struct {
    textDocument: TextDocumentIdentifier,
};
const SignatureHelpParams = struct {
    textDocument: TextDocumentIdentifier,
    position: LspPosition,
    context: ?struct {
        triggerKind: u32,
        triggerCharacter: ?[]const u8,
        isRetrigger: bool,
    } = null,
};
const SignatureHelp = struct {
    signatures: []const SignatureInformation,
    activeSignature: ?u32 = 0,
    activeParameter: ?u32 = 0,
};
const SignatureInformation = struct {
    label: []const u8,
    documentation: ?[]const u8 = null,
    parameters: ?[]const ParameterInformation = null,
};
const ParameterInformation = struct {
    label: []const u8,
    documentation: ?[]const u8 = null,
};
const CodeActionParams = struct {
    textDocument: TextDocumentIdentifier,
    range: LspRange,
    context: struct {
        diagnostics: []const LspDiagnostic,
    },
};
const DocumentSymbol = struct {
    name: []const u8,
    detail: ?[]const u8 = null,
    kind: u32,
    range: LspRange,
    selectionRange: LspRange,
    children: ?[]const DocumentSymbol = null,
};
const SymbolKind = enum(u32) {
    File = 1,
    Module = 2,
    Namespace = 3,
    Package = 4,
    Class = 5,
    Method = 6,
    Property = 7,
    Field = 8,
    Constructor = 9,
    Enum = 10,
    Interface = 11,
    Function = 12,
    Variable = 13,
    Constant = 14,
    String = 15,
    Number = 16,
    Boolean = 17,
    Array = 18,
    Object = 19,
    Key = 20,
    Null = 21,
    EnumMember = 22,
    Struct = 23,
    Event = 24,
    Operator = 25,
    TypeParameter = 26,
};
const RenameParams = struct {
    textDocument: TextDocumentIdentifier,
    position: LspPosition,
    newName: []const u8,
};
const TextDocumentOpenParams = struct {
    textDocument: struct {
        uri: []const u8,
        text: []const u8,
        version: u64,
    },
};
const TextDocumentChangeParams = struct {
    textDocument: VersionedTextDocumentIdentifier,
    contentChanges: []const struct { text: []const u8 },
};

const semantic_token_types = [_][]const u8{
    "keyword",
    "string",
    "number",
    "comment",
    "function",
    "type",
    "namespace",
    "variable",
    "property",
    "parameter",
    "enumMember",
    "enum",
    "struct",
    "operator",
};

const semantic_token_modifiers = [_][]const u8{};

/// Canonical semantic token categories for syntax highlighting.
const SemanticTokenKind = enum(u8) {
    keyword,
    string,
    number,
    comment,
    function,
    type,
    namespace,
    variable,
    property,
    parameter,
    enum_member,
    @"enum",
    @"struct",
    operator,
};

/// In-memory store for LSP document contents keyed by URI.
const DocumentStore = struct {
    /// Allocator backing stored document buffers.
    gpa: std.mem.Allocator,
    /// Mapping from URI strings to document entries.
    map: std.StringHashMapUnmanaged(Document) = .{},

    /// Entry that owns the buffered text for a document.
    const Document = struct {
        /// Owned text bytes for the document.
        text: []u8,
        /// Cached line starts for fast position math.
        line_starts: []usize,
        /// Incrementing version used to invalidate analysis cache.
        version: u64,
        /// Zero-terminated copy of text for lexer convenience.
        z_text: [:0]u8,
    };

    /// Create an empty document store backed by `gpa`.
    fn init(gpa: std.mem.Allocator) DocumentStore {
        return .{ .gpa = gpa };
    }

    /// Release all stored document bytes and free the hash map.
    fn deinit(self: *DocumentStore) void {
        var it = self.map.iterator();
        while (it.next()) |entry| {
            self.gpa.free(entry.key_ptr.*);
            self.gpa.free(entry.value_ptr.text);
            self.gpa.free(entry.value_ptr.line_starts);
        }
        self.map.deinit(self.gpa);
    }

    /// Associate `text` with `uri`, replacing existing content if present.
    fn set(self: *DocumentStore, uri: []const u8, text: []const u8, client_version: u64) !void {
        const dup_text = try self.gpa.dupe(u8, text);
        errdefer self.gpa.free(dup_text);
        const line_starts = try buildLineStarts(self.gpa, dup_text);
        errdefer self.gpa.free(line_starts);
        const z_text = try buildZeroTerminated(self.gpa, dup_text);
        errdefer self.gpa.free(z_text);

        if (self.map.getPtr(uri)) |doc| {
            self.gpa.free(doc.text);
            self.gpa.free(doc.line_starts);
            self.gpa.free(doc.z_text);
            doc.text = dup_text;
            doc.line_starts = line_starts;
            doc.z_text = z_text;
            doc.version = client_version;
            return;
        }

        const dup_uri = try self.gpa.dupe(u8, uri);
        errdefer self.gpa.free(dup_uri);
        try self.map.put(self.gpa, dup_uri, .{
            .text = dup_text,
            .line_starts = line_starts,
            .version = client_version,
            .z_text = z_text,
        });
    }

    /// Return the buffered text for `uri`, or `null` when missing.
    fn get(self: *DocumentStore, uri: []const u8) ?*Document {
        return self.map.getPtr(uri);
    }

    /// Drop the stored document for `uri` if it exists.
    fn remove(self: *DocumentStore, uri: []const u8) void {
        if (self.map.fetchRemove(uri)) |kv| {
            self.gpa.free(kv.key);
            self.gpa.free(kv.value.text);
            self.gpa.free(kv.value.line_starts);
            self.gpa.free(kv.value.z_text);
        }
    }
};

/// Start the LSP server loop reading from stdin/stdout using `gpa`.
pub fn run(gpa: std.mem.Allocator) !void {
    const stdin_file = std.fs.File.stdin();
    const stdout_file = std.fs.File.stdout();

    var stdout = stdout_file.writer(&.{});

    var docs: DocumentStore = .init(gpa);
    defer docs.deinit();
    var analysis: AnalysisCache = .init(gpa);
    defer analysis.deinit();

    var arena_state: std.heap.ArenaAllocator = .init(gpa);
    defer arena_state.deinit();

    // Persistent input buffer
    var recv_buf = std.ArrayList(u8){};
    defer recv_buf.deinit(gpa);

    std.debug.print("[lsp] server started \n", .{});

    while (true) {
        const arena = arena_state.allocator();
        defer _ = arena_state.reset(.retain_capacity);

        // --- 1. Read Headers ---
        var body_start_index: ?usize = null;
        while (body_start_index == null) {
            if (findHeaderEnd(recv_buf.items)) |idx| {
                body_start_index = idx;
            } else {
                var tmp: [4096]u8 = undefined;
                const n = try stdin_file.read(&tmp);
                if (n == 0) return; // EOF

                try recv_buf.appendSlice(gpa, tmp[0..n]);

                if (recv_buf.items.len > 10 * 1024 * 1024) return error.ResourceExhausted;
            }
        }

        const body_start = body_start_index.?;
        const header_bytes = recv_buf.items[0..body_start];

        // --- 2. Parse Content-Length ---
        const content_len = parseContentLength(header_bytes) catch |err| {
            std.debug.print("[lsp] header parse error: {s}\n", .{@errorName(err)});
            // Robustness: consume bad header and retry
            try recv_buf.replaceRange(gpa, 0, body_start, &.{});
            continue;
        };

        // --- 3. Read Body ---
        const total_msg_len = body_start + content_len;
        while (recv_buf.items.len < total_msg_len) {
            var tmp: [4096]u8 = undefined;
            const n = try stdin_file.read(&tmp);
            if (n == 0) return;
            try recv_buf.appendSlice(gpa, tmp[0..n]);
        }

        // --- 4. Extract ---
        const body_src = recv_buf.items[body_start..total_msg_len];
        const body = try arena.dupe(u8, body_src);
        try recv_buf.replaceRange(gpa, 0, total_msg_len, &.{});

        // --- 5. Process ---
        const Request = struct {
            jsonrpc: []const u8,
            method: []const u8,
            id: ?u64 = null,
            params: ?json.Value = null,
        };

        const parsed = json.parseFromSlice(Request, arena, body, .{ .ignore_unknown_fields = true }) catch |e| {
            std.debug.print("[lsp] json parse error: {s}\n", .{@errorName(e)});
            continue;
        };
        const req = parsed.value;

        // Dispatch: Pass 'stdout' (anytype) which handles the unbuffered write
        if (std.mem.eql(u8, req.method, "initialize")) {
            try respondInitialize(&stdout.interface, arena, req.id orelse 0);
        } else if (std.mem.eql(u8, req.method, "initialized")) {
            // no-op
        } else if (std.mem.eql(u8, req.method, "shutdown")) {
            try writeJson(&stdout.interface, arena, .{ .jsonrpc = "2.0", .id = req.id orelse 0, .result = null });
        } else if (std.mem.eql(u8, req.method, "exit")) {
            return;
        } else if (std.mem.eql(u8, req.method, "textDocument/didOpen")) {
            if (req.params) |p| try onDidOpen(&stdout.interface, arena, &docs, &analysis, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/didChange")) {
            if (req.params) |p| try onDidChange(&stdout.interface, arena, &docs, &analysis, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/didClose")) {
            if (req.params) |p| try onDidClose(&stdout.interface, arena, &docs, &analysis, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/definition")) {
            if (req.params) |p| try onGoToDefinition(&stdout.interface, arena, &docs, &analysis, req.id orelse 0, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/hover")) {
            if (req.params) |p| try onHover(&stdout.interface, arena, &docs, &analysis, req.id orelse 0, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/rename")) {
            if (req.params) |p| try onRename(&stdout.interface, arena, &docs, &analysis, req.id orelse 0, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/completion")) {
            if (req.params) |p| try onCompletion(&stdout.interface, arena, &docs, &analysis, req.id orelse 0, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/semanticTokens/full")) {
            if (req.params) |p| try onSemanticTokensFull(&stdout.interface, arena, &docs, &analysis, req.id orelse 0, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/formatting")) {
            if (req.params) |p| try onFormatting(&stdout.interface, arena, &docs, &analysis, req.id orelse 0, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/references")) {
            if (req.params) |p| try onReferences(&stdout.interface, arena, &docs, &analysis, req.id orelse 0, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/documentSymbol")) {
            if (req.params) |p| try onDocumentSymbol(&stdout.interface, arena, &docs, &analysis, req.id orelse 0, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/signatureHelp")) {
            if (req.params) |p| try onSignatureHelp(&stdout.interface, arena, &docs, &analysis, req.id orelse 0, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/codeAction")) {
            if (req.params) |p| try onCodeAction(&stdout.interface, arena, &docs, &analysis, req.id orelse 0, p);
        } else {
            if (req.id) |rid| try writeJson(&stdout.interface, arena, .{ .jsonrpc = "2.0", .id = rid, .result = null });
        }
    }
}

/// Locate the split between headers and body within `buf`.
fn findHeaderEnd(buf: []const u8) ?usize {
    if (std.mem.indexOf(u8, buf, "\r\n\r\n")) |i| return i + 4;
    if (std.mem.indexOf(u8, buf, "\n\n")) |i| return i + 2;
    return null;
}

/// Parse the `Content-Length` header field from `header_bytes`.
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

/// Read exactly `dest.len` bytes from `in` into `dest`.
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
/// Emit an LSP response with the given JSON `payload`.
fn sendMessage(out: *std.Io.Writer, payload: []const u8) !void {
    try out.print("Content-Length: {d}\r\n\r\n", .{payload.len});
    try out.writeAll(payload);
    try out.flush();
}

/// Serialize `value` as JSON and send it through `out`.
fn writeJson(out: *std.Io.Writer, gpa: std.mem.Allocator, value: anytype) !void {
    var allocw: std.Io.Writer.Allocating = .init(gpa);
    defer allocw.deinit();
    var s = json.Stringify{ .writer = &allocw.writer, .options = .{ .whitespace = .minified } };
    try s.write(value);
    try sendMessage(out, allocw.written());
}

/// Send a null result for a request identified by `id`.
fn respondNullResult(out: *std.Io.Writer, gpa: std.mem.Allocator, id: u64) !void {
    try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
}

/// Notify the client that semantic tokens should be refreshed.
fn notifySemanticTokensRefresh(out: *std.Io.Writer, gpa: std.mem.Allocator) !void {
    const Msg = struct {
        jsonrpc: []const u8 = "2.0",
        method: []const u8 = "workspace/semanticTokens/refresh",
    };
    try writeJson(out, gpa, Msg{});
}

/// Return the document text or respond with a null result when missing.
fn requireDocumentOrRespondNull(
    out: *std.Io.Writer,
    gpa: std.mem.Allocator,
    docs: *DocumentStore,
    uri: []const u8,
    id: u64,
) !?*DocumentStore.Document {
    if (docs.get(uri)) |doc| return doc;
    try respondNullResult(out, gpa, id);
    return null;
}

// ================== LSP handlers ==================

/// Respond to `initialize` requests with capabilities and `id`.
fn respondInitialize(out: *std.Io.Writer, gpa: std.mem.Allocator, id: u64) !void {
    // Capability descriptor broadcast during `initialize` responses.
    const Caps = struct {
        /// Synchronization mode requested by the client.
        textDocumentSync: u32 = 1, // Full sync
        /// Indicates hover support.
        hoverProvider: bool = true,
        /// Indicates definition lookup support.
        definitionProvider: bool = true,
        /// Indicates rename support.
        renameProvider: bool = true,
        /// Indicates formatting support.
        documentFormattingProvider: bool = true,
        /// Indicates reference support.
        referencesProvider: bool = true,
        /// Indicates document symbol support.
        documentSymbolProvider: bool = true,
        /// Indicates signature help support.
        signatureHelpProvider: struct {
            triggerCharacters: []const []const u8,
        } = .{ .triggerCharacters = &.{ "(", "," } },
        /// Indicates code action support.
        codeActionProvider: bool = true,
        /// Completion provider metadata.
        completionProvider: struct { triggerCharacters: []const []const u8 } = .{ .triggerCharacters = &.{"."} },
        /// Semantic token capability metadata.
        semanticTokensProvider: struct {
            legend: struct {
                tokenTypes: []const []const u8,
                tokenModifiers: []const []const u8,
            },
            full: bool = true,
            range: bool = true,
            refreshSupport: bool = true,
        } = .{
            .legend = .{
                .tokenTypes = semantic_token_types[0..],
                .tokenModifiers = semantic_token_modifiers[0..],
            },
            .range = true,
            .refreshSupport = true,
        },
        positionEncoding: []const u8 = "utf-8",
    };
    // Response envelope for the `initialize` request containing capabilities.
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

/// Handle `textDocument/didOpen` by caching the document's text.
fn onDidOpen(out: *std.Io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, analysis: *AnalysisCache, params: json.Value) !void {
    var p = try json.parseFromValue(TextDocumentOpenParams, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();
    try docs.set(p.value.textDocument.uri, p.value.textDocument.text, p.value.textDocument.version);

    analysis.remove(p.value.textDocument.uri);

    try publishDiagnostics(out, gpa, docs, analysis, p.value.textDocument.uri);
    try notifySemanticTokensRefresh(out, gpa);
}

/// Handle `textDocument/didChange` by updating stored text ranges.
fn onDidChange(out: *std.Io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, analysis: *AnalysisCache, params: json.Value) !void {
    var p = try json.parseFromValue(TextDocumentChangeParams, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();
    if (p.value.contentChanges.len == 0) return;

    // Update the document text and version
    try docs.set(p.value.textDocument.uri, p.value.contentChanges[0].text, p.value.textDocument.version);

    try publishDiagnostics(out, gpa, docs, analysis, p.value.textDocument.uri);
    try notifySemanticTokensRefresh(out, gpa);
}

/// Handle `textDocument/didClose` by removing the cached document.
fn onDidClose(out: *std.Io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, analysis: *AnalysisCache, params: json.Value) !void {
    // JSON parameters for `textDocument/didClose`.
    // Parameters payload for `textDocument/didClose` notifications.
    var p = try json.parseFromValue(TextDocumentParams, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();
    const uri = p.value.textDocument.uri;
    docs.remove(uri);
    analysis.remove(uri);
    // Notification payload sent to acknowledge diagnostics removal.
    const Msg = struct {
        jsonrpc: []const u8 = "2.0",
        method: []const u8 = "textDocument/publishDiagnostics",
        params: struct { uri: []const u8, diagnostics: []const LspDiagnostic },
    };
    const empty_diags = [_]LspDiagnostic{};
    try writeJson(out, gpa, Msg{ .params = .{ .uri = uri, .diagnostics = &empty_diags } });
}

/// Represents an identifier declared within a scope for semantic token highlights.
const Symbol = struct {
    /// Location of the declaration used for highlighting references.
    decl_loc: ast.LocId,
    /// Semantic token kind assigned to this symbol.
    kind: SemanticTokenKind,
};

/// Represents the symbol table kept for a lexical scope during semantic analysis.
const Scope = struct {
    /// Symbol table for the current scope.
    symbols: std.StringHashMap(Symbol),
    /// Optional parent scope used for fallback lookup.
    parent: ?*const Scope,
    /// Allocator backing nested scope storage.
    gpa: std.mem.Allocator,

    /// Create a nested scope optionally chained to `parent`.
    fn init(gpa: std.mem.Allocator, parent: ?*const Scope) Scope {
        return .{
            .symbols = .init(gpa),
            .parent = parent,
            .gpa = gpa,
        };
    }

    /// Release the storage backing the scope.
    fn deinit(self: *Scope) void {
        self.symbols.deinit();
    }

    /// Register a symbol named `name` in this scope.
    fn declare(self: *Scope, name: []const u8, loc: ast.LocId, kind: SemanticTokenKind) !void {
        try self.symbols.put(name, .{ .decl_loc = loc, .kind = kind });
    }

    /// Lookup `name` within this scope or any parent scopes.
    fn lookup(self: *const Scope, name: []const u8) ?Symbol {
        if (self.symbols.get(name)) |symbol| {
            return symbol;
        }
        if (self.parent) |p| {
            return p.lookup(name);
        }
        return null;
    }
};

/// Builds lookup tables that map AST locations to symbol metadata.
const SymbolResolver = struct {
    /// Allocator used for temporary scope tracking.
    gpa: std.mem.Allocator,
    /// AST unit being analyzed.
    ast_unit: *ast.Ast,
    /// Map storing the resolved symbols keyed by declaration ID.
    resolution_map: *std.AutoArrayHashMap(u32, Symbol),

    /// Build symbol map by walking the AST and recording definitions.
    pub fn run(gpa: std.mem.Allocator, ast_unit: *ast.Ast, resolution_map: *std.AutoArrayHashMap(u32, Symbol)) !void {
        var self = SymbolResolver{
            .gpa = gpa,
            .ast_unit = ast_unit,
            .resolution_map = resolution_map,
        };

        var global_scope: Scope = .init(gpa, null);
        defer global_scope.deinit();

        try self.walkUnit(&global_scope);
    }

    /// Walk every declaration in `ast_unit` to register symbol bindings.
    fn walkUnit(self: *SymbolResolver, scope: *Scope) !void {
        const decls = self.ast_unit.exprs.decl_pool.slice(self.ast_unit.unit.decls);
        for (decls) |decl_id| {
            try self.walkDecl(scope, decl_id);
        }
        for (decls) |decl_id| {
            const decl_row = self.ast_unit.exprs.Decl.get(decl_id);
            try self.walkExpr(scope, decl_row.value);
            if (!decl_row.ty.isNone()) {
                try self.walkExpr(scope, decl_row.ty.unwrap());
            }
        }
    }

    /// Walk declaration `decl_id`, storing its bindings (patterns/types).
    fn walkDecl(self: *SymbolResolver, scope: *Scope, decl_id: ast.DeclId) !void {
        const decl_row = self.ast_unit.exprs.Decl.get(decl_id);
        const decl_kind = classifyDeclKind(self.ast_unit, decl_row.value);
        if (!decl_row.pattern.isNone()) {
            try self.walkPattern(scope, patternFromOpt(decl_row.pattern), decl_kind);
        }
    }

    /// Walk statement `stmt_id`, using patterns as necessary to populate symbols.
    fn walkStmt(self: *SymbolResolver, scope: *Scope, stmt_id: ast.StmtId) anyerror!void {
        const stmt_store = &self.ast_unit.stmts;
        const stmt_kind = stmt_store.kind(stmt_id);
        switch (stmt_kind) {
            .Expr => {
                const row = stmt_store.get(.Expr, stmt_id);
                try self.walkExpr(scope, row.expr);
            },
            .Decl => {
                const row = stmt_store.get(.Decl, stmt_id);
                try self.walkDecl(scope, row.decl);
                const decl_row = self.ast_unit.exprs.Decl.get(row.decl);
                try self.walkExpr(scope, decl_row.value);
                if (!decl_row.ty.isNone()) {
                    try self.walkExpr(scope, decl_row.ty.unwrap());
                }
            },
            .Assign => {
                const row = stmt_store.get(.Assign, stmt_id);
                try self.walkExpr(scope, row.left);
                try self.walkExpr(scope, row.right);
            },
            else => {},
        }
    }

    /// Walk expression `expr_id` to gather potential bindings (e.g., function literals).
    fn walkExpr(self: *SymbolResolver, scope: *const Scope, expr_id: ast.ExprId) !void {
        const expr_store = &self.ast_unit.exprs;
        const expr_kind = expr_store.kind(expr_id);

        switch (expr_kind) {
            .Ident => {
                const row = expr_store.get(.Ident, expr_id);
                if (scope.lookup(expr_store.strs.get(row.name))) |symbol| {
                    try self.resolution_map.put(expr_id.toRaw(), symbol);
                }
            },
            .Block => {
                const row = expr_store.get(.Block, expr_id);
                var block_scope: Scope = .init(self.gpa, scope);
                defer block_scope.deinit();
                const stmts = self.ast_unit.stmts.stmt_pool.slice(row.items);
                for (stmts) |stmt_id| {
                    try self.walkStmt(&block_scope, stmt_id);
                }
            },
            .FunctionLit => {
                const row = expr_store.get(.FunctionLit, expr_id);
                var fn_scope: Scope = .init(self.gpa, scope);
                defer fn_scope.deinit();

                const params = expr_store.param_pool.slice(row.params);
                for (params) |param_id| {
                    const param = expr_store.Param.get(param_id);
                    if (!param.pat.isNone()) {
                        try self.walkPattern(&fn_scope, patternFromOpt(param.pat), .parameter);
                    }
                }

                if (!row.body.isNone()) {
                    try self.walkExpr(&fn_scope, row.body.unwrap());
                }
            },
            .Closure => {
                const row = expr_store.get(.Closure, expr_id);
                var fn_scope: Scope = .init(self.gpa, scope);
                defer fn_scope.deinit();

                const params = expr_store.param_pool.slice(row.params);
                for (params) |param_id| {
                    const param = expr_store.Param.get(param_id);
                    if (!param.pat.isNone()) {
                        try self.walkPattern(&fn_scope, patternFromOpt(param.pat), .parameter);
                    }
                }
                try self.walkExpr(&fn_scope, row.body);
            },
            .For => {
                const row = expr_store.get(.For, expr_id);
                var for_scope: Scope = .init(self.gpa, scope);
                defer for_scope.deinit();
                try self.walkPattern(&for_scope, row.pattern, .variable);
                try self.walkExpr(scope, row.iterable);
                try self.walkExpr(&for_scope, row.body);
            },
            .While => {
                const row = expr_store.get(.While, expr_id);
                if (row.is_pattern and !row.pattern.isNone()) {
                    var while_scope: Scope = .init(self.gpa, scope);
                    defer while_scope.deinit();
                    try self.walkPattern(&while_scope, patternFromOpt(row.pattern), .variable);
                    if (!row.cond.isNone()) {
                        try self.walkExpr(scope, row.cond.unwrap());
                    }
                    try self.walkExpr(&while_scope, row.body);
                } else {
                    if (!row.cond.isNone()) {
                        try self.walkExpr(scope, row.cond.unwrap());
                    }
                    try self.walkExpr(scope, row.body);
                }
            },
            .Unary => {
                const row = expr_store.get(.Unary, expr_id);
                try self.walkExpr(scope, row.expr);
            },
            .Binary => {
                const row = expr_store.get(.Binary, expr_id);
                try self.walkExpr(scope, row.left);
                try self.walkExpr(scope, row.right);
            },
            .Range => {
                const row = expr_store.get(.Range, expr_id);
                if (!row.start.isNone()) try self.walkExpr(scope, row.start.unwrap());
                if (!row.end.isNone()) try self.walkExpr(scope, row.end.unwrap());
            },
            .Deref => {
                const row = expr_store.get(.Deref, expr_id);
                try self.walkExpr(scope, row.expr);
            },
            .ArrayLit => {
                const row = expr_store.get(.ArrayLit, expr_id);
                for (expr_store.expr_pool.slice(row.elems)) |elem| try self.walkExpr(scope, elem);
            },
            .TupleLit => {
                const row = expr_store.get(.TupleLit, expr_id);
                for (expr_store.expr_pool.slice(row.elems)) |elem| try self.walkExpr(scope, elem);
            },
            .MapLit => {
                const row = expr_store.get(.MapLit, expr_id);
                for (expr_store.kv_pool.slice(row.entries)) |kv_id| {
                    const kv = expr_store.KeyValue.get(kv_id);
                    try self.walkExpr(scope, kv.key);
                    try self.walkExpr(scope, kv.value);
                }
            },
            .Call => {
                const row = expr_store.get(.Call, expr_id);
                try self.walkExpr(scope, row.callee);
                for (expr_store.expr_pool.slice(row.args)) |arg| try self.walkExpr(scope, arg);
            },
            .IndexAccess => {
                const row = expr_store.get(.IndexAccess, expr_id);
                try self.walkExpr(scope, row.collection);
                try self.walkExpr(scope, row.index);
            },
            .FieldAccess => {
                const row = expr_store.get(.FieldAccess, expr_id);
                try self.walkExpr(scope, row.parent);
            },
            .StructLit => {
                const row = expr_store.get(.StructLit, expr_id);
                if (!row.ty.isNone()) try self.walkExpr(scope, row.ty.unwrap());
                for (expr_store.sfv_pool.slice(row.fields)) |field_id| {
                    const field = expr_store.StructFieldValue.get(field_id);
                    try self.walkExpr(scope, field.value);
                }
            },
            .ComptimeBlock => {
                const row = expr_store.get(.ComptimeBlock, expr_id);
                try self.walkExpr(scope, row.block);
            },
            .CodeBlock => {
                const row = expr_store.get(.CodeBlock, expr_id);
                try self.walkExpr(scope, row.block);
            },
            .AsyncBlock => {
                const row = expr_store.get(.AsyncBlock, expr_id);
                try self.walkExpr(scope, row.body);
            },
            .MlirBlock => {
                const row = expr_store.get(.MlirBlock, expr_id);
                for (expr_store.expr_pool.slice(row.args)) |arg| try self.walkExpr(scope, arg);
            },
            .Insert => {
                const row = expr_store.get(.Insert, expr_id);
                try self.walkExpr(scope, row.expr);
            },
            .Return => {
                const row = expr_store.get(.Return, expr_id);
                if (!row.value.isNone()) try self.walkExpr(scope, row.value.unwrap());
            },
            .If => {
                const row = expr_store.get(.If, expr_id);
                try self.walkExpr(scope, row.cond);
                try self.walkExpr(scope, row.then_block);
                if (!row.else_block.isNone()) try self.walkExpr(scope, row.else_block.unwrap());
            },
            .Match => {
                const row = expr_store.get(.Match, expr_id);
                try self.walkExpr(scope, row.expr);
                const arms = expr_store.arm_pool.slice(row.arms);
                for (arms) |arm_id| {
                    const arm = expr_store.MatchArm.get(arm_id);
                    var arm_scope: Scope = .init(self.gpa, scope);
                    defer arm_scope.deinit();
                    try self.walkPattern(&arm_scope, arm.pattern, .variable);
                    if (!arm.guard.isNone()) {
                        try self.walkExpr(&arm_scope, arm.guard.unwrap());
                    }
                    try self.walkExpr(&arm_scope, arm.body);
                }
            },
            .Break => {
                const row = expr_store.get(.Break, expr_id);
                if (!row.value.isNone()) try self.walkExpr(scope, row.value.unwrap());
            },
            .Defer => {
                const row = expr_store.get(.Defer, expr_id);
                try self.walkExpr(scope, row.expr);
            },
            .ErrDefer => {
                const row = expr_store.get(.ErrDefer, expr_id);
                try self.walkExpr(scope, row.expr);
            },
            .ErrUnwrap => {
                const row = expr_store.get(.ErrUnwrap, expr_id);
                try self.walkExpr(scope, row.expr);
            },
            .OptionalUnwrap => {
                const row = expr_store.get(.OptionalUnwrap, expr_id);
                try self.walkExpr(scope, row.expr);
            },
            .Await => {
                const row = expr_store.get(.Await, expr_id);
                try self.walkExpr(scope, row.expr);
            },
            .Cast => {
                const row = expr_store.get(.Cast, expr_id);
                try self.walkExpr(scope, row.expr);
                try self.walkExpr(scope, row.ty);
            },
            .Catch => {
                const row = expr_store.get(.Catch, expr_id);
                try self.walkExpr(scope, row.expr);
                var handler_scope: Scope = .init(self.gpa, scope);
                defer handler_scope.deinit();
                if (!row.binding_name.isNone()) {
                    try handler_scope.declare(expr_store.strs.get(row.binding_name.unwrap()), row.binding_loc.unwrap(), .variable);
                }
                try self.walkExpr(&handler_scope, row.handler);
            },
            .TypeOf => {
                const row = expr_store.get(.TypeOf, expr_id);
                try self.walkExpr(scope, row.expr);
            },
            .TupleType => {
                const row = expr_store.get(.TupleType, expr_id);
                for (expr_store.expr_pool.slice(row.elems)) |elem| try self.walkExpr(scope, elem);
            },
            .ArrayType => {
                const row = expr_store.get(.ArrayType, expr_id);
                try self.walkExpr(scope, row.elem);
                try self.walkExpr(scope, row.size);
            },
            .DynArrayType => {
                const row = expr_store.get(.DynArrayType, expr_id);
                try self.walkExpr(scope, row.elem);
            },
            .MapType => {
                const row = expr_store.get(.MapType, expr_id);
                try self.walkExpr(scope, row.key);
                try self.walkExpr(scope, row.value);
            },
            .SliceType => {
                const row = expr_store.get(.SliceType, expr_id);
                try self.walkExpr(scope, row.elem);
            },
            .OptionalType => {
                const row = expr_store.get(.OptionalType, expr_id);
                try self.walkExpr(scope, row.elem);
            },
            .ErrorSetType => {
                const row = expr_store.get(.ErrorSetType, expr_id);
                try self.walkExpr(scope, row.err);
                try self.walkExpr(scope, row.value);
            },
            .StructType => {
                const row = expr_store.get(.StructType, expr_id);
                for (expr_store.sfield_pool.slice(row.fields)) |field_id| {
                    const field = expr_store.StructField.get(field_id);
                    try self.walkExpr(scope, field.ty);
                    if (!field.value.isNone()) try self.walkExpr(scope, field.value.unwrap());
                }
            },
            .EnumType => {
                const row = expr_store.get(.EnumType, expr_id);
                if (!row.discriminant.isNone()) try self.walkExpr(scope, row.discriminant.unwrap());
                for (expr_store.efield_pool.slice(row.fields)) |field_id| {
                    const field = expr_store.EnumField.get(field_id);
                    if (!field.value.isNone()) try self.walkExpr(scope, field.value.unwrap());
                }
            },
            .VariantType => {
                const row = expr_store.get(.VariantType, expr_id);
                for (expr_store.vfield_pool.slice(row.fields)) |field_id| {
                    const field = expr_store.VariantField.get(field_id);
                    if (!field.value.isNone()) try self.walkExpr(scope, field.value.unwrap());
                }
            },
            .UnionType => {
                const row = expr_store.get(.UnionType, expr_id);
                for (expr_store.sfield_pool.slice(row.fields)) |field_id| {
                    const field = expr_store.StructField.get(field_id);
                    try self.walkExpr(scope, field.ty);
                    if (!field.value.isNone()) try self.walkExpr(scope, field.value.unwrap());
                }
            },
            .PointerType => {
                const row = expr_store.get(.PointerType, expr_id);
                try self.walkExpr(scope, row.elem);
            },
            .SimdType => {
                const row = expr_store.get(.SimdType, expr_id);
                try self.walkExpr(scope, row.elem);
                try self.walkExpr(scope, row.lanes);
            },
            .ComplexType => {
                const row = expr_store.get(.ComplexType, expr_id);
                try self.walkExpr(scope, row.elem);
            },
            .TensorType => {
                const row = expr_store.get(.TensorType, expr_id);
                try self.walkExpr(scope, row.elem);
                for (expr_store.expr_pool.slice(row.shape)) |elem| try self.walkExpr(scope, elem);
            },
            else => {},
        }
    }

    /// Record each binding introduced by pattern `pat_id` using `kind`.
    fn walkPattern(self: *SymbolResolver, scope: *Scope, pat_id: ast.PatternId, kind: SemanticTokenKind) !void {
        const pat_store = &self.ast_unit.pats;
        const pat_kind = pat_store.kind(pat_id);
        switch (pat_kind) {
            .Binding => {
                const row = pat_store.get(.Binding, pat_id);
                try scope.declare(self.ast_unit.pats.strs.get(row.name), row.loc, kind);
            },
            .Tuple => {
                const row = pat_store.get(.Tuple, pat_id);
                const elems = pat_store.pat_pool.slice(row.elems);
                for (elems) |elem| try self.walkPattern(scope, elem, kind);
            },
            .Slice => {
                const row = pat_store.get(.Slice, pat_id);
                const elems = pat_store.pat_pool.slice(row.elems);
                for (elems) |elem| try self.walkPattern(scope, elem, kind);
                if (!row.rest_binding.isNone()) {
                    try self.walkPattern(scope, patternFromOpt(row.rest_binding), kind);
                }
            },
            .Struct => {
                const row = pat_store.get(.Struct, pat_id);
                const fields = pat_store.field_pool.slice(row.fields);
                for (fields) |field_id| {
                    const field = pat_store.StructField.get(field_id);
                    try self.walkPattern(scope, field.pattern, kind);
                }
            },
            .VariantStruct => {
                const row = pat_store.get(.VariantStruct, pat_id);
                const fields = pat_store.field_pool.slice(row.fields);
                for (fields) |field_id| {
                    const field = pat_store.StructField.get(field_id);
                    try self.walkPattern(scope, field.pattern, kind);
                }
            },
            .VariantTuple => {
                const row = pat_store.get(.VariantTuple, pat_id);
                const elems = pat_store.pat_pool.slice(row.elems);
                for (elems) |elem| try self.walkPattern(scope, elem, kind);
            },
            .Or => {
                const row = pat_store.get(.Or, pat_id);
                const alts = pat_store.pat_pool.slice(row.alts);
                for (alts) |alt| try self.walkPattern(scope, alt, kind);
            },
            .At => {
                const row = pat_store.get(.At, pat_id);
                try scope.declare(self.ast_unit.pats.strs.get(row.binder), row.loc, kind);
                try self.walkPattern(scope, row.pattern, kind);
            },
            else => {},
        }
    }
};

/// Respond to hover requests by computing `HoverInfo` at the caret.
fn onHover(out: *std.Io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, analysis: *AnalysisCache, id: u64, params: json.Value) !void {
    // JSON parameters for hover requests.
    // Parameters payload for `textDocument/hover` requests.
    var p = try json.parseFromValue(TextDocumentPositionParams, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();

    const uri = p.value.textDocument.uri;
    const doc = try requireDocumentOrRespondNull(out, gpa, docs, uri, id) orelse return;
    const text = doc.text;

    // Response payload sent for semantic token requests.
    // Response envelope for the hover request.
    const Resp = struct {
        jsonrpc: []const u8 = "2.0",
        id: u64,
        result: ?struct {
            contents: struct { kind: []const u8 = "markdown", value: []const u8 },
            range: LspRange,
        } = null,
    };

    const offset = positionToOffset(text, p.value.position.line, p.value.position.character, doc.line_starts);
    const entry = try analysis.ensure(uri, doc) orelse {
        try writeJson(out, gpa, Resp{ .id = id, .result = null });
        return;
    };

    const hover_info = try computeHover(gpa, doc, entry, offset);

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

/// Handle go-to-definition requests by locating the symbol at the caret.
fn onGoToDefinition(out: *std.io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, analysis: *AnalysisCache, id: u64, params: json.Value) !void {
    // JSON parameters for `textDocument/definition`.
    // Parameters payload for `textDocument/definition` requests.
    var p = try json.parseFromValue(TextDocumentPositionParams, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();

    const uri = p.value.textDocument.uri;
    const doc = try requireDocumentOrRespondNull(out, gpa, docs, uri, id) orelse return;
    const text = doc.text;

    const offset = positionToOffset(text, p.value.position.line, p.value.position.character, doc.line_starts);
    const entry = try analysis.ensure(uri, doc) orelse {
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
        return;
    };

    const ast_unit = entry.ast_unit orelse {
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
        return;
    };

    const expr_id = findExprAt(ast_unit, offset) orelse {
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
        return;
    };

    if (try resolveDefinition(gpa, entry, expr_id)) |def| {
        const def_loc = def.loc;
        const def_file_id = def_loc.file_id;
        const def_path = entry.context.source_manager.get(def_file_id) orelse {
            try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
            return;
        };
        const def_text = entry.context.source_manager.read(def_file_id) catch {
            try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
            return;
        };
        defer gpa.free(def_text);

        const def_uri = try pathToUri(gpa, def_path);
        defer gpa.free(def_uri);

        const def_lines = try buildLineStarts(gpa, def_text);
        defer gpa.free(def_lines);

        const range = locToRange(def_text, def_lines, def_loc);
        const res_uri = try gpa.dupe(u8, def_uri);

        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = .{ .uri = res_uri, .range = range } });
        gpa.free(res_uri);
    } else {
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
    }
}

const ResolvedDef = struct {
    decl_ast: *ast.Ast,
    decl_id: ast.DeclId,
    loc: Loc,
};

fn resolveDefinition(_: std.mem.Allocator, entry: *AnalysisCache.Entry, expr_id: ast.ExprId) !?ResolvedDef {
    const ast_unit = entry.ast_unit orelse return null;

    // 1. Try local resolution map
    if (entry.resolution_map.get(expr_id.toRaw())) |symbol| {
        const decl_loc = ast_unit.exprs.locs.get(symbol.decl_loc);
        // Find which decl owns this loc
        // Optimization: We know the decl location, we can scan decls.
        // Or we can just return the loc and use the current AST.
        // But we need DeclId for Signature Help.
        // For now, let's scan top-level decls of the current unit.
        const decls = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);
        for (decls) |d_id| {
            const row = ast_unit.exprs.Decl.get(d_id);
            if (row.loc.eq(symbol.decl_loc)) {
                return ResolvedDef{ .decl_ast = ast_unit, .decl_id = d_id, .loc = decl_loc };
            }
        }
        // If not a top-level decl, it might be a local variable binding.
        // In that case we return the loc but maybe no DeclId (or a dummy).
        // But Signature Help needs DeclId to get params.
        // Local function literals are Exprs, not Decls.
        // If the symbol resolves to a local binding `let x = fn...`, `x` is a Pattern.
        // This is complex. For now, let's support Top-Level Decls (Imports/Functions).
        return ResolvedDef{ .decl_ast = ast_unit, .decl_id = ast.DeclId.fromRaw(0), .loc = decl_loc };
    }

    // 2. Try Method Binding
    if (ast_unit.type_info.getMethodBinding(expr_id)) |binding| {
        const decl_loc = binding.decl_ast.exprs.locs.get(binding.decl_ast.exprs.Decl.get(binding.decl_id).loc);
        return ResolvedDef{ .decl_ast = binding.decl_ast, .decl_id = binding.decl_id, .loc = decl_loc };
    }

    // 3. Try Global Search (Cross-file)
    // Only if it is an Identifier
    if (ast_unit.exprs.kind(expr_id) == .Ident) {
        const ident_row = ast_unit.exprs.get(.Ident, expr_id);
        const name = ast_unit.exprs.strs.get(ident_row.name);

        // Iterate all packages -> sources
        var pkg_iter = entry.context.compilation_unit.packages.iterator();
        while (pkg_iter.next()) |pkg| {
            var src_iter = pkg.value_ptr.sources.iterator();
            while (src_iter.next()) |src_entry| {
                // Skip current file (already checked via local resolution map usually, but safe to check again)
                if (src_entry.value_ptr.file_id == entry.file_id) continue;

                if (src_entry.value_ptr.ast) |other_ast| {
                    const decls = other_ast.exprs.decl_pool.slice(other_ast.unit.decls);
                    for (decls) |d_id| {
                        const d_row = other_ast.exprs.Decl.get(d_id);
                        // Check pattern name
                        if (!d_row.pattern.isNone()) {
                            const pat_id = patternFromOpt(d_row.pattern);
                            if (other_ast.pats.kind(pat_id) == .Binding) {
                                const bind = other_ast.pats.get(.Binding, pat_id);
                                const bind_name = other_ast.pats.strs.get(bind.name);
                                if (std.mem.eql(u8, bind_name, name)) {
                                    const d_loc = other_ast.exprs.locs.get(d_row.loc);
                                    return ResolvedDef{ .decl_ast = other_ast, .decl_id = d_id, .loc = d_loc };
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    return null;
}

/// Find all references to the symbol at `offset`.
fn computeReferences(
    gpa: std.mem.Allocator,
    entry: *AnalysisCache.Entry,
    offset: usize,
    include_decl: bool,
) !?std.ArrayList(Loc) {
    const ast_unit = entry.ast_unit orelse return null;
    const expr_id = findExprAt(ast_unit, offset) orelse return null;
    const symbol = entry.resolution_map.get(expr_id.toRaw()) orelse return null;

    var refs = std.ArrayList(Loc){};
    errdefer refs.deinit(gpa);

    if (include_decl) {
        try refs.append(gpa, ast_unit.exprs.locs.get(symbol.decl_loc));
    }

    var it = entry.resolution_map.iterator();
    while (it.next()) |ent| {
        if (ent.value_ptr.decl_loc.eq(symbol.decl_loc)) {
            const ref_expr_id = ast.ExprId.fromRaw(ent.key_ptr.*);
            const ref_loc = exprLoc(ast_unit, ref_expr_id);
            try refs.append(gpa, ref_loc);
        }
    }
    return refs;
}

/// Handle find references requests.
fn onReferences(out: *std.io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, analysis: *AnalysisCache, id: u64, params: json.Value) !void {
    var p = try json.parseFromValue(ReferenceParams, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();

    const uri = p.value.textDocument.uri;
    const doc = try requireDocumentOrRespondNull(out, gpa, docs, uri, id) orelse return;
    const text = doc.text;
    const offset = positionToOffset(text, p.value.position.line, p.value.position.character, doc.line_starts);

    const entry = try analysis.ensure(uri, doc) orelse {
        try respondNullResult(out, gpa, id);
        return;
    };

    var refs_opt = try computeReferences(gpa, entry, offset, p.value.context.includeDeclaration);
    if (refs_opt) |*refs| {
        defer refs.deinit(gpa);

        var locs = std.ArrayList(struct { uri: []const u8, range: LspRange }){};
        defer {
            for (locs.items) |l| gpa.free(l.uri);
            locs.deinit(gpa);
        }

        for (refs.items) |ref_loc| {
            if (ref_loc.file_id != entry.file_id) continue;
            const range = locToRange(text, doc.line_starts, ref_loc);
            const u = try gpa.dupe(u8, uri);
            try locs.append(gpa, .{ .uri = u, .range = range });
        }
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = locs.items });
    } else {
        try respondNullResult(out, gpa, id);
    }
}

/// Handle document symbol requests.
fn onDocumentSymbol(out: *std.io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, analysis: *AnalysisCache, id: u64, params: json.Value) !void {
    var p = try json.parseFromValue(DocumentSymbolParams, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();

    const uri = p.value.textDocument.uri;
    const doc = try requireDocumentOrRespondNull(out, gpa, docs, uri, id) orelse return;

    const entry = try analysis.ensure(uri, doc) orelse {
        try respondNullResult(out, gpa, id);
        return;
    };

    var symbols = std.ArrayList(DocumentSymbol){};
    defer {
        freeDocumentSymbols(gpa, symbols.items);
        symbols.deinit(gpa);
    }

    if (entry.ast_unit) |ast_unit| {
        try computeDocumentSymbols(gpa, ast_unit, doc, &symbols);
    }

    try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = symbols.items });
}

fn freeDocumentSymbols(gpa: std.mem.Allocator, items: []const DocumentSymbol) void {
    for (items) |*item| {
        gpa.free(item.name);
        if (item.detail) |d| gpa.free(d);
        if (item.children) |c| {
            freeDocumentSymbols(gpa, c);
            gpa.free(c);
        }
    }
}

fn computeDocumentSymbols(gpa: std.mem.Allocator, ast_unit: *ast.Ast, doc: *const DocumentStore.Document, out: *std.ArrayList(DocumentSymbol)) !void {
    const decls = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);
    for (decls) |decl_id| {
        const row = ast_unit.exprs.Decl.get(decl_id);
        if (row.pattern.isNone()) continue;
        const pat_id = patternFromOpt(row.pattern);

        if (ast_unit.pats.kind(pat_id) == .Binding) {
            const bind_row = ast_unit.pats.get(.Binding, pat_id);
            const name = ast_unit.pats.strs.get(bind_row.name);
            const name_dupe = try gpa.dupe(u8, name);

            const loc = ast_unit.exprs.locs.get(row.loc);
            const range = locToRange(doc.text, doc.line_starts, loc);

            const kind: SymbolKind = switch (classifyDeclKind(ast_unit, row.value)) {
                .function => .Function,
                .type => .Struct,
                .variable => .Variable,
                else => .Variable,
            };

            try out.append(gpa, DocumentSymbol{
                .name = name_dupe,
                .kind = @intFromEnum(kind),
                .range = range,
                .selectionRange = range,
            });
        }
    }
}

/// Handle rename requests by recomputing AST and emitting edits.
fn onRename(out: *std.io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, analysis: *AnalysisCache, id: u64, params: json.Value) !void {
    // Rename request JSON payload describing the document and caret.
    // Parameters payload for `textDocument/rename` requests.
    var p = try json.parseFromValue(RenameParams, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();

    const uri = p.value.textDocument.uri;
    const doc = try requireDocumentOrRespondNull(out, gpa, docs, uri, id) orelse return;
    const text = doc.text;

    const offset = positionToOffset(text, p.value.position.line, p.value.position.character, doc.line_starts);
    const entry = try analysis.ensure(uri, doc) orelse {
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
        return;
    };

    var references = try computeReferences(gpa, entry, offset, true);
    if (references) |*refs| {
        defer refs.deinit(gpa);

        // Encoded workspace edits returned by rename operations.
        const WorkspaceEdit = struct {
            changes: std.StringHashMap([]const TextEdit),

            /// Emit JSON for this workspace edit (helper for rename responses).
            pub fn jsonStringify(self: @This(), s: *json.Stringify) !void {
                try s.beginObject();
                try s.objectField("changes");
                try s.beginObject();
                var changes_it = self.changes.iterator();
                while (changes_it.next()) |ent| {
                    try s.objectField(ent.key_ptr.*);
                    try s.write(ent.value_ptr.*);
                }
                try s.endObject();
                try s.endObject();
            }
        };

        var edits = std.ArrayList(TextEdit){};
        defer edits.deinit(gpa);

        for (refs.items) |loc| {
            const range = locToRange(text, doc.line_starts, loc);
            try edits.append(gpa, .{ .range = range, .newText = p.value.newName });
        }

        var changes: std.StringHashMap([]const TextEdit) = .init(gpa);
        defer {
            if (changes.get(uri)) |owned_slice| {
                gpa.free(owned_slice);
            }
            changes.deinit();
        }

        try changes.put(uri, try edits.toOwnedSlice(gpa));

        const workspace_edit = WorkspaceEdit{ .changes = changes };

        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = workspace_edit });
    } else {
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
    }
}

/// Convert filesystem `path` into a UTF-8 URI string.
fn pathToUri(gpa: std.mem.Allocator, path: []const u8) ![]u8 {
    return std.fmt.allocPrint(gpa, "file://{s}", .{path});
}

/// Represents a completion candidate returned to the client.
const CompletionItem = struct {
    label: []const u8,
    kind: ?u32 = null,
    detail: ?[]const u8 = null,
};

/// Static keyword completion entries.
const keyword_completion_items = [_]CompletionItem{
    .{ .label = "fn", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "struct", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "enum", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "let", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "const", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "if", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "else", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "for", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "while", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "match", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "return", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "true", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "false", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "import", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "package", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "defer", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "errdefer", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "async", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "await", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "try", .kind = @intFromEnum(CompletionItemKind.Keyword) },
    .{ .label = "catch", .kind = @intFromEnum(CompletionItemKind.Keyword) },
};

/// Enumeration of semantic completion categories exposed over LSP.
const CompletionItemKind = enum(u32) {
    Text = 1,
    Method = 2,
    Function = 3,
    Constructor = 4,
    Field = 5,
    Variable = 6,
    Class = 7,
    Interface = 8,
    Module = 9,
    Property = 10,
    Unit = 11,
    Value = 12,
    Enum = 13,
    Keyword = 14,
    Snippet = 15,
    Color = 16,
    File = 17,
    Reference = 18,
    Folder = 19,
    EnumMember = 20,
    Constant = 21,
    Struct = 22,
    Event = 23,
    Operator = 24,
    TypeParameter = 25,
};

/// Map semantic token kinds to their completion item analog in LSP.
fn lspCompletionKindFromSemantic(kind: SemanticTokenKind) CompletionItemKind {
    return switch (kind) {
        .keyword => .Keyword,
        .string, .number, .comment => .Value,
        .function => .Function,
        .type, .@"struct", .@"enum" => .Struct,
        .namespace => .Module,
        .variable => .Variable,
        .property => .Property,
        .parameter => .Variable,
        .enum_member => .EnumMember,
        .operator => .Operator,
    };
}

fn onSignatureHelp(out: *std.io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, analysis: *AnalysisCache, id: u64, params: json.Value) !void {
    var p = try json.parseFromValue(SignatureHelpParams, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();

    const uri = p.value.textDocument.uri;
    const doc = try requireDocumentOrRespondNull(out, gpa, docs, uri, id) orelse return;
    const text = doc.text;
    const offset = positionToOffset(text, p.value.position.line, p.value.position.character, doc.line_starts);

    const entry = try analysis.ensure(uri, doc) orelse {
        try respondNullResult(out, gpa, id);
        return;
    };

    if (entry.ast_unit) |ast_unit| {
        if (try computeSignatureHelp(gpa, ast_unit, entry, offset)) |help| {
            defer {
                for (help.signatures) |sig| {
                    gpa.free(sig.label);
                    if (sig.parameters) |params_slice| {
                        for (params_slice) |pm| gpa.free(pm.label);
                        gpa.free(params_slice);
                    }
                }
                gpa.free(help.signatures);
            }
            try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = help });
            return;
        }
    }
    try respondNullResult(out, gpa, id);
}

fn computeSignatureHelp(gpa: std.mem.Allocator, ast_unit: *ast.Ast, entry: *AnalysisCache.Entry, offset: usize) !?SignatureHelp {
    const expr_store = &ast_unit.exprs;
    const total = expr_store.index.kinds.items.len;

    var best_call: ?ast.ExprId = null;
    var best_span: usize = std.math.maxInt(usize);

    var i: usize = 0;
    while (i < total) : (i += 1) {
        const expr_id = ast.ExprId.fromRaw(@intCast(i));
        if (expr_store.kind(expr_id) == .Call) {
            const loc = exprLoc(ast_unit, expr_id);
            if (loc.file_id != entry.file_id) continue;

            if (offset >= loc.start and offset <= loc.end) {
                const span = loc.end - loc.start;
                if (span < best_span) {
                    best_span = span;
                    best_call = expr_id;
                }
            }
        }
    }

    const call_id = best_call orelse return null;
    const row = expr_store.get(.Call, call_id);

    // Calculate active parameter
    var active_param: u32 = 0;
    const args = expr_store.expr_pool.slice(row.args);
    for (args) |arg_id| {
        const arg_loc = exprLoc(ast_unit, arg_id);
        // If cursor is after this arg (and its comma), increment.
        // A simple heuristic: check if offset > arg.end.
        // This handles commas implicitly if we assume arguments are ordered.
        if (offset > arg_loc.end) {
            active_param += 1;
        }
    }
    // Clamp to args.len if we are not strictly inside an arg but maybe at the end
    // However, we might be typing the *next* argument.
    // If we have 0 args, active is 0.
    // If we have 1 arg and offset > arg.end, active is 1 (ready for 2nd arg).

    // Resolve the function definition to get parameter names
    var label = std.ArrayList(u8){};
    defer label.deinit(gpa);
    var parameters = std.ArrayList(ParameterInformation){};
    defer {
        for (parameters.items) |pm| gpa.free(pm.label);
        parameters.deinit(gpa);
    }

    var found_def = false;
    if (try resolveDefinition(gpa, entry, row.callee)) |def| {
        const decl_ast = def.decl_ast;
        const decl_row = decl_ast.exprs.Decl.get(def.decl_id);

        // Check if the value is a function literal
        if (decl_ast.exprs.kind(decl_row.value) == .FunctionLit) {
            found_def = true;
            const fn_row = decl_ast.exprs.get(.FunctionLit, decl_row.value);
            const params = decl_ast.exprs.param_pool.slice(fn_row.params);

            try label.appendSlice(gpa, "fn(");

            for (params, 0..) |param_id, idx| {
                if (idx > 0) try label.appendSlice(gpa, ", ");

                const param = decl_ast.exprs.Param.get(param_id);
                var param_str: []const u8 = "_";

                if (!param.pat.isNone()) {
                    const pat_id = patternFromOpt(param.pat);
                    if (decl_ast.pats.kind(pat_id) == .Binding) {
                        const bind = decl_ast.pats.get(.Binding, pat_id);
                        param_str = decl_ast.pats.strs.get(bind.name);
                    }
                }

                const start_idx = label.items.len;
                try label.appendSlice(gpa, param_str);
                const end_idx = label.items.len;

                // Add type info if available
                if (!param.ty.isNone()) {
                    try label.appendSlice(gpa, ": ");
                    // We can't easily print the AST type expr as a string without a formatter.
                    // But we can use the type store if we have the resolved type.
                    // For now, just ": type" is better than nothing, or skip type.
                    // Or use "..."
                    try label.appendSlice(gpa, "...");
                }

                const param_label = try gpa.dupe(u8, label.items[start_idx..end_idx]); // Just the name for highlighting?
                // LSP says label can be string (substring of signature) or [start, end].
                // If string, it must be contained in signature.
                // Let's use the simple string "name".
                try parameters.append(gpa, ParameterInformation{ .label = param_label });
            }
            try label.appendSlice(gpa, ")");
        }
    }

    if (!found_def) {
        try label.appendSlice(gpa, "fn(...)");
    }

    const sig_label = try label.toOwnedSlice(gpa);
    const sigs = try gpa.alloc(SignatureInformation, 1);
    const params_owned = try parameters.toOwnedSlice(gpa);
    sigs[0] = .{ .label = sig_label, .parameters = if (params_owned.len > 0) params_owned else null };
    if (params_owned.len == 0) gpa.free(params_owned);

    return SignatureHelp{
        .signatures = sigs,
        .activeSignature = 0,
        .activeParameter = active_param,
    };
}

fn onCodeAction(out: *std.io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, analysis: *AnalysisCache, id: u64, params: json.Value) !void {
    _ = docs;
    _ = analysis;
    _ = params;
    try respondNullResult(out, gpa, id);
}

/// Provide completion items in response to client requests.
fn onCompletion(out: *std.Io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, analysis: *AnalysisCache, id: u64, params: json.Value) !void {
    // Completion request payload describing the document and cursor position.
    // Parameters payload for completion requests.
    var p = try json.parseFromValue(TextDocumentPositionParams, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();

    const uri = p.value.textDocument.uri;
    const doc = try requireDocumentOrRespondNull(out, gpa, docs, uri, id) orelse return;

    var items = std.ArrayList(CompletionItem){};
    var owned = std.ArrayList([]const u8){};
    defer {
        for (owned.items) |buf| {
            gpa.free(buf);
        }
        owned.deinit(gpa);
        items.deinit(gpa);
    }

    computeCompletions(gpa, uri, doc, analysis, &items, &owned) catch |err| {
        std.debug.print("[lsp] completion error: {s}\n", .{@errorName(err)});
        const empty_items: ?[]const CompletionItem = null;
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = .{ .items = empty_items } });
        return;
    };

    try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = .{ .items = items.items } });
}

/// Populate `items` with completion candidates derived from `uri` and `text`.
fn computeCompletions(
    gpa: std.mem.Allocator,
    uri: []const u8,
    doc: *const DocumentStore.Document,
    analysis: *AnalysisCache,
    items: *std.ArrayList(CompletionItem),
    owned: *std.ArrayList([]const u8),
) !void {
    // Add keywords (static storage, no dup/free required)
    try items.appendSlice(gpa, &keyword_completion_items);

    const entry = try analysis.ensure(uri, doc) orelse return;
    const ast_unit = entry.ast_unit orelse return;

    // Add global declarations
    const decls = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);
    for (decls) |decl_id| {
        const decl_row = ast_unit.exprs.Decl.get(decl_id);
        const decl_kind = classifyDeclKind(ast_unit, decl_row.value);
        if (decl_row.pattern.isNone()) continue;
        try addPatternBindingsToCompletions(gpa, items, owned, ast_unit, patternFromOpt(decl_row.pattern), decl_kind);
    }
}

/// Add completion entries based on bindings found within `pat_id`.
fn addPatternBindingsToCompletions(
    gpa: std.mem.Allocator,
    items: *std.ArrayList(CompletionItem),
    owned: *std.ArrayList([]const u8),
    ast_unit: *ast.Ast,
    pat_id: ast.PatternId,
    kind: SemanticTokenKind,
) !void {
    const pat_store = &ast_unit.pats;
    const pat_kind = pat_store.kind(pat_id);
    switch (pat_kind) {
        .Binding => {
            const row = pat_store.get(.Binding, pat_id);
            const name = ast_unit.pats.strs.get(row.name);
            const copy = try gpa.dupe(u8, name);
            try owned.append(gpa, copy);
            try items.append(gpa, .{
                .label = copy,
                .kind = @intFromEnum(lspCompletionKindFromSemantic(kind)),
            });
        },
        .Tuple => {
            const row = pat_store.get(.Tuple, pat_id);
            for (pat_store.pat_pool.slice(row.elems)) |elem| try addPatternBindingsToCompletions(gpa, items, owned, ast_unit, elem, kind);
        },
        .Slice => {
            const row = pat_store.get(.Slice, pat_id);
            for (pat_store.pat_pool.slice(row.elems)) |elem| try addPatternBindingsToCompletions(gpa, items, owned, ast_unit, elem, kind);
            if (!row.rest_binding.isNone()) {
                try addPatternBindingsToCompletions(gpa, items, owned, ast_unit, patternFromOpt(row.rest_binding), kind);
            }
        },
        .Struct => {
            const row = pat_store.get(.Struct, pat_id);
            for (pat_store.field_pool.slice(row.fields)) |field_id| {
                const field = pat_store.StructField.get(field_id);
                try addPatternBindingsToCompletions(gpa, items, owned, ast_unit, field.pattern, kind);
            }
        },
        .VariantStruct => {
            const row = pat_store.get(.VariantStruct, pat_id);
            for (pat_store.field_pool.slice(row.fields)) |field_id| {
                const field = pat_store.StructField.get(field_id);
                try addPatternBindingsToCompletions(gpa, items, owned, ast_unit, field.pattern, kind);
            }
        },
        .VariantTuple => {
            const row = pat_store.get(.VariantTuple, pat_id);
            for (pat_store.pat_pool.slice(row.elems)) |elem| try addPatternBindingsToCompletions(gpa, items, owned, ast_unit, elem, kind);
        },
        .Or => {
            const row = pat_store.get(.Or, pat_id);
            for (pat_store.pat_pool.slice(row.alts)) |alt| try addPatternBindingsToCompletions(gpa, items, owned, ast_unit, alt, kind);
        },
        .At => {
            const row = pat_store.get(.At, pat_id);
            const name = ast_unit.pats.strs.get(row.binder);
            const copy = try gpa.dupe(u8, name);
            try owned.append(gpa, copy);
            try items.append(gpa, .{
                .label = copy,
                .kind = @intFromEnum(lspCompletionKindFromSemantic(kind)),
            });
            try addPatternBindingsToCompletions(gpa, items, owned, ast_unit, row.pattern, kind);
        },
        else => {},
    }
}

/// Generate a full semantic token response for the given document.
fn onSemanticTokensFull(out: *std.Io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, analysis: *AnalysisCache, id: u64, params: json.Value) !void {
    // Semantic tokens request payload describing the document to highlight.
    // Parameters payload used for full semantic tokens requests.
    var p = try json.parseFromValue(TextDocumentParams, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();

    const uri = p.value.textDocument.uri;
    // Response payload delivered for semantic token queries.
    const Resp = struct {
        jsonrpc: []const u8 = "2.0",
        id: u64,
        result: struct { data: []const u32 },
    };

    if (docs.get(uri)) |doc| {
        const data = computeSemanticTokens(gpa, uri, doc, analysis) catch |err| {
            std.debug.print("[lsp] computeSemanticTokens failed: {s}\n", .{@errorName(err)});
            const empty = [_]u32{};
            try writeJson(out, gpa, Resp{ .id = id, .result = .{ .data = &empty } });
            return;
        };
        defer gpa.free(data);
        try writeJson(out, gpa, Resp{ .id = id, .result = .{ .data = data } });
    } else {
        const empty = [_]u32{};
        try writeJson(out, gpa, Resp{ .id = id, .result = .{ .data = &empty } });
    }
}

/// Produce formatting edits for the document at `uri`.
fn onFormatting(out: *std.Io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, _: *AnalysisCache, id: u64, params: json.Value) !void {
    // Formatting request payload specifying the document URI.
    // Parameters payload for `textDocument/formatting` requests.
    var p = try json.parseFromValue(TextDocumentParams, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();

    const uri = p.value.textDocument.uri;

    const doc = docs.get(uri) orelse {
        // Response payload emitted when formatting cannot read the document.
        const Resp = struct {
            jsonrpc: []const u8 = "2.0",
            id: u64,
            result: []const TextEdit,
        };
        try writeJson(out, gpa, Resp{ .id = id, .result = emptyTextEdits });
        return;
    };
    const source = doc.text;

    const path = try fileUriToPath(gpa, uri);
    defer gpa.free(path);

    const source_z = try std.mem.concatWithSentinel(gpa, u8, &.{source}, 0);
    defer gpa.free(source_z);

    const formatted = lib.formatter.formatSource(gpa, source_z, path) catch |err| {
        std.debug.print("[lsp] formatter failed: {s}\n", .{@errorName(err)});
        // Response payload emitted when the formatter fails.
        const Resp = struct {
            jsonrpc: []const u8 = "2.0",
            id: u64,
            result: []const TextEdit,
        };
        try writeJson(out, gpa, Resp{ .id = id, .result = emptyTextEdits });
        return;
    };
    defer gpa.free(formatted);

    const edit = TextEdit{ .range = fullRange(source, doc.line_starts), .newText = formatted };
    const edits = [_]TextEdit{edit};
    // Response payload containing the formatting edits.
    const Resp = struct {
        jsonrpc: []const u8 = "2.0",
        id: u64,
        result: []const TextEdit,
    };
    try writeJson(out, gpa, Resp{ .id = id, .result = edits[0..] });
}

/// Run the checker and publish diagnostics for `uri`.
fn publishDiagnostics(out: *std.Io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, analysis: *AnalysisCache, uri: []const u8) !void {
    const doc = docs.get(uri) orelse {
        // Notification payload used when no diagnostics are available.
        const Msg = struct {
            jsonrpc: []const u8 = "2.0",
            method: []const u8 = "textDocument/publishDiagnostics",
            params: struct { uri: []const u8, diagnostics: []const LspDiagnostic },
        };
        const empty_diags = [_]LspDiagnostic{};
        try writeJson(out, gpa, Msg{ .params = .{ .uri = uri, .diagnostics = &empty_diags } });
        return;
    };
    const text: []const u8 = doc.text;

    const entry = try analysis.ensure(uri, doc) orelse {
        // Notification payload used when no diagnostics are available.
        const Msg = struct {
            jsonrpc: []const u8 = "2.0",
            method: []const u8 = "textDocument/publishDiagnostics",
            params: struct { uri: []const u8, diagnostics: []const LspDiagnostic },
        };
        const empty_diags = [_]LspDiagnostic{};
        try writeJson(out, gpa, Msg{ .params = .{ .uri = uri, .diagnostics = &empty_diags } });
        return;
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

    for (entry.context.diags.messages.items) |message| {
        if (message.loc.file_id != entry.file_id) continue;

        const msg_text = entry.context.diags.messageToOwnedSlice(gpa, message) catch |err| {
            std.debug.print("[lsp] failed to render diagnostic: {s}\n", .{@errorName(err)});
            continue;
        };

        var diag = LspDiagnostic{
            .range = locToRange(text, doc.line_starts, message.loc),
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
            if (note_loc.file_id != entry.file_id) continue;

            const note_msg = entry.context.diags.noteToOwnedSlice(gpa, note) catch |err| {
                std.debug.print("[lsp] failed to render note: {s}\n", .{@errorName(err)});
                continue;
            };

            try related.append(gpa, .{
                .location = .{ .uri = uri, .range = locToRange(text, doc.line_starts, note_loc) },
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

    // Notification payload used to publish diagnostics to the editor.
    const Msg = struct {
        jsonrpc: []const u8 = "2.0",
        method: []const u8 = "textDocument/publishDiagnostics",
        params: struct { uri: []const u8, diagnostics: []const LspDiagnostic },
    };
    try writeJson(out, gpa, Msg{ .params = .{ .uri = uri, .diagnostics = diags.items } });
}

/// Key describing a semantic token span.
const TokenKey = struct {
    start: usize,
    end: usize,
};

/// Semantic token record used when sorting/encoding tokens.
const TokenEntry = struct {
    start: usize,
    end: usize,
    kind: SemanticTokenKind,
};

/// Deduplicates and orders semantic tokens before encoding them for LSP.
const TokenAccumulator = struct {
    map: std.AutoArrayHashMap(TokenKey, SemanticTokenKind),
    gpa: std.mem.Allocator,

    /// Initialize a token accumulator that deduplicates semantic tokens.
    fn init(gpa: std.mem.Allocator) TokenAccumulator {
        return .{ .map = .init(gpa), .gpa = gpa };
    }

    /// Release resources held by the accumulator.
    fn deinit(self: *TokenAccumulator) void {
        self.map.deinit();
    }

    /// Record a semantic token covering `[start,end)` of `kind`.
    fn add(self: *TokenAccumulator, start: usize, end: usize, kind: SemanticTokenKind) !void {
        if (start >= end) return;
        const key = TokenKey{ .start = start, .end = end };
        const gop = try self.map.getOrPut(key);
        if (!gop.found_existing) {
            gop.value_ptr.* = kind;
        } else {
            const existing = gop.value_ptr.*;
            if (kindPriority(kind) > kindPriority(existing)) {
                gop.value_ptr.* = kind;
            }
        }
    }

    /// Return sorted token entries computed from accumulated ranges.
    fn toSortedEntries(self: *TokenAccumulator) ![]TokenEntry {
        const count = self.map.count();
        var out = try self.gpa.alloc(TokenEntry, count);
        errdefer self.gpa.free(out);

        var it = self.map.iterator();
        var idx: usize = 0;
        while (it.next()) |entry| {
            out[idx] = .{
                .start = entry.key_ptr.start,
                .end = entry.key_ptr.end,
                .kind = entry.value_ptr.*,
            };
            idx += 1;
        }

        std.sort.heap(TokenEntry, out, {}, struct {
            /// Sorting helper that orders token entries by start/end positions.
            fn lessThan(_: void, a: TokenEntry, b: TokenEntry) bool {
                if (a.start == b.start) return a.end < b.end;
                return a.start < b.start;
            }
        }.lessThan);

        return out;
    }

    /// Encode the accumulated tokens into the compact LSP semantic token format.
    fn toEncodedSlice(self: *TokenAccumulator, text: []const u8, line_starts: []const usize) ![]u32 {
        const entries = try self.toSortedEntries();
        defer self.gpa.free(entries);

        var data = std.ArrayList(u32){};
        errdefer data.deinit(self.gpa);

        var have_prev = false;
        var last_line: u32 = 0;
        var last_char: u32 = 0;

        for (entries) |entry| {
            const pos = offsetToPosition(text, entry.start, line_starts);
            const seg_len = entry.end - entry.start;

            const delta_line: u32 = if (have_prev) pos.line - last_line else pos.line;
            var delta_start: u32 = pos.character;
            if (have_prev and delta_line == 0) {
                delta_start = pos.character - last_char;
            }

            try data.append(self.gpa, delta_line);
            try data.append(self.gpa, delta_start);
            try data.append(self.gpa, @intCast(seg_len));
            try data.append(self.gpa, @as(u32, @intFromEnum(entry.kind)));
            try data.append(self.gpa, 0);

            have_prev = true;
            last_line = pos.line;
            last_char = pos.character;
        }

        return try data.toOwnedSlice(self.gpa);
    }
};

/// Assign a priority used to resolve overlapping tokens.
fn kindPriority(kind: SemanticTokenKind) u8 {
    return switch (kind) {
        .function, .type, .namespace, .variable, .property, .parameter, .enum_member => 2,
        else => 1,
    };
}

/// Add a multi-line segment `kind` spanning `[start,end)` to `tokens`.
fn addSegmentMultiLine(tokens: *TokenAccumulator, text: []const u8, start: usize, end: usize, kind: SemanticTokenKind) !void {
    var seg_start = start;
    var idx = start;
    while (idx < end) {
        const c = text[idx];
        if (c == '\n' or c == '\r') {
            if (seg_start < idx) {
                try tokens.add(seg_start, idx, kind);
            }
            if (c == '\r' and idx + 1 < end and text[idx + 1] == '\n') {
                idx += 1;
            }
            idx += 1;
            seg_start = idx;
        } else {
            idx += 1;
        }
    }

    if (seg_start < end) {
        try tokens.add(seg_start, end, kind);
    }
}

/// Compute semantic tokens for `text` and return their LSP encoding.
fn computeSemanticTokens(gpa: std.mem.Allocator, uri: []const u8, doc: *const DocumentStore.Document, analysis: *AnalysisCache) ![]u32 {
    const text = doc.text;
    if (text.len == 0) {
        return &[_]u32{};
    }

    var tokens: TokenAccumulator = .init(gpa);
    defer tokens.deinit();

    try collectLexicalTokens(&tokens, doc);

    if (try analysis.ensure(uri, doc)) |entry| {
        if (entry.ast_unit) |ast_unit| {
            try gatherAstTokens(&tokens, gpa, text, ast_unit, entry.file_id, &entry.resolution_map);
        }
    }

    return try tokens.toEncodedSlice(text, doc.line_starts);
}

/// Collect lexical tokens from `text` into `tokens`.
fn collectLexicalTokens(tokens: *TokenAccumulator, doc: *const DocumentStore.Document) !void {
    const text = doc.text;
    if (text.len == 0) return;

    var tokenizer: lib.lexer.Tokenizer = .init(doc.z_text, 0, .normal);
    while (true) {
        const tok = tokenizer.next();
        if (tok.tag == .eof) break;

        const kind = classifyLexTokenTag(tok.tag) orelse continue;
        const start = clampOffset(text, tok.loc.start);
        const end = clampOffset(text, tok.loc.end);
        if (start >= end) continue;
        try addSegmentMultiLine(tokens, text, start, end, kind);
    }
}

/// Gather semantic tokens from the AST and add them to `tokens`.
fn gatherAstTokens(tokens: *TokenAccumulator, gpa: std.mem.Allocator, text: []const u8, ast_unit: *ast.Ast, file_id: u32, resolution_map: *const std.AutoArrayHashMap(u32, Symbol)) !void {
    try highlightPackage(tokens, text, ast_unit, file_id);
    try highlightDecls(tokens, text, ast_unit, file_id);
    try highlightExpressions(tokens, gpa, text, ast_unit, file_id, resolution_map);
}

/// Resolve symbols for `ast_unit` and return the populated map.
fn buildResolutionMap(gpa: std.mem.Allocator, ast_unit: *ast.Ast) !std.AutoArrayHashMap(u32, Symbol) {
    var map: std.AutoArrayHashMap(u32, Symbol) = .init(gpa);
    try SymbolResolver.run(gpa, ast_unit, &map);
    return map;
}

/// Highlight function/closure signature (result + parameters).
fn highlightFunctionSignature(
    tokens: *TokenAccumulator,
    text: []const u8,
    ast_unit: *ast.Ast,
    file_id: u32,
    params_range: ast.RangeParam,
    result_ty: ?ast.ExprId,
    binding_kind: SemanticTokenKind,
) !void {
    const expr_store = &ast_unit.exprs;

    if (result_ty) |ty| {
        try highlightTypeExpr(tokens, text, ast_unit, file_id, ty);
    }

    const params = expr_store.param_pool.slice(params_range);
    for (params) |param_id| {
        const param = expr_store.Param.get(param_id);
        if (!param.ty.isNone()) {
            try highlightTypeExpr(tokens, text, ast_unit, file_id, param.ty.unwrap());
        }
        if (!param.pat.isNone()) {
            const pat_id = patternFromOpt(param.pat);
            try highlightPattern(tokens, text, ast_unit, pat_id, binding_kind, file_id);
        }
    }
}

/// Highlight package declarations within `ast_unit`.
fn highlightPackage(tokens: *TokenAccumulator, text: []const u8, ast_unit: *ast.Ast, file_id: u32) !void {
    if (ast_unit.unit.package_loc.isNone()) return;
    const loc_idx = ast_unit.unit.package_loc.unwrap();
    const loc_id = ast.LocId.fromRaw(loc_idx.toRaw());
    try highlightLoc(tokens, text, ast_unit.exprs.locs, loc_id, file_id, .namespace);
}

/// Highlight top-level declarations and add to `tokens`.
fn highlightDecls(tokens: *TokenAccumulator, text: []const u8, ast_unit: *ast.Ast, file_id: u32) !void {
    const decl_ids = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);
    for (decl_ids) |decl_id| {
        const row = ast_unit.exprs.Decl.get(decl_id);
        const decl_kind = classifyDeclKind(ast_unit, row.value);

        if (!row.ty.isNone()) {
            try highlightTypeExpr(tokens, text, ast_unit, file_id, row.ty.unwrap());
        }

        if (!row.pattern.isNone()) {
            const pat_id = patternFromOpt(row.pattern);
            try highlightPattern(tokens, text, ast_unit, pat_id, decl_kind, file_id);
        }

        if (!row.method_path.isNone()) {
            const seg_ids = ast_unit.exprs.method_path_pool.slice(row.method_path.asRange());
            var i: usize = 0;
            while (i < seg_ids.len) : (i += 1) {
                const seg_id = seg_ids[i];
                const seg = ast_unit.exprs.MethodPathSeg.get(seg_id);
                const seg_kind = if (i + 1 == seg_ids.len) decl_kind else .type;
                try highlightLoc(tokens, text, ast_unit.exprs.locs, seg.loc, file_id, seg_kind);
            }
        }
    }
}

/// Collect binding identifiers introduced by `pat_id`.
fn collectPatternBindingNames(gpa: std.mem.Allocator, names: *std.StringHashMap(void), ast_unit: *ast.Ast, pat_id: ast.PatternId) !void {
    const pat_store = &ast_unit.pats;
    const pat_kind = pat_store.kind(pat_id);
    switch (pat_kind) {
        .Binding => {
            const row = pat_store.get(.Binding, pat_id);
            try names.put(ast_unit.exprs.strs.get(row.name), {});
        },
        .Tuple => {
            const row = pat_store.get(.Tuple, pat_id);
            const elems = pat_store.pat_pool.slice(row.elems);
            for (elems) |elem| try collectPatternBindingNames(gpa, names, ast_unit, elem);
        },
        .Slice => {
            const row = pat_store.get(.Slice, pat_id);
            const elems = pat_store.pat_pool.slice(row.elems);
            for (elems) |elem| try collectPatternBindingNames(gpa, names, ast_unit, elem);
            if (!row.rest_binding.isNone()) {
                try collectPatternBindingNames(gpa, names, ast_unit, patternFromOpt(row.rest_binding));
            }
        },
        .Struct => {
            const row = pat_store.get(.Struct, pat_id);
            const fields = pat_store.field_pool.slice(row.fields);
            for (fields) |field_id| {
                const field = pat_store.StructField.get(field_id);
                try collectPatternBindingNames(gpa, names, ast_unit, field.pattern);
            }
        },
        .VariantStruct => {
            const row = pat_store.get(.VariantStruct, pat_id);
            const fields = pat_store.field_pool.slice(row.fields);
            for (fields) |field_id| {
                const field = pat_store.StructField.get(field_id);
                try collectPatternBindingNames(gpa, names, ast_unit, field.pattern);
            }
        },
        .VariantTuple => {
            const row = pat_store.get(.VariantTuple, pat_id);
            const elems = pat_store.pat_pool.slice(row.elems);
            for (elems) |elem| try collectPatternBindingNames(gpa, names, ast_unit, elem);
        },
        .Or => {
            const row = pat_store.get(.Or, pat_id);
            const alts = pat_store.pat_pool.slice(row.alts);
            for (alts) |alt| try collectPatternBindingNames(gpa, names, ast_unit, alt);
        },
        .At => {
            const row = pat_store.get(.At, pat_id);
            try names.put(ast_unit.exprs.strs.get(row.binder), {});
            try collectPatternBindingNames(gpa, names, ast_unit, row.pattern);
        },
        else => {},
    }
}

/// Collect descriptors for every parameter declared in the AST.
fn collectAllParamNames(gpa: std.mem.Allocator, names: *std.StringHashMap(void), ast_unit: *ast.Ast) !void {
    const expr_store = &ast_unit.exprs;
    const kinds_len = expr_store.index.kinds.items.len;
    var idx: usize = 0;
    while (idx < kinds_len) : (idx += 1) {
        const expr_id = ast.ExprId.fromRaw(@intCast(idx));
        const expr_kind = expr_store.kind(expr_id);
        switch (expr_kind) {
            .FunctionLit => {
                const fn_row = expr_store.get(.FunctionLit, expr_id);
                const params = expr_store.param_pool.slice(fn_row.params);
                for (params) |param_id| {
                    const param = expr_store.Param.get(param_id);
                    if (!param.pat.isNone()) {
                        try collectPatternBindingNames(gpa, names, ast_unit, patternFromOpt(param.pat));
                    }
                }
            },
            .Closure => {
                const cl_row = expr_store.get(.Closure, expr_id);
                const params = expr_store.param_pool.slice(cl_row.params);
                for (params) |param_id| {
                    const param = expr_store.Param.get(param_id);
                    if (!param.pat.isNone()) {
                        try collectPatternBindingNames(gpa, names, ast_unit, patternFromOpt(param.pat));
                    }
                }
            },
            else => {},
        }
    }
}

/// Highlight type expressions as semantic tokens.
fn highlightTypeExpr(tokens: *TokenAccumulator, text: []const u8, ast_unit: *ast.Ast, file_id: u32, expr_id: ast.ExprId) !void {
    const expr_store = &ast_unit.exprs;
    const expr_kind = expr_store.kind(expr_id);
    switch (expr_kind) {
        .Ident => {
            const row = expr_store.get(.Ident, expr_id);
            try highlightLoc(tokens, text, expr_store.locs, row.loc, file_id, .type);
        },
        .PointerType => {
            const row = expr_store.get(.PointerType, expr_id);
            try highlightTypeExpr(tokens, text, ast_unit, file_id, row.elem);
        },
        .OptionalType => {
            const row = expr_store.get(.OptionalType, expr_id);
            try highlightTypeExpr(tokens, text, ast_unit, file_id, row.elem);
        },
        .SliceType => {
            const row = expr_store.get(.SliceType, expr_id);
            try highlightTypeExpr(tokens, text, ast_unit, file_id, row.elem);
        },
        .ArrayType => {
            const row = expr_store.get(.ArrayType, expr_id);
            try highlightTypeExpr(tokens, text, ast_unit, file_id, row.elem);
        },
        .DynArrayType => {
            const row = expr_store.get(.DynArrayType, expr_id);
            try highlightTypeExpr(tokens, text, ast_unit, file_id, row.elem);
        },
        .MapType => {
            const row = expr_store.get(.MapType, expr_id);
            try highlightTypeExpr(tokens, text, ast_unit, file_id, row.key);
            try highlightTypeExpr(tokens, text, ast_unit, file_id, row.value);
        },
        .TupleType => {
            const row = expr_store.get(.TupleType, expr_id);
            const elems = expr_store.expr_pool.slice(row.elems);
            for (elems) |elem| try highlightTypeExpr(tokens, text, ast_unit, file_id, elem);
        },
        .ErrorSetType => {
            const row = expr_store.get(.ErrorSetType, expr_id);
            try highlightTypeExpr(tokens, text, ast_unit, file_id, row.err);
            try highlightTypeExpr(tokens, text, ast_unit, file_id, row.value);
        },
        .FieldAccess => { // For qualified type names like `my_module.MyType`
            const row = expr_store.get(.FieldAccess, expr_id);
            try highlightTypeExpr(tokens, text, ast_unit, file_id, row.parent);
            try highlightLoc(tokens, text, expr_store.locs, row.loc, file_id, .type);
        },
        else => {},
    }
}

/// Highlight expressions and binding occurrences in `ast_unit`.
fn highlightExpressions(tokens: *TokenAccumulator, gpa: std.mem.Allocator, text: []const u8, ast_unit: *ast.Ast, file_id: u32, resolution_map: *const std.AutoArrayHashMap(u32, Symbol)) !void {
    _ = gpa;
    const expr_store = &ast_unit.exprs;
    const kinds_len = expr_store.index.kinds.items.len;
    const expr_types = ast_unit.type_info.expr_types.items;
    const type_store = ast_unit.type_info.store;

    var idx: usize = 0;
    expr_loop: while (idx < kinds_len) : (idx += 1) {
        const expr_id = ast.ExprId.fromRaw(@intCast(idx));
        const expr_kind = expr_store.kind(expr_id);
        switch (expr_kind) {
            .Ident => {
                const row = expr_store.get(.Ident, expr_id);
                const loc = expr_store.locs.get(row.loc);
                if (loc.file_id != file_id) continue :expr_loop;
                const start = clampOffset(text, loc.start);
                const end = clampOffset(text, loc.end);

                var kind: SemanticTokenKind = undefined;
                if (resolution_map.get(expr_id.toRaw())) |symbol| {
                    kind = symbol.kind;
                } else {
                    const ty_opt = if (idx < expr_types.len) expr_types[idx] else null;
                    kind = classifyIdentType(type_store, ty_opt);
                }
                try addSegmentMultiLine(tokens, text, start, end, kind);
            },
            .FieldAccess => {
                const row = expr_store.get(.FieldAccess, expr_id);
                const loc = expr_store.locs.get(row.loc);
                if (loc.file_id != file_id) continue :expr_loop;

                const parent_ty_opt = getExprType(ast_unit, row.parent);
                var is_enum_access = false;
                if (parent_ty_opt) |parent_ty_id| {
                    const parent_ty_kind = type_store.getKind(parent_ty_id);
                    if (parent_ty_kind == .Enum) {
                        is_enum_access = true;
                    } else if (parent_ty_kind == .TypeType) {
                        // It could be access on the type itself, e.g. EnumType.member
                        const inner_ty_id = type_store.get(.TypeType, parent_ty_id).of;
                        if (type_store.getKind(inner_ty_id) == .Enum) {
                            is_enum_access = true;
                        }
                    }
                }

                const start = clampOffset(text, loc.start);
                const end = clampOffset(text, loc.end);
                const ty_opt = if (idx < expr_types.len) expr_types[idx] else null;

                var kind = classifyMemberAccessType(type_store, ty_opt);
                if (is_enum_access) {
                    kind = .enum_member;
                }

                try addSegmentMultiLine(tokens, text, start, end, kind);
            },
            .For => {
                const row = expr_store.get(.For, expr_id);
                try highlightPattern(tokens, text, ast_unit, row.pattern, .variable, file_id);
            },
            .Match => {
                const row = expr_store.get(.Match, expr_id);
                const arms = expr_store.arm_pool.slice(row.arms);
                for (arms) |arm_id| {
                    const arm = expr_store.MatchArm.get(arm_id);
                    try highlightPattern(tokens, text, ast_unit, arm.pattern, .variable, file_id);
                }
            },
            .While => {
                const row = expr_store.get(.While, expr_id);
                if (row.is_pattern) {
                    if (!row.pattern.isNone()) {
                        const pat_id = patternFromOpt(row.pattern);
                        try highlightPattern(tokens, text, ast_unit, pat_id, .variable, file_id);
                    }
                }
            },
            .Catch => {
                const row = expr_store.get(.Catch, expr_id);
                if (row.binding_loc.isNone()) continue :expr_loop;
                const loc_id = ast.LocId.fromRaw(row.binding_loc.unwrap().toRaw());
                try highlightLoc(tokens, text, expr_store.locs, loc_id, file_id, .variable);
            },
            .FunctionLit => {
                const fn_row = expr_store.get(.FunctionLit, expr_id);
                const result_ty_opt = exprFromOpt(fn_row.result_ty);
                try highlightFunctionSignature(tokens, text, ast_unit, file_id, fn_row.params, result_ty_opt, .parameter);
            },
            .Closure => {
                const cl_row = expr_store.get(.Closure, expr_id);
                const result_ty_opt = exprFromOpt(cl_row.result_ty);
                try highlightFunctionSignature(tokens, text, ast_unit, file_id, cl_row.params, result_ty_opt, .parameter);
            },
            .StructType => {
                const struct_row = expr_store.get(.StructType, expr_id);
                const fields = expr_store.sfield_pool.slice(struct_row.fields);
                for (fields) |field_id| {
                    const field = expr_store.StructField.get(field_id);
                    try highlightLoc(tokens, text, expr_store.locs, field.loc, file_id, .property);
                    try highlightTypeExpr(tokens, text, ast_unit, file_id, field.ty);
                }
            },
            .EnumType => {
                const enum_row = expr_store.get(.EnumType, expr_id);
                if (!enum_row.discriminant.isNone()) {
                    try highlightTypeExpr(tokens, text, ast_unit, file_id, enum_row.discriminant.unwrap());
                }
                const fields = expr_store.efield_pool.slice(enum_row.fields);
                for (fields) |field_id| {
                    const field = expr_store.EnumField.get(field_id);
                    try highlightLoc(tokens, text, expr_store.locs, field.loc, file_id, .enum_member);
                }
            },
            .VariantType => {
                const variant_row = expr_store.get(.VariantType, expr_id);
                const fields = expr_store.vfield_pool.slice(variant_row.fields);
                for (fields) |field_id| {
                    const field = expr_store.VariantField.get(field_id);
                    try highlightLoc(tokens, text, expr_store.locs, field.loc, file_id, .enum_member);
                    if (!field.payload_elems.isNone()) {
                        const elems = expr_store.expr_pool.slice(field.payload_elems.asRange());
                        for (elems) |elem_id| {
                            try highlightTypeExpr(tokens, text, ast_unit, file_id, elem_id);
                        }
                    }
                    if (!field.payload_fields.isNone()) {
                        const sfields = expr_store.sfield_pool.slice(field.payload_fields.asRange());
                        for (sfields) |sfield_id| {
                            const sfield = expr_store.StructField.get(sfield_id);
                            try highlightTypeExpr(tokens, text, ast_unit, file_id, sfield.ty);
                        }
                    }
                }
            },
            .ErrorType => {
                const err_row = expr_store.get(.ErrorType, expr_id);
                const fields = expr_store.vfield_pool.slice(err_row.fields);
                for (fields) |field_id| {
                    const field = expr_store.VariantField.get(field_id);
                    try highlightLoc(tokens, text, expr_store.locs, field.loc, file_id, .enum_member);
                    if (!field.payload_elems.isNone()) {
                        const elems = expr_store.expr_pool.slice(field.payload_elems.asRange());
                        for (elems) |elem_id| {
                            try highlightTypeExpr(tokens, text, ast_unit, file_id, elem_id);
                        }
                    }
                    if (!field.payload_fields.isNone()) {
                        const sfields = expr_store.sfield_pool.slice(field.payload_fields.asRange());
                        for (sfields) |sfield_id| {
                            const sfield = expr_store.StructField.get(sfield_id);
                            try highlightTypeExpr(tokens, text, ast_unit, file_id, sfield.ty);
                        }
                    }
                }
            },
            .UnionType => {
                const union_row = expr_store.get(.UnionType, expr_id);
                const fields = expr_store.sfield_pool.slice(union_row.fields);
                for (fields) |field_id| {
                    const field = expr_store.StructField.get(field_id);
                    try highlightLoc(tokens, text, expr_store.locs, field.loc, file_id, .property);
                    try highlightTypeExpr(tokens, text, ast_unit, file_id, field.ty);
                }
            },
            .StructLit => {
                const lit_row = expr_store.get(.StructLit, expr_id);
                const fields = expr_store.sfv_pool.slice(lit_row.fields);
                for (fields) |field_id| {
                    const field = expr_store.StructFieldValue.get(field_id);
                    if (field.name.isNone()) continue;
                    try highlightLoc(tokens, text, expr_store.locs, field.loc, file_id, .property);
                }
            },
            else => {},
        }
    }
}

/// Classify the semantic kind for a declaration represented by `value_expr`.
fn classifyDeclKind(ast_unit: *ast.Ast, value_expr: ast.ExprId) SemanticTokenKind {
    const expr_store = &ast_unit.exprs;
    const expr_kind = expr_store.kind(value_expr);
    return switch (expr_kind) {
        .FunctionLit => .function,
        .StructType,
        .EnumType,
        .VariantType,
        .ErrorType,
        .UnionType,
        => .type,
        else => blk: {
            const ty_opt = getExprType(ast_unit, value_expr);
            if (ty_opt) |ty| {
                const type_kind = ast_unit.type_info.store.getKind(ty);
                if (type_kind == .TypeType) break :blk .type;
            }
            break :blk .variable;
        },
    };
}

/// Map lexical token tags to semantic token kinds when possible.
fn classifyLexTokenTag(tag: lib.lexer.Token.Tag) ?SemanticTokenKind {
    return switch (tag) {
        .string_literal, .raw_string_literal, .char_literal, .raw_asm_block => .string,
        .integer_literal, .float_literal, .imaginary_literal => .number,
        .doc_comment, .container_doc_comment => .comment,
        .plus, .minus, .star, .slash, .percent, .caret, .bang, .b_and, .b_or, .ltlt, .gtgt, .plus_equal, .minus_equal, .rarrow, .star_equal, .slash_equal, .percent_equal, .caret_equal, .and_equal, .or_equal, .shl_equal, .shr_equal, .shl_pipe, .shl_pipe_equal, .plus_pipe, .plus_pipe_equal, .minus_pipe, .minus_pipe_equal, .star_pipe, .star_pipe_equal, .plus_percent, .plus_percent_equal, .minus_percent, .minus_percent_equal, .star_percent, .star_percent_equal, .equal, .equal_equal, .not_equal, .greater_than, .less_than, .greater_equal, .less_equal => .operator,
        .dot, .dotdot, .dotstar, .dotdotdot, .dotdoteq, .fatarrow, .question => .operator,
        else => if (isKeywordTag(tag)) .keyword else null,
    };
}

/// Determine a semantic kind from `ty_opt` when classifying identifiers.
fn classifyIdentType(type_store: *types.TypeStore, ty_opt: ?types.TypeId) SemanticTokenKind {
    if (ty_opt) |ty| {
        return switch (type_store.getKind(ty)) {
            .Function => .function,
            .TypeType => .type,
            .Ast => .namespace,
            else => .variable,
        };
    }
    return .variable;
}

/// Classify a semantic kind for member access based on `ty_opt`.
fn classifyMemberAccessType(type_store: *types.TypeStore, ty_opt: ?types.TypeId) SemanticTokenKind {
    if (ty_opt) |ty| {
        return switch (type_store.getKind(ty)) {
            .Function => .function,
            .TypeType => .type,
            .Ast => .namespace,
            else => .property,
        };
    }
    return .property;
}

/// Highlight the nodes inside pattern expressions for semantic tokens.
fn highlightPattern(
    tokens: *TokenAccumulator,
    text: []const u8,
    ast_unit: *ast.Ast,
    pat_id: ast.PatternId,
    binding_kind: SemanticTokenKind,
    file_id: u32,
) !void {
    const pat_store = &ast_unit.pats;
    const locs = ast_unit.exprs.locs;
    const pat_kind = pat_store.kind(pat_id);
    switch (pat_kind) {
        .Binding => {
            const row = pat_store.get(.Binding, pat_id);
            try highlightLoc(tokens, text, locs, row.loc, file_id, binding_kind);
        },
        .Tuple => {
            const row = pat_store.get(.Tuple, pat_id);
            const elems = pat_store.pat_pool.slice(row.elems);
            for (elems) |elem| try highlightPattern(tokens, text, ast_unit, elem, binding_kind, file_id);
        },
        .Slice => {
            const row = pat_store.get(.Slice, pat_id);
            const elems = pat_store.pat_pool.slice(row.elems);
            for (elems) |elem| try highlightPattern(tokens, text, ast_unit, elem, binding_kind, file_id);
            if (!row.rest_binding.isNone()) {
                const rest_id = patternFromOpt(row.rest_binding);
                try highlightPattern(tokens, text, ast_unit, rest_id, binding_kind, file_id);
            }
        },
        .Struct => {
            const row = pat_store.get(.Struct, pat_id);
            try highlightPatternPath(tokens, text, ast_unit, row.path, file_id);
            const fields = pat_store.field_pool.slice(row.fields);
            for (fields) |field_id| {
                const field = pat_store.StructField.get(field_id);
                try highlightLoc(tokens, text, locs, field.loc, file_id, .property);
                try highlightPattern(tokens, text, ast_unit, field.pattern, binding_kind, file_id);
            }
        },
        .VariantStruct => {
            const row = pat_store.get(.VariantStruct, pat_id);
            try highlightPatternPath(tokens, text, ast_unit, row.path, file_id);
            const fields = pat_store.field_pool.slice(row.fields);
            for (fields) |field_id| {
                const field = pat_store.StructField.get(field_id);
                try highlightLoc(tokens, text, locs, field.loc, file_id, .property);
                try highlightPattern(tokens, text, ast_unit, field.pattern, binding_kind, file_id);
            }
        },
        .VariantTuple => {
            const row = pat_store.get(.VariantTuple, pat_id);
            try highlightPatternPath(tokens, text, ast_unit, row.path, file_id);
            const elems = pat_store.pat_pool.slice(row.elems);
            for (elems) |elem| try highlightPattern(tokens, text, ast_unit, elem, binding_kind, file_id);
        },
        .Path => {
            const row = pat_store.get(.Path, pat_id);
            try highlightPatternPath(tokens, text, ast_unit, row.segments, file_id);
        },
        .Literal => {},
        .Range => {},
        .Or => {
            const row = pat_store.get(.Or, pat_id);
            const alts = pat_store.pat_pool.slice(row.alts);
            for (alts) |alt| try highlightPattern(tokens, text, ast_unit, alt, binding_kind, file_id);
        },
        .At => {
            const row = pat_store.get(.At, pat_id);
            try highlightPattern(tokens, text, ast_unit, row.pattern, binding_kind, file_id);
        },
        else => {},
    }
}

/// Convert `OptPatternId` to `PatternId` using sentinel lookup.
fn patternFromOpt(opt: ast.OptPatternId) ast.PatternId {
    std.debug.assert(!opt.isNone());
    const idx = opt.unwrap();
    return ast.PatternId.fromRaw(idx.toRaw());
}

fn exprFromOpt(opt: ast.OptExprId) ?ast.ExprId {
    if (opt.isNone()) return null;
    const idx = opt.unwrap();
    return ast.ExprId.fromRaw(idx.toRaw());
}

/// Highlight each segment of an identifier path used in semantic tokens.
fn highlightPatternPath(tokens: *TokenAccumulator, text: []const u8, ast_unit: *ast.Ast, path: ast.RangePathSeg, file_id: u32) !void {
    const pat_store = &ast_unit.pats;
    const segs = pat_store.seg_pool.slice(path);
    for (segs) |seg_id| {
        const seg = pat_store.PathSeg.get(seg_id);
        try highlightLoc(tokens, text, ast_unit.exprs.locs, seg.loc, file_id, .type);
    }
}

/// Highlight the location `loc` as a semantic token.
fn highlightLoc(
    tokens: *TokenAccumulator,
    text: []const u8,
    locs: *const ast.LocStore,
    loc_id: ast.LocId,
    file_id: u32,
    kind: SemanticTokenKind,
) !void {
    const loc = locs.get(loc_id);
    if (loc.file_id != file_id) return;
    const start = clampOffset(text, loc.start);
    const end = clampOffset(text, loc.end);
    if (start >= end) return;
    try addSegmentMultiLine(tokens, text, start, end, kind);
}

/// Return true when `tag` corresponds to an LSP keyword token.
fn isKeywordTag(tag: lib.lexer.Token.Tag) bool {
    return @intFromEnum(tag) >= @intFromEnum(lib.lexer.Token.Tag.keyword_align);
}

/// Convert URI strings to filesystem paths.
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

/// Return the numeric value of hexadecimal digit `c`.
fn hexDigit(c: u8) ?u8 {
    return switch (c) {
        '0'...'9' => c - '0',
        'a'...'f' => c - 'a' + 10,
        'A'...'F' => c - 'A' + 10,
        else => null,
    };
}

/// Build a list of line start offsets for `text`.
fn buildLineStarts(gpa: std.mem.Allocator, text: []const u8) ![]usize {
    var starts = std.ArrayList(usize){};
    errdefer starts.deinit(gpa);
    try starts.append(gpa, 0);

    var i: usize = 0;
    while (i < text.len) : (i += 1) {
        const c = text[i];
        if (c == '\n') {
            try starts.append(gpa, i + 1);
        } else if (c == '\r') {
            if (i + 1 < text.len and text[i + 1] == '\n') {
                i += 1;
            }
            try starts.append(gpa, i + 1);
        }
    }

    return starts.toOwnedSlice(gpa);
}

/// Convert `loc` into an LSP `Range` relative to `text`.
fn locToRange(text: []const u8, line_starts: []const usize, loc: Loc) LspRange {
    const start_idx = clampOffset(text, loc.start);
    const raw_end = if (loc.end > loc.start) loc.end else loc.start;
    const end_idx = clampOffset(text, raw_end);

    return .{
        .start = offsetToPosition(text, start_idx, line_starts),
        .end = offsetToPosition(text, end_idx, line_starts),
    };
}

/// Allocate a zero-terminated copy of `text`.
fn buildZeroTerminated(gpa: std.mem.Allocator, text: []const u8) ![:0]u8 {
    const buf = try gpa.allocSentinel(u8, text.len, 0);
    @memcpy(buf[0..text.len], text);
    return buf;
}

/// Return the `LspRange` covering the entire `text`.
fn fullRange(text: []const u8, line_starts: []const usize) LspRange {
    return .{
        .start = .{ .line = 0, .character = 0 },
        .end = offsetToPosition(text, text.len, line_starts),
    };
}

/// Clamp `offset` to the bounds of `text`.
fn clampOffset(text: []const u8, offset: usize) usize {
    if (offset > text.len) return text.len;
    return offset;
}

/// Convert byte `offset` inside `text` to an LSP position (line/char).
fn offsetToPosition(text: []const u8, offset_in: usize, line_starts: []const usize) LspPosition {
    const offset = clampOffset(text, offset_in);
    // line_starts are sorted; find greatest start <= offset.
    var low: usize = 0;
    var high: usize = line_starts.len;
    while (low + 1 < high) {
        const mid = low + (high - low) / 2;
        if (line_starts[mid] > offset) {
            high = mid;
        } else {
            low = mid;
        }
    }
    const line_start = line_starts[low];
    const character = offset - line_start;
    return .{ .line = @intCast(low), .character = @intCast(character) };
}

/// Translate diagnostic `Severity` into LSP severity codes.
fn severityToLsp(sev: Severity) ?u32 {
    return switch (sev) {
        .err => 1,
        .warning => 2,
        .note => 3,
    };
}

/// Resolve alias/indirection of `type_id` to its concrete type.
fn resolvePointer(type_store: *types.TypeStore, type_id: types.TypeId) types.TypeId {
    var current_id = type_id;
    while (type_store.getKind(current_id) == .Ptr) {
        const ptr_row = type_store.get(.Ptr, current_id);
        current_id = ptr_row.elem;
    }
    return current_id;
}

/// Print the struct `fields_range` into hover output.
fn printHoverFields(writer: *std.io.Writer, type_store: *types.TypeStore, fields_range: types.RangeField) !void {
    const fields = type_store.field_pool.slice(fields_range);
    if (fields.len > 0) {
        try writer.print("\n\n---\n", .{});
        for (fields) |field_id| {
            const field_row = type_store.Field.get(field_id);
            const field_name = type_store.strs.get(field_row.name);
            try writer.print("{s}: ", .{field_name});
            try type_store.formatTypeForDiagnostic(field_row.ty, .{}, writer);
            try writer.print("\n", .{});
        }
    }
}

/// Compute hover message for offset `offset_in`.
fn computeHover(gpa: std.mem.Allocator, doc: *const DocumentStore.Document, entry: *AnalysisCache.Entry, offset_in: usize) !?HoverInfo {
    const text = doc.text;
    const offset = if (offset_in > text.len) text.len else offset_in;
    const ast_unit = entry.ast_unit orelse return null;
    const expr_id = findExprAt(ast_unit, offset) orelse return null;
    const loc = exprLoc(ast_unit, expr_id);

    var msg_builder: std.Io.Writer.Allocating = .init(gpa);
    defer msg_builder.deinit();
    const writer = &msg_builder.writer;

    if (entry.resolution_map.get(expr_id.toRaw())) |symbol| {
        const decl_loc = ast_unit.exprs.locs.get(symbol.decl_loc);
        const decl_file_id = decl_loc.file_id;

        const decl_text = entry.context.source_manager.read(decl_file_id) catch return null;
        defer gpa.free(decl_text);

        const start_offset = decl_loc.start;
        var line_start = start_offset;
        while (line_start > 0 and decl_text[line_start - 1] != '\n') {
            line_start -= 1;
        }
        var line_end = start_offset;
        while (line_end < decl_text.len and decl_text[line_end] != '\n') {
            line_end += 1;
        }

        const decl_line = std.mem.trim(u8, decl_text[line_start..line_end], " \t\r");

        try writer.print("```sr\n{s}\n```", .{decl_line});

        if (getExprType(ast_unit, expr_id)) |type_id| {
            try writer.print("\n\n---\n\n", .{});
            try writer.print("```sr\n", .{});
            try entry.context.type_store.formatTypeForDiagnostic(type_id, .{}, writer);
            try writer.print("\n```", .{});
        }

        const message = try msg_builder.toOwnedSlice();
        return HoverInfo{
            .message = message,
            .range = locToRange(text, doc.line_starts, loc),
        };
    }

    // Fallback for unresolved symbols
    if (getExprType(ast_unit, expr_id)) |type_id| {
        try writer.print("```sr\n", .{});
        try entry.context.type_store.formatTypeForDiagnostic(type_id, .{}, writer);
        try writer.print("\n```", .{});
        const message = try msg_builder.toOwnedSlice();
        return HoverInfo{
            .message = message,
            .range = locToRange(text, doc.line_starts, loc),
        };
    }

    return null;
}

/// Return the AST corresponding to `file_id` inside `unit`, if loaded.
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

/// Find the expression at byte `offset` in `ast_unit`, if any.
fn findExprAt(ast_unit: *ast.Ast, offset: usize) ?ast.ExprId {
    const total = ast_unit.exprs.index.kinds.items.len;
    var best: ?ast.ExprId = null;
    var best_span: usize = std.math.maxInt(usize);

    var i: usize = 0;
    while (i < total) : (i += 1) {
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

/// Return the location metadata for expression `expr_id`.
fn exprLoc(ast_unit: *ast.Ast, expr_id: ast.ExprId) Loc {
    const kind = ast_unit.kind(expr_id);
    return switch (kind) {
        inline else => |k| blk: {
            const row = ast_unit.exprs.get(k, expr_id);
            break :blk ast_unit.exprs.locs.get(row.loc);
        },
    };
}

/// Lookup the inferred type of `expr_id`, if available.
fn getExprType(ast_unit: *ast.Ast, expr_id: ast.ExprId) ?types.TypeId {
    const idx = expr_id.toRaw();
    if (idx >= ast_unit.type_info.expr_types.items.len) return null;
    return ast_unit.type_info.expr_types.items[idx];
}

/// Convert LSP position to byte offset within `text`.
fn positionToOffset(text: []const u8, target_line: u32, target_character: u32, line_starts: []const usize) usize {
    if (line_starts.len == 0) return 0;
    const line_idx: usize = if (target_line < line_starts.len) @intCast(target_line) else line_starts.len - 1;
    const start = line_starts[line_idx];
    if (start >= text.len) return text.len;

    // Clamp character within the line.
    var idx = start;
    var remaining = target_character;
    while (idx < text.len and remaining > 0) : (idx += 1) {
        const c = text[idx];
        if (c == '\n') break;
        if (c == '\r') {
            if (idx + 1 < text.len and text[idx + 1] == '\n') idx += 1;
            break;
        }
        remaining -= 1;
    }

    return idx;
}
