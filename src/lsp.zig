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

const TextEdit = struct {
    range: LspRange,
    newText: []const u8,
};

const emptyTextEdits: []const TextEdit = &[_]TextEdit{};

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

        const cl = parseContentLength(hdr.buf[0..hdr.body_start]) catch |err| {
            std.debug.print("[lsp] error parsing content length: {s}\nHeaders received:\n---\n{s}\n---\n", .{ @errorName(err), hdr.buf[0..hdr.body_start] });
            continue;
        };
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
        } else if (std.mem.eql(u8, req.method, "textDocument/definition")) {
            if (req.params) |p| try onGoToDefinition(Out, gpa, &docs, req.id orelse 0, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/hover")) {
            if (req.params) |p| try onHover(Out, gpa, &docs, req.id orelse 0, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/rename")) {
            if (req.params) |p| try onRename(Out, gpa, &docs, req.id orelse 0, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/completion")) {
            if (req.params) |p| try onCompletion(Out, gpa, &docs, req.id orelse 0, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/semanticTokens/full")) {
            if (req.params) |p| try onSemanticTokensFull(Out, gpa, &docs, req.id orelse 0, p);
        } else if (std.mem.eql(u8, req.method, "textDocument/formatting")) {
            if (req.params) |p| try onFormatting(Out, gpa, &docs, req.id orelse 0, p);
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
        definitionProvider: bool = true,
        renameProvider: bool = true,
        documentFormattingProvider: bool = true,
        completionProvider: struct { triggerCharacters: []const []const u8 } = .{ .triggerCharacters = &.{"."} },
        semanticTokensProvider: struct {
            legend: struct {
                tokenTypes: []const []const u8,
                tokenModifiers: []const []const u8,
            },
            full: bool = true,
            range: bool = true,
        } = .{
            .legend = .{
                .tokenTypes = semantic_token_types[0..],
                .tokenModifiers = semantic_token_modifiers[0..],
            },
            .range = true,
        },
        positionEncoding: []const u8 = "utf-8",
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

const Symbol = struct {
    decl_loc: ast.LocId,
    kind: SemanticTokenKind,
};

const Scope = struct {
    symbols: std.StringHashMap(Symbol),
    parent: ?*const Scope,
    gpa: std.mem.Allocator,

    fn init(gpa: std.mem.Allocator, parent: ?*const Scope) Scope {
        return .{
            .symbols = std.StringHashMap(Symbol).init(gpa),
            .parent = parent,
            .gpa = gpa,
        };
    }

    fn deinit(self: *Scope) void {
        self.symbols.deinit();
    }

    fn declare(self: *Scope, name: []const u8, loc: ast.LocId, kind: SemanticTokenKind) !void {
        try self.symbols.put(name, .{ .decl_loc = loc, .kind = kind });
    }

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

const SymbolResolver = struct {
    gpa: std.mem.Allocator,
    ast_unit: *ast.Ast,
    resolution_map: *std.AutoArrayHashMap(u32, Symbol),

    pub fn run(gpa: std.mem.Allocator, ast_unit: *ast.Ast, resolution_map: *std.AutoArrayHashMap(u32, Symbol)) !void {
        var self = SymbolResolver{
            .gpa = gpa,
            .ast_unit = ast_unit,
            .resolution_map = resolution_map,
        };

        var global_scope = Scope.init(gpa, null);
        defer global_scope.deinit();

        try self.walkUnit(&global_scope);
    }

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

    fn walkDecl(self: *SymbolResolver, scope: *Scope, decl_id: ast.DeclId) !void {
        const decl_row = self.ast_unit.exprs.Decl.get(decl_id);
        const decl_kind = classifyDeclKind(self.ast_unit, decl_row.value);
        if (!decl_row.pattern.isNone()) {
            try self.walkPattern(scope, patternFromOpt(decl_row.pattern), decl_kind);
        }
    }

    fn walkStmt(self: *SymbolResolver, scope: *Scope, stmt_id: ast.StmtId) anyerror!void {
        const stmt_store = &self.ast_unit.stmts;
        const stmt_kind = stmt_store.index.kinds.items[stmt_id.toRaw()];
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

    fn walkExpr(self: *SymbolResolver, scope: *const Scope, expr_id: ast.ExprId) !void {
        const expr_store = &self.ast_unit.exprs;
        const expr_kind = expr_store.index.kinds.items[expr_id.toRaw()];

        switch (expr_kind) {
            .Ident => {
                const row = expr_store.get(.Ident, expr_id);
                if (scope.lookup(expr_store.strs.get(row.name))) |symbol| {
                    try self.resolution_map.put(expr_id.toRaw(), symbol);
                }
            },
            .Block => {
                const row = expr_store.get(.Block, expr_id);
                var block_scope = Scope.init(self.gpa, scope);
                defer block_scope.deinit();
                const stmts = self.ast_unit.stmts.stmt_pool.slice(row.items);
                for (stmts) |stmt_id| {
                    try self.walkStmt(&block_scope, stmt_id);
                }
            },
            .FunctionLit => {
                const row = expr_store.get(.FunctionLit, expr_id);
                var fn_scope = Scope.init(self.gpa, scope);
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
                var fn_scope = Scope.init(self.gpa, scope);
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
                var for_scope = Scope.init(self.gpa, scope);
                defer for_scope.deinit();
                try self.walkPattern(&for_scope, row.pattern, .variable);
                try self.walkExpr(scope, row.iterable);
                try self.walkExpr(&for_scope, row.body);
            },
            .While => {
                const row = expr_store.get(.While, expr_id);
                if (row.is_pattern and !row.pattern.isNone()) {
                    var while_scope = Scope.init(self.gpa, scope);
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
                    var arm_scope = Scope.init(self.gpa, scope);
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
                var handler_scope = Scope.init(self.gpa, scope);
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

    fn walkPattern(self: *SymbolResolver, scope: *Scope, pat_id: ast.PatternId, kind: SemanticTokenKind) !void {
        const pat_store = &self.ast_unit.pats;
        const pat_kind = pat_store.index.kinds.items[pat_id.toRaw()];
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

fn onGoToDefinition(out: *std.io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, id: u64, params: json.Value) !void {
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

    var context = lib.compile.Context.init(gpa);
    defer context.deinit();

    const path = try fileUriToPath(gpa, uri);
    defer gpa.free(path);

    const offset = positionToOffset(text, p.value.position.line, p.value.position.character);
    const file_id = try context.source_manager.setVirtualSourceByPath(path, text);
    var pipeline = lib.pipeline.Pipeline.init(gpa, &context);

    _ = pipeline.run(path, &.{}, .check, null) catch |err| switch (err) {
        error.ParseFailed => {
            try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
            return;
        },
        else => {
            // Proceed with partial results (AST) if available
        },
    };

    const ast_unit = findAstForFile(&context.compilation_unit, file_id) orelse {
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
        return;
    };

    var resolution_map = std.AutoArrayHashMap(u32, Symbol).init(gpa);
    defer resolution_map.deinit();
    try SymbolResolver.run(gpa, ast_unit, &resolution_map);

    const expr_id = findExprAt(ast_unit, offset) orelse {
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
        return;
    };

    var result: ?struct { uri: []const u8, range: LspRange } = null;

    if (resolution_map.get(expr_id.toRaw())) |symbol| {
        const decl_loc = ast_unit.exprs.locs.get(symbol.decl_loc);
        const decl_file_id = decl_loc.file_id;

        const decl_path = context.source_manager.get(decl_file_id) orelse {
            try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
            return;
        };
        const decl_text = context.source_manager.read(decl_file_id) catch {
            try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
            return;
        };
        defer gpa.free(decl_text);

        const decl_uri = try pathToUri(gpa, decl_path);
        defer gpa.free(decl_uri);

        const range = locToRange(decl_text, decl_loc);

        const result_uri = try gpa.dupe(u8, decl_uri);
        result = .{ .uri = result_uri, .range = range };
    } else if (ast_unit.type_info.getMethodBinding(expr_id)) |binding| blk: {
        const decl_ast = binding.decl_ast;
        const decl_row = decl_ast.exprs.Decl.get(binding.decl_id);
        const decl_loc = decl_ast.exprs.locs.get(decl_row.loc);
        const decl_file_id = decl_loc.file_id;

        const decl_path = context.source_manager.get(decl_file_id) orelse break :blk;
        const decl_text = context.source_manager.read(decl_file_id) catch break :blk;
        defer gpa.free(decl_text);

        const decl_uri = try pathToUri(gpa, decl_path);
        defer gpa.free(decl_uri);

        const range = locToRange(decl_text, decl_loc);

        const result_uri = try gpa.dupe(u8, decl_uri);
        result = .{ .uri = result_uri, .range = range };
    }

    if (result) |r| {
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = r });
        gpa.free(r.uri);
    } else {
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
    }
}

fn onRename(out: *std.io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, id: u64, params: json.Value) !void {
    const P = struct {
        textDocument: struct { uri: []const u8 },
        position: struct { line: u32, character: u32 },
        newName: []const u8,
    };
    var p = try json.parseFromValue(P, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();

    const uri = p.value.textDocument.uri;
    const text = docs.get(uri) orelse {
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
        return;
    };

    var context = lib.compile.Context.init(gpa);
    defer context.deinit();

    const path = try fileUriToPath(gpa, uri);
    defer gpa.free(path);

    const offset = positionToOffset(text, p.value.position.line, p.value.position.character);
    const file_id = try context.source_manager.setVirtualSourceByPath(path, text);
    var pipeline = lib.pipeline.Pipeline.init(gpa, &context);

    _ = pipeline.run(path, &.{}, .check, null) catch |err| switch (err) {
        error.ParseFailed => {
            try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
            return;
        },
        else => {
            // Proceed with partial results if AST is present
        },
    };

    const ast_unit = findAstForFile(&context.compilation_unit, file_id) orelse {
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
        return;
    };

    var resolution_map = std.AutoArrayHashMap(u32, Symbol).init(gpa);
    defer resolution_map.deinit();
    try SymbolResolver.run(gpa, ast_unit, &resolution_map);

    const expr_id = findExprAt(ast_unit, offset) orelse {
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
        return;
    };

    const symbol = resolution_map.get(expr_id.toRaw()) orelse {
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
        return;
    };

    var references = std.ArrayList(Loc){};
    defer references.deinit(gpa);

    try references.append(gpa, ast_unit.exprs.locs.get(symbol.decl_loc));

    var it = resolution_map.iterator();
    while (it.next()) |entry| {
        if (entry.value_ptr.decl_loc.toRaw() == symbol.decl_loc.toRaw()) {
            const ref_expr_id = ast.ExprId.fromRaw(entry.key_ptr.*);
            const ref_loc = exprLoc(ast_unit, ref_expr_id);
            try references.append(gpa, ref_loc);
        }
    }

    const WorkspaceEdit = struct {
        changes: std.StringHashMap([]const TextEdit),

        pub fn jsonStringify(self: @This(), s: *json.Stringify) !void {
            try s.beginObject();
            try s.objectField("changes");
            try s.beginObject();
            var changes_it = self.changes.iterator();
            while (changes_it.next()) |entry| {
                try s.objectField(entry.key_ptr.*);
                try s.write(entry.value_ptr.*);
            }
            try s.endObject();
            try s.endObject();
        }
    };

    var edits = std.ArrayList(TextEdit){};
    defer edits.deinit(gpa);

    for (references.items) |loc| {
        const range = locToRange(text, loc);
        try edits.append(gpa, .{ .range = range, .newText = p.value.newName });
    }

    var changes = std.StringHashMap([]const TextEdit).init(gpa);
    defer {
        if (changes.get(uri)) |owned_slice| {
            gpa.free(owned_slice);
        }
        changes.deinit();
    }

    try changes.put(uri, try edits.toOwnedSlice(gpa));

    const workspace_edit = WorkspaceEdit{ .changes = changes };

    try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = workspace_edit });
}

fn pathToUri(gpa: std.mem.Allocator, path: []const u8) ![]u8 {
    return std.fmt.allocPrint(gpa, "file://{s}", .{path});
}

const CompletionItem = struct {
    label: []const u8,
    kind: ?u32 = null,
    detail: ?[]const u8 = null,
};

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

fn onCompletion(out: *std.Io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, id: u64, params: json.Value) !void {
    const P = struct {
        textDocument: struct { uri: []const u8 },
        position: LspPosition,
    };
    var p = try json.parseFromValue(P, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();

    const uri = p.value.textDocument.uri;
    const text = docs.get(uri) orelse {
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = null });
        return;
    };

    var items = std.ArrayList(CompletionItem){};
    defer {
        for (items.items) |item| {
            gpa.free(item.label);
            if (item.detail) |d| gpa.free(d);
        }
        items.deinit(gpa);
    }

    computeCompletions(gpa, uri, text, &items) catch |err| {
        std.debug.print("[lsp] completion error: {s}\n", .{@errorName(err)});
        const empty_items: ?[]const CompletionItem = null;
        try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = .{ .items = empty_items } });
        return;
    };

    try writeJson(out, gpa, .{ .jsonrpc = "2.0", .id = id, .result = .{ .items = items.items } });
}

fn computeCompletions(gpa: std.mem.Allocator, uri: []const u8, text: []const u8, items: *std.ArrayList(CompletionItem)) !void {
    // Add keywords
    const keywords = [_][]const u8{ "fn", "struct", "enum", "let", "const", "if", "else", "for", "while", "match", "return", "true", "false", "import", "package", "defer", "errdefer", "async", "await", "try", "catch" };
    for (keywords) |kw| {
        try items.append(gpa, .{ .label = try gpa.dupe(u8, kw), .kind = @intFromEnum(CompletionItemKind.Keyword) });
    }

    var context = lib.compile.Context.init(gpa);
    defer context.deinit();

    const path = try fileUriToPath(gpa, uri);
    defer gpa.free(path);

    const file_id = try context.source_manager.setVirtualSourceByPath(path, text);
    var pipeline = lib.pipeline.Pipeline.init(gpa, &context);

    _ = pipeline.run(path, &.{}, .parse, null) catch |err| switch (err) {
        error.ParseFailed, error.TooManyErrors => {},
        else => |e| return e,
    };

    const ast_unit = findAstForFile(&context.compilation_unit, file_id) orelse return;

    // Add global declarations
    const decls = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);
    for (decls) |decl_id| {
        const decl_row = ast_unit.exprs.Decl.get(decl_id);
        const decl_kind = classifyDeclKind(ast_unit, decl_row.value);
        if (decl_row.pattern.isNone()) continue;
        try addPatternBindingsToCompletions(gpa, items, ast_unit, patternFromOpt(decl_row.pattern), decl_kind);
    }
}

fn addPatternBindingsToCompletions(gpa: std.mem.Allocator, items: *std.ArrayList(CompletionItem), ast_unit: *ast.Ast, pat_id: ast.PatternId, kind: SemanticTokenKind) !void {
    const pat_store = &ast_unit.pats;
    const pat_kind = pat_store.index.kinds.items[pat_id.toRaw()];
    switch (pat_kind) {
        .Binding => {
            const row = pat_store.get(.Binding, pat_id);
            const name = ast_unit.pats.strs.get(row.name);
            try items.append(gpa, .{
                .label = try gpa.dupe(u8, name),
                .kind = @intFromEnum(lspCompletionKindFromSemantic(kind)),
            });
        },
        .Tuple => {
            const row = pat_store.get(.Tuple, pat_id);
            for (pat_store.pat_pool.slice(row.elems)) |elem| try addPatternBindingsToCompletions(gpa, items, ast_unit, elem, kind);
        },
        .Slice => {
            const row = pat_store.get(.Slice, pat_id);
            for (pat_store.pat_pool.slice(row.elems)) |elem| try addPatternBindingsToCompletions(gpa, items, ast_unit, elem, kind);
            if (!row.rest_binding.isNone()) {
                try addPatternBindingsToCompletions(gpa, items, ast_unit, patternFromOpt(row.rest_binding), kind);
            }
        },
        .Struct => {
            const row = pat_store.get(.Struct, pat_id);
            for (pat_store.field_pool.slice(row.fields)) |field_id| {
                const field = pat_store.StructField.get(field_id);
                try addPatternBindingsToCompletions(gpa, items, ast_unit, field.pattern, kind);
            }
        },
        .VariantStruct => {
            const row = pat_store.get(.VariantStruct, pat_id);
            for (pat_store.field_pool.slice(row.fields)) |field_id| {
                const field = pat_store.StructField.get(field_id);
                try addPatternBindingsToCompletions(gpa, items, ast_unit, field.pattern, kind);
            }
        },
        .VariantTuple => {
            const row = pat_store.get(.VariantTuple, pat_id);
            for (pat_store.pat_pool.slice(row.elems)) |elem| try addPatternBindingsToCompletions(gpa, items, ast_unit, elem, kind);
        },
        .Or => {
            const row = pat_store.get(.Or, pat_id);
            for (pat_store.pat_pool.slice(row.alts)) |alt| try addPatternBindingsToCompletions(gpa, items, ast_unit, alt, kind);
        },
        .At => {
            const row = pat_store.get(.At, pat_id);
            const name = ast_unit.pats.strs.get(row.binder);
            try items.append(gpa, .{
                .label = try gpa.dupe(u8, name),
                .kind = @intFromEnum(lspCompletionKindFromSemantic(kind)),
            });
            try addPatternBindingsToCompletions(gpa, items, ast_unit, row.pattern, kind);
        },
        else => {},
    }
}

fn onSemanticTokensFull(out: *std.Io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, id: u64, params: json.Value) !void {
    const P = struct {
        textDocument: struct { uri: []const u8 },
    };
    var p = try json.parseFromValue(P, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();

    const uri = p.value.textDocument.uri;
    const Resp = struct {
        jsonrpc: []const u8 = "2.0",
        id: u64,
        result: struct { data: []const u32 },
    };

    if (docs.get(uri)) |text| {
        const data = try computeSemanticTokens(gpa, uri, text);
        defer gpa.free(data);
        try writeJson(out, gpa, Resp{ .id = id, .result = .{ .data = data } });
    } else {
        const empty = [_]u32{};
        try writeJson(out, gpa, Resp{ .id = id, .result = .{ .data = &empty } });
    }
}

fn onFormatting(out: *std.Io.Writer, gpa: std.mem.Allocator, docs: *DocumentStore, id: u64, params: json.Value) !void {
    const P = struct {
        textDocument: struct { uri: []const u8 },
    };
    var p = try json.parseFromValue(P, gpa, params, .{ .ignore_unknown_fields = true });
    defer p.deinit();

    const uri = p.value.textDocument.uri;

    const source = docs.get(uri) orelse {
        const Resp = struct {
            jsonrpc: []const u8 = "2.0",
            id: u64,
            result: []const TextEdit,
        };
        try writeJson(out, gpa, Resp{ .id = id, .result = emptyTextEdits });
        return;
    };

    const path = try fileUriToPath(gpa, uri);
    defer gpa.free(path);

    const source_z = try std.mem.concatWithSentinel(gpa, u8, &.{source}, 0);
    defer gpa.free(source_z);

    const formatted = lib.formatter.formatSource(gpa, source_z, path) catch |err| {
        std.debug.print("[lsp] formatter failed: {s}\n", .{@errorName(err)});
        const Resp = struct {
            jsonrpc: []const u8 = "2.0",
            id: u64,
            result: []const TextEdit,
        };
        try writeJson(out, gpa, Resp{ .id = id, .result = emptyTextEdits });
        return;
    };
    defer gpa.free(formatted);

    const edit = TextEdit{
        .range = fullRange(source),
        .newText = formatted,
    };
    const edits = [_]TextEdit{edit};
    const Resp = struct {
        jsonrpc: []const u8 = "2.0",
        id: u64,
        result: []const TextEdit,
    };
    try writeJson(out, gpa, Resp{ .id = id, .result = edits[0..] });

    try docs.set(uri, formatted);
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

    _ = pipeline.run(path, &.{}, .check, null) catch |err| switch (err) {
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

const TokenKey = struct {
    start: usize,
    end: usize,
};

const TokenEntry = struct {
    start: usize,
    end: usize,
    kind: SemanticTokenKind,
};

const TokenAccumulator = struct {
    map: std.AutoArrayHashMap(TokenKey, SemanticTokenKind),
    gpa: std.mem.Allocator,

    fn init(gpa: std.mem.Allocator) TokenAccumulator {
        return .{ .map = std.AutoArrayHashMap(TokenKey, SemanticTokenKind).init(gpa), .gpa = gpa };
    }

    fn deinit(self: *TokenAccumulator) void {
        self.map.deinit();
    }

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
            fn lessThan(_: void, a: TokenEntry, b: TokenEntry) bool {
                if (a.start == b.start) return a.end < b.end;
                return a.start < b.start;
            }
        }.lessThan);

        return out;
    }

    fn toEncodedSlice(self: *TokenAccumulator, text: []const u8) ![]u32 {
        const entries = try self.toSortedEntries();
        defer self.gpa.free(entries);

        var data = std.ArrayList(u32){};
        errdefer data.deinit(self.gpa);

        var have_prev = false;
        var last_line: u32 = 0;
        var last_char: u32 = 0;

        for (entries) |entry| {
            const pos = offsetToPosition(text, entry.start);
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

fn kindPriority(kind: SemanticTokenKind) u8 {
    return switch (kind) {
        .function, .type, .namespace, .variable, .property, .parameter, .enum_member => 2,
        else => 1,
    };
}

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

fn computeSemanticTokens(gpa: std.mem.Allocator, uri: []const u8, text: []const u8) ![]u32 {
    if (text.len == 0) {
        return &[_]u32{};
    }

    const path = try fileUriToPath(gpa, uri);
    defer gpa.free(path);

    var tokens = TokenAccumulator.init(gpa);
    defer tokens.deinit();

    try collectLexicalTokens(&tokens, gpa, text);
    try collectAstSemanticTokens(&tokens, gpa, text, path);

    return try tokens.toEncodedSlice(text);
}

fn collectLexicalTokens(tokens: *TokenAccumulator, gpa: std.mem.Allocator, text: []const u8) !void {
    if (text.len == 0) return;

    const text_z = try gpa.dupeZ(u8, text);
    defer gpa.free(text_z);

    var tokenizer = lib.lexer.Tokenizer.init(text_z, 0, .normal);
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

fn collectAstSemanticTokens(tokens: *TokenAccumulator, gpa: std.mem.Allocator, text: []const u8, path: []const u8) !void {
    var context = lib.compile.Context.init(gpa);
    defer context.deinit();

    const file_id = try context.source_manager.setVirtualSourceByPath(path, text);
    var pipeline = lib.pipeline.Pipeline.init(gpa, &context);

    _ = pipeline.run(path, &.{}, .check, null) catch |err| switch (err) {
        error.ParseFailed,
        error.TypeCheckFailed,
        error.LoweringFailed,
        error.TirLoweringFailed,
        error.TooManyErrors,
        => {},
        else => {
            std.debug.print("[lsp] semantic token pipeline error: {s}\n", .{@errorName(err)});
            return;
        },
    };

    const ast_unit = findAstForFile(&context.compilation_unit, file_id) orelse return;

    var resolution_map = std.AutoArrayHashMap(u32, Symbol).init(gpa);
    defer resolution_map.deinit();
    try SymbolResolver.run(gpa, ast_unit, &resolution_map);

    try gatherAstTokens(tokens, gpa, text, ast_unit, file_id, &resolution_map);
}

fn gatherAstTokens(tokens: *TokenAccumulator, gpa: std.mem.Allocator, text: []const u8, ast_unit: *ast.Ast, file_id: u32, resolution_map: *const std.AutoArrayHashMap(u32, Symbol)) !void {
    try highlightPackage(tokens, text, ast_unit, file_id);
    try highlightDecls(tokens, text, ast_unit, file_id);
    try highlightExpressions(tokens, gpa, text, ast_unit, file_id, resolution_map);
}

fn highlightPackage(tokens: *TokenAccumulator, text: []const u8, ast_unit: *ast.Ast, file_id: u32) !void {
    if (ast_unit.unit.package_loc.isNone()) return;
    const loc_idx = ast_unit.unit.package_loc.unwrap();
    const loc_id = ast.LocId.fromRaw(loc_idx.toRaw());
    try highlightLoc(tokens, text, ast_unit.exprs.locs, loc_id, file_id, .namespace);
}

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

fn collectPatternBindingNames(gpa: std.mem.Allocator, names: *std.StringHashMap(void), ast_unit: *ast.Ast, pat_id: ast.PatternId) !void {
    const pat_store = &ast_unit.pats;
    const pat_kind = pat_store.index.kinds.items[pat_id.toRaw()];
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

fn collectAllParamNames(gpa: std.mem.Allocator, names: *std.StringHashMap(void), ast_unit: *ast.Ast) !void {
    const expr_store = &ast_unit.exprs;
    const kinds = expr_store.index.kinds.items;
    var idx: usize = 0;
    while (idx < kinds.len) : (idx += 1) {
        const expr_kind = kinds[idx];
        const expr_id = ast.ExprId.fromRaw(@intCast(idx));
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

fn highlightTypeExpr(tokens: *TokenAccumulator, text: []const u8, ast_unit: *ast.Ast, file_id: u32, expr_id: ast.ExprId) !void {
    const expr_store = &ast_unit.exprs;
    const expr_kind = expr_store.index.kinds.items[expr_id.toRaw()];
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

fn highlightExpressions(tokens: *TokenAccumulator, gpa: std.mem.Allocator, text: []const u8, ast_unit: *ast.Ast, file_id: u32, resolution_map: *const std.AutoArrayHashMap(u32, Symbol)) !void {
    _ = gpa;
    const expr_store = &ast_unit.exprs;
    const kinds = expr_store.index.kinds.items;
    const expr_types = ast_unit.type_info.expr_types.items;
    const type_store = ast_unit.type_info.store;

    var idx: usize = 0;
    expr_loop: while (idx < kinds.len) : (idx += 1) {
        const expr_kind = kinds[idx];
        const expr_id = ast.ExprId.fromRaw(@intCast(idx));
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
                if (!fn_row.result_ty.isNone()) {
                    try highlightTypeExpr(tokens, text, ast_unit, file_id, fn_row.result_ty.unwrap());
                }
                const params = expr_store.param_pool.slice(fn_row.params);
                for (params) |param_id| {
                    const param = expr_store.Param.get(param_id);
                    if (!param.ty.isNone()) {
                        try highlightTypeExpr(tokens, text, ast_unit, file_id, param.ty.unwrap());
                    }
                    if (!param.pat.isNone()) {
                        const pat_id = patternFromOpt(param.pat);
                        try highlightPattern(tokens, text, ast_unit, pat_id, .parameter, file_id);
                    }
                }
            },
            .Closure => {
                const cl_row = expr_store.get(.Closure, expr_id);
                if (!cl_row.result_ty.isNone()) {
                    try highlightTypeExpr(tokens, text, ast_unit, file_id, cl_row.result_ty.unwrap());
                }
                const params = expr_store.param_pool.slice(cl_row.params);
                for (params) |param_id| {
                    const param = expr_store.Param.get(param_id);
                    if (!param.ty.isNone()) {
                        try highlightTypeExpr(tokens, text, ast_unit, file_id, param.ty.unwrap());
                    }
                    if (!param.pat.isNone()) {
                        const pat_id = patternFromOpt(param.pat);
                        try highlightPattern(tokens, text, ast_unit, pat_id, .parameter, file_id);
                    }
                }
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

fn classifyDeclKind(ast_unit: *ast.Ast, value_expr: ast.ExprId) SemanticTokenKind {
    const expr_store = &ast_unit.exprs;
    const expr_kind = expr_store.index.kinds.items[value_expr.toRaw()];
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
    const pat_kind = pat_store.index.kinds.items[pat_id.toRaw()];
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

fn patternFromOpt(opt: ast.OptPatternId) ast.PatternId {
    std.debug.assert(!opt.isNone());
    const idx = opt.unwrap();
    return ast.PatternId.fromRaw(idx.toRaw());
}

fn highlightPatternPath(tokens: *TokenAccumulator, text: []const u8, ast_unit: *ast.Ast, path: ast.RangePathSeg, file_id: u32) !void {
    const pat_store = &ast_unit.pats;
    const segs = pat_store.seg_pool.slice(path);
    for (segs) |seg_id| {
        const seg = pat_store.PathSeg.get(seg_id);
        try highlightLoc(tokens, text, ast_unit.exprs.locs, seg.loc, file_id, .type);
    }
}

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

fn isKeywordTag(tag: lib.lexer.Token.Tag) bool {
    return @intFromEnum(tag) >= @intFromEnum(lib.lexer.Token.Tag.keyword_align);
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

fn fullRange(text: []const u8) LspRange {
    return .{
        .start = .{ .line = 0, .character = 0 },
        .end = offsetToPosition(text, text.len),
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

fn resolvePointer(type_store: *types.TypeStore, type_id: types.TypeId) types.TypeId {
    var current_id = type_id;
    while (type_store.getKind(current_id) == .Ptr) {
        const ptr_row = type_store.get(.Ptr, current_id);
        current_id = ptr_row.elem;
    }
    return current_id;
}

fn printHoverFields(writer: *std.io.Writer, type_store: *types.TypeStore, fields_range: types.RangeField) !void {
    const fields = type_store.field_pool.slice(fields_range);
    if (fields.len > 0) {
        try writer.print("\n\n---\n", .{});
        for (fields) |field_id| {
            const field_row = type_store.Field.get(field_id);
            const field_name = type_store.strs.get(field_row.name);
            try writer.print("{s}: ", .{field_name});
            try type_store.fmt(field_row.ty, writer);
            try writer.print("\n", .{});
        }
    }
}

fn computeHover(gpa: std.mem.Allocator, uri: []const u8, text: []const u8, offset_in: usize) !?HoverInfo {
    var context = lib.compile.Context.init(gpa);
    defer context.deinit();

    const path = try fileUriToPath(gpa, uri);
    defer gpa.free(path);

    const offset = if (offset_in > text.len) text.len else offset_in;
    const file_id = try context.source_manager.setVirtualSourceByPath(path, text);
    var pipeline = lib.pipeline.Pipeline.init(gpa, &context);

    _ = pipeline.run(path, &.{}, .check, null) catch |err| switch (err) {
        error.ParseFailed => return null,
        else => {
            // Proceed with partial AST-based hover if available
        },
    };

    const ast_unit = findAstForFile(&context.compilation_unit, file_id) orelse return null;

    var resolution_map = std.AutoArrayHashMap(u32, Symbol).init(gpa);
    defer resolution_map.deinit();
    try SymbolResolver.run(gpa, ast_unit, &resolution_map);

    const expr_id = findExprAt(ast_unit, offset) orelse return null;
    const loc = exprLoc(ast_unit, expr_id);

    var msg_builder = std.Io.Writer.Allocating.init(gpa);
    defer msg_builder.deinit();
    const writer = &msg_builder.writer;

    if (resolution_map.get(expr_id.toRaw())) |symbol| {
        const decl_loc = ast_unit.exprs.locs.get(symbol.decl_loc);
        const decl_file_id = decl_loc.file_id;

        const decl_text = context.source_manager.read(decl_file_id) catch return null;
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
            try context.type_store.fmt(type_id, writer);
            try writer.print("\n```", .{});
        }

        const message = try msg_builder.toOwnedSlice();
        return HoverInfo{
            .message = message,
            .range = locToRange(text, loc),
        };
    }

    // Fallback for unresolved symbols
    if (getExprType(ast_unit, expr_id)) |type_id| {
        try writer.print("```sr\n", .{});
        try context.type_store.fmt(type_id, writer);
        try writer.print("\n```", .{});
        const message = try msg_builder.toOwnedSlice();
        return HoverInfo{
            .message = message,
            .range = locToRange(text, loc),
        };
    }

    return null;
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
