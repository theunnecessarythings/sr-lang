const std = @import("std");
const cst = @import("cst.zig");
const Parser = @import("parser.zig").Parser;
const compile = @import("compile.zig");
const diag = @import("diagnostics.zig");
const Loc = @import("lexer.zig").Token.Loc;

/// Format a single source buffer and return the formatted text.
pub fn formatSource(gpa: std.mem.Allocator, source: [:0]const u8, file_path: []const u8) ![]u8 {
    var ctx: compile.Context = .init(gpa);
    defer ctx.deinit();
    ctx.load_imports = false;

    const file_id = try ctx.source_manager.setVirtualSourceByPath(file_path, source);
    defer ctx.source_manager.clearVirtualSource(file_id);

    var diagnostics: diag.Diagnostics = .init(gpa, ctx.type_store, ctx.interner);
    defer diagnostics.deinit();

    var parser: Parser = .init(gpa, source, file_id, &diagnostics, &ctx);
    var tree = try parser.parse();
    defer tree.deinit();

    if (diagnostics.messages.items.len != 0) {
        return error.ParseFailed;
    }

    var fmt = Formatter{
        .gpa = gpa,
        .source = source,
        .exprs = &tree.exprs,
        .pats = &tree.pats,
        .program = tree.program,
        .comments = tree.comments.slice(),
        .locs = tree.exprs.locs,
    };
    return try fmt.format();
}

const spaces = " " ** 256;

/// Tracks formatter-specific state while printing a CST program.
const Formatter = struct {
    /// Allocator used to build intermediate buffers.
    gpa: std.mem.Allocator,
    /// Original source text that is being formatted.
    source: []const u8,
    /// The parser's expression store for lookup during formatting.
    exprs: *cst.ExprStore,
    /// Pattern store consulted when formatting match expressions.
    pats: *cst.PatternStore,
    /// CST representation of the program being formatted.
    program: cst.ProgramDO,
    /// Comments extracted from the parser to preserve placement.
    comments: []const cst.Comment,
    /// Location table used to resolve node positions.
    locs: *cst.LocStore,

    /// Builder that accumulates the emitted bytes.
    builder: std.ArrayList(u8) = .{},
    /// Current indentation level (in spaces).
    indent: usize = 0,
    /// Whether the next printed byte needs indentation padding.
    needs_indent: bool = true,
    /// Index of the next comment that should be emitted.
    comment_idx: usize = 0,

    /// Tracks the end index of the last printed token/node.
    last_written_loc: usize = 0,

    /// Generate formatted source text for the current program/builder.
    fn format(self: *Formatter) ![]u8 {
        self.builder = .{};
        self.last_written_loc = 0;
        self.comment_idx = 0;
        try self.builder.ensureTotalCapacity(self.gpa, self.source.len + 1);
        errdefer self.builder.deinit(self.gpa);

        try self.printProgram();
        try self.flushComments(self.source.len);

        if (self.builder.items.len == 0 or self.builder.items[self.builder.items.len - 1] != '\n') {
            try self.builder.append(self.gpa, '\n');
        }
        return self.builder.toOwnedSlice(self.gpa);
    }

    // ------------------------------------------------------------
    // Basics & Comment Logic
    // ------------------------------------------------------------
    /// Ensure indentation spaces are emitted before the next token.
    fn ws(self: *Formatter) !void {
        if (!self.needs_indent) return;
        var remaining = self.indent;
        while (remaining > 0) {
            const chunk = @min(remaining, spaces.len);
            try self.builder.appendSlice(self.gpa, spaces[0..chunk]);
            remaining -= chunk;
        }
        self.needs_indent = false;
    }

    /// Append a newline and reset indentation tracking.
    fn newline(self: *Formatter) !void {
        try self.builder.append(self.gpa, '\n');
        self.needs_indent = true;
    }

    /// Return true if the last emitted character is a newline.
    inline fn lastCharIsNewline(self: *Formatter) bool {
        return self.builder.items.len > 0 and self.builder.items[self.builder.items.len - 1] == '\n';
    }

    /// Return true when the builder ends with two consecutive newlines.
    fn endsWithDoubleNewline(self: *Formatter) bool {
        const len = self.builder.items.len;
        return len >= 2 and
            self.builder.items[len - 1] == '\n' and
            self.builder.items[len - 2] == '\n';
    }

    /// Append a literal slice after obeying the current indentation.
    fn printLiteral(self: *Formatter, text: []const u8) !void {
        try self.ws();
        try self.builder.appendSlice(self.gpa, text);
    }

    /// Resolve interned string `id` into its byte slice.
    inline fn s(self: *const Formatter, id: cst.StrId) []const u8 {
        return self.exprs.strs.get(id);
    }

    /// Return the source offset where `loc` begins.
    inline fn locStart(self: *const Formatter, loc: cst.LocId) usize {
        return self.locs.get(loc).start;
    }

    /// Return the source offset immediately after `loc`.
    inline fn locEnd(self: *const Formatter, loc: cst.LocId) usize {
        return self.locs.get(loc).end;
    }

    /// Emit comments that precede byte position `pos`.
    fn emitCommentsBefore(self: *Formatter, pos: usize) !void {
        try self.flushComments(pos);
    }

    /// Return true if the comment at `comment_start` starts on a fresh line.
    fn isLineComment(self: *Formatter, comment_start: usize) bool {
        var i: usize = comment_start;
        while (i > 0) {
            i -= 1;
            const c = self.source[i];
            if (c == '\n') return true;
            if (c != ' ' and c != '\t' and c != '\r') return false; // Found code -> Trailing
        }
        return true; // Start of file
    }

    /// Flush recorded comments up to `limit`, preserving spacing rules.
    fn flushComments(self: *Formatter, limit: usize) !void {
        while (self.comment_idx < self.comments.len) {
            const c = self.comments[self.comment_idx];
            const loc = self.locs.get(c.loc);

            if (loc.start >= limit) break;

            const is_line_comment = self.isLineComment(loc.start);
            const gap_has_blank = self.gapHasExtraBlank(self.last_written_loc, loc.start);

            if (is_line_comment) {
                if (self.builder.items.len > 0 and !self.lastCharIsNewline()) {
                    try self.newline();
                }
                if (gap_has_blank) {
                    if (!self.endsWithDoubleNewline()) {
                        try self.newline();
                    }
                }
                try self.ws();
            } else {
                // Trailing comment: Ensure exactly one space separator
                if (self.builder.items.len > 0) {
                    const last = self.builder.items[self.builder.items.len - 1];
                    if (last != ' ' and last != '\n') {
                        try self.builder.append(self.gpa, ' ');
                    }
                }
            }

            try self.printCommentBody(c, loc);

            switch (c.kind) {
                .line, .doc, .container_doc => try self.newline(),
                .block => {},
            }

            self.last_written_loc = loc.end;
            self.comment_idx += 1;
        }
    }

    /// Append the syntax for comment `c` (line/block/docs) to the builder.
    fn printCommentBody(self: *Formatter, c: cst.Comment, loc: Loc) !void {
        const text = self.source[loc.start..loc.end];
        switch (c.kind) {
            .line => {
                if (!std.mem.startsWith(u8, text, "//")) try self.builder.appendSlice(self.gpa, "//");
                try self.builder.appendSlice(self.gpa, text);
            },
            .doc => {
                if (!std.mem.startsWith(u8, text, "///")) try self.builder.appendSlice(self.gpa, "///");
                try self.builder.appendSlice(self.gpa, text);
            },
            .container_doc => {
                if (!std.mem.startsWith(u8, text, "//!")) try self.builder.appendSlice(self.gpa, "//!");
                try self.builder.appendSlice(self.gpa, text);
            },
            .block => try self.builder.appendSlice(self.gpa, text),
        }
    }

    /// Return whether `source[start..end]` contains at least two blank lines.
    fn gapHasExtraBlank(self: *Formatter, start: usize, end: usize) bool {
        if (start >= end or end > self.source.len) return false;
        var newlines: u32 = 0;
        for (self.source[start..end]) |b| {
            if (b == '\n') {
                newlines += 1;
                if (newlines >= 2) return true;
            }
        }
        return false;
    }

    // ------------------------------------------------------------
    // Program / Decl printing
    // ------------------------------------------------------------
    /// Emit top-level package/import/function declarations and associated comments.
    fn printProgram(self: *Formatter) !void {
        if (!self.program.package_name.isNone() and !self.program.package_loc.isNone()) {
            const pkg_loc_id = self.program.package_loc.unwrap();
            const pkg_loc = self.locs.get(pkg_loc_id);
            const text = self.source[pkg_loc.start..pkg_loc.end];

            if (std.mem.eql(u8, text, "package")) {
                try self.emitCommentsBefore(pkg_loc.start);
                try self.printLiteral("package ");
                try self.printLiteral(self.s(self.program.package_name.unwrap()));

                var line_end = pkg_loc.end;
                while (line_end < self.source.len and self.source[line_end] != '\n') : (line_end += 1) {}

                try self.flushComments(line_end);
                self.last_written_loc = line_end;

                try self.newline();
                try self.newline();
            }
        }

        const decl_ids = self.exprs.decl_pool.slice(self.program.top_decls);
        var prev_kind: u8 = 0; // 0: start, 1: import, 2: function, 3: other
        var prev_has_body = false;

        for (decl_ids, 0..) |did, i| {
            const row = self.exprs.Decl.get(did);
            const start_loc = self.locStart(row.loc);
            const rhs_kind = self.exprs.kind(row.rhs);
            const is_import = rhs_kind == .Import;
            const is_function = rhs_kind == .Function;
            const has_body = if (is_function)
                !self.exprs.get(.Function, row.rhs).body.isNone()
            else
                false;
            const kind: u8 = if (is_import) 1 else if (is_function) 2 else 3;

            var needs_blank = false;
            if (i > 0) {
                if (prev_kind == 1 and kind != 1) needs_blank = true;
                if (has_body and prev_has_body) needs_blank = true;
                if (self.gapHasExtraBlank(self.last_written_loc, start_loc)) needs_blank = true;
            }

            if (i > 0) {
                if (needs_blank) {
                    if (!self.lastCharIsNewline()) try self.newline();
                    if (!self.endsWithDoubleNewline()) try self.newline();
                } else {
                    if (!self.lastCharIsNewline()) try self.newline();
                }
            }

            try self.emitCommentsBefore(start_loc);
            try self.printDecl(did);

            var line_end = self.locEnd(row.loc);
            while (line_end < self.source.len and self.source[line_end] != '\n') : (line_end += 1) {}
            try self.flushComments(line_end);
            self.last_written_loc = line_end;

            prev_kind = kind;
            prev_has_body = has_body;
        }
        try self.newline();
    }

    /// Format declaration `id` with comments and spacing.
    fn printDecl(self: *Formatter, id: cst.DeclId) !void {
        const row = self.exprs.Decl.get(id);
        try self.emitCommentsBefore(self.locStart(row.loc));

        if (try self.tryPrintTestDecl(row)) return;

        if (!row.lhs.isNone()) {
            try self.printExpr(row.lhs.unwrap());
        }

        if (!row.ty.isNone()) {
            try self.printLiteral(": ");
            try self.printExpr(row.ty.unwrap());
            if (row.flags.is_const) {
                try self.printLiteral(" : ");
            } else {
                try self.printLiteral(" = ");
            }
            try self.printExpr(row.rhs);
            return;
        }

        if (!row.lhs.isNone()) {
            if (row.flags.is_const) {
                try self.printLiteral(" :: ");
            } else if (row.flags.is_assign) {
                try self.printLiteral(" = ");
            } else {
                try self.printLiteral(" := ");
            }
            try self.printExpr(row.rhs);
            return;
        }

        try self.printExpr(row.rhs);
    }

    fn tryPrintTestDecl(self: *Formatter, row: cst.Rows.Decl) !bool {
        if (row.lhs.isNone()) return false;
        if (!row.flags.is_const) return false;
        if (self.exprs.kind(row.rhs) != .Function) return false;

        const fn_node = self.exprs.get(.Function, row.rhs);
        if (!fn_node.flags.is_test) return false;
        if (fn_node.body.isNone()) return false;

        const test_name = self.testNameFromAttrs(fn_node.attrs) orelse return false;

        try self.printLiteral("test ");
        try self.printLiteral(test_name);
        try self.printLiteral(" ");
        try self.printExpr(fn_node.body.unwrap());
        return true;
    }

    fn testNameFromAttrs(self: *Formatter, attrs_opt: cst.OptRangeAttr) ?[]const u8 {
        if (attrs_opt.isNone()) return null;
        const attrs = self.exprs.attr_pool.slice(attrs_opt.asRange());
        for (attrs) |aid| {
            const attr = self.exprs.Attribute.get(aid);
            if (!std.mem.eql(u8, self.s(attr.name), "test")) continue;
            if (attr.value.isNone()) continue;
            const val_id = attr.value.unwrap();
            if (self.exprs.kind(val_id) != .Literal) continue;
            const lit = self.exprs.get(.Literal, val_id);
            return self.s(lit.value);
        }
        return null;
    }

    fn tryFormatIfInline(self: *Formatter, id: cst.ExprId) !bool {
        const node = self.exprs.get(.If, id);

        // Check then_block
        if (self.exprs.kind(node.then_block) != .Block) return false;
        const then_blk = self.exprs.get(.Block, node.then_block);
        const then_decls = self.exprs.decl_pool.slice(then_blk.items);
        if (then_decls.len != 1) return false;

        // Check else_block
        var else_decl: ?cst.DeclId = null;
        if (!node.else_block.isNone()) {
            const else_id = node.else_block.unwrap();
            if (self.exprs.kind(else_id) != .Block) return false;
            const else_blk = self.exprs.get(.Block, else_id);
            const else_decls = self.exprs.decl_pool.slice(else_blk.items);
            if (else_decls.len != 1) return false;
            else_decl = else_decls[0];
        }

        const snapshot = self.*;
        self.builder = .{};
        errdefer self.builder.deinit(self.gpa);

        try self.printLiteral("if ");
        try self.printExpr(node.cond);
        try self.printLiteral(" { ");
        try self.printDecl(then_decls[0]);
        try self.printLiteral(" }");

        if (else_decl) |ed| {
            try self.printLiteral(" else { ");
            try self.printDecl(ed);
            try self.printLiteral(" }");
        }

        const text = self.builder.items;
        if (std.mem.indexOfScalar(u8, text, '\n') != null) {
            self.builder.deinit(self.gpa);
            self.* = snapshot;
            return false;
        }

        var pre_len: usize = 0;
        if (snapshot.builder.items.len > 0) {
            var i = snapshot.builder.items.len;
            while (i > 0) {
                i -= 1;
                if (snapshot.builder.items[i] == '\n') break;
                pre_len += 1;
            }
        }

        if (pre_len + text.len > 100) {
            self.builder.deinit(self.gpa);
            self.* = snapshot;
            return false;
        }

        var new_state = self.*;
        new_state.builder = snapshot.builder;
        try new_state.builder.appendSlice(self.gpa, text);
        self.builder.deinit(self.gpa);
        self.* = new_state;
        return true;
    }

    /// Return the source location recorded for expression `eid`.
    inline fn exprLocFromId(exprs: *cst.ExprStore, eid: cst.ExprId, kind: cst.ExprKind) Loc {
        @setEvalBranchQuota(10000);
        return switch (kind) {
            inline else => |x| exprs.locs.get(exprs.get(x, eid).loc),
        };
    }

    fn trimAsciiSpace(str: []const u8) []const u8 {
        return std.mem.trim(u8, str, " \t\r\n");
    }

    fn mlirBodyIsMultiline(body: []const u8) bool {
        return std.mem.indexOfScalar(u8, body, '\n') != null;
    }

    fn printMlirBody(self: *Formatter, body_raw: []const u8) !void {
        const body_trimmed = trimAsciiSpace(body_raw);

        if (!mlirBodyIsMultiline(body_trimmed)) {
            try self.printLiteral(" { ");
            try self.printLiteral(body_trimmed);
            try self.printLiteral(" }");
            return;
        }

        try self.printLiteral(" {");
        try self.newline();

        self.indent += 4;
        defer self.indent -= 4;

        var it = std.mem.splitScalar(u8, body_trimmed, '\n');
        while (it.next()) |line_raw| {
            const line = std.mem.trimRight(u8, line_raw, " \t\r");
            if (line.len == 0) {
                try self.newline();
                continue;
            }
            try self.ws();
            const stripped = std.mem.trimLeft(u8, line, " \t");
            try self.printLiteral(stripped);
            try self.newline();
        }

        try self.ws();
        try self.printLiteral("}");
    }

    // ------------------------------------------------------------
    // Expressions
    // ------------------------------------------------------------
    /// Print expression `id` recursively with indentation and comments.
    pub fn printExpr(self: *Formatter, id: cst.ExprId) anyerror!void {
        const kind = self.exprs.kind(id);

        defer {
            @setEvalBranchQuota(100000);
            const loc = exprLocFromId(self.exprs, id, kind);
            if (loc.end > self.last_written_loc) {
                self.last_written_loc = loc.end;
            }
        }

        switch (kind) {
            .Block => {
                const node = self.exprs.get(.Block, id);
                const block_loc = self.exprs.locs.get(node.loc);

                try self.printLiteral("{");

                if (block_loc.start + 1 > self.last_written_loc) {
                    self.last_written_loc = block_loc.start + 1;
                }

                self.indent += 4;
                const decls = self.exprs.decl_pool.slice(node.items);

                for (decls) |did| {
                    const row = self.exprs.Decl.get(did);
                    const start = self.locStart(row.loc);

                    try self.emitCommentsBefore(start);

                    if (!self.lastCharIsNewline()) try self.newline();
                    if (self.gapHasExtraBlank(self.last_written_loc, start)) {
                        if (!self.endsWithDoubleNewline()) try self.newline();
                    }

                    try self.printDecl(did);

                    var line_end = self.locEnd(row.loc);
                    while (line_end < self.source.len and self.source[line_end] != '\n') : (line_end += 1) {}
                    try self.flushComments(line_end);
                    self.last_written_loc = line_end;
                }

                try self.emitCommentsBefore(block_loc.end);

                self.indent -= 4;
                if (!self.lastCharIsNewline()) {
                    try self.newline();
                }
                try self.printLiteral("}");
            },
            .Literal => {
                const node = self.exprs.get(.Literal, id);
                try self.printLiteral(self.s(node.value));
            },
            .Ident => {
                const node = self.exprs.get(.Ident, id);
                try self.printLiteral(self.s(node.name));
            },
            .Splice => {
                const node = self.exprs.get(.Splice, id);
                try self.printLiteral("`");
                try self.printLiteral(self.s(node.name));
                try self.printLiteral("`");
            },
            .Prefix => {
                const node = self.exprs.get(.Prefix, id);
                try self.printLiteral(prefixOpStr(node.op));
                try self.printExpr(node.right);
            },
            .Infix => {
                const node = self.exprs.get(.Infix, id);
                try self.printExpr(node.left);
                try self.printLiteral(" ");
                try self.printLiteral(infixOpStr(node.op));
                try self.printLiteral(" ");
                try self.printExpr(node.right);
            },
            .Deref => {
                const node = self.exprs.get(.Deref, id);
                try self.printExpr(node.expr);
                try self.printLiteral(".*");
            },
            .ArrayLit => {
                const node = self.exprs.get(.ArrayLit, id);
                try self.printLiteral("[");
                const elems = self.exprs.expr_pool.slice(node.elems);
                if (node.trailing_comma and elems.len > 0) {
                    self.indent += 4;
                    for (elems) |el| {
                        const el_kind = self.exprs.kind(el);
                        const el_loc = exprLocFromId(self.exprs, el, el_kind);
                        try self.emitCommentsBefore(el_loc.start);

                        if (!self.lastCharIsNewline()) try self.newline();
                        try self.ws();
                        try self.printExpr(el);
                        try self.printLiteral(",");

                        var line_end = el_loc.end;
                        while (line_end < self.source.len and self.source[line_end] != '\n') : (line_end += 1) {}
                        try self.flushComments(line_end);
                        self.last_written_loc = line_end;
                    }
                    self.indent -= 4;
                    if (!self.lastCharIsNewline()) try self.newline();
                    try self.ws();
                } else {
                    for (elems, 0..) |el, i| {
                        if (i > 0) try self.printLiteral(", ");
                        try self.printExpr(el);
                    }
                }
                try self.printLiteral("]");
            },
            .Tuple => {
                const node = self.exprs.get(.Tuple, id);
                try self.printLiteral("(");
                const elems = self.exprs.expr_pool.slice(node.elems);
                for (elems, 0..) |el, i| {
                    if (i > 0) try self.printLiteral(", ");
                    try self.printExpr(el);
                }
                try self.printLiteral(")");
            },
            .Parenthesized => {
                const node = self.exprs.get(.Parenthesized, id);
                try self.printLiteral("(");
                try self.printExpr(node.inner);
                try self.printLiteral(")");
            },
            .MapLit => {
                const node = self.exprs.get(.MapLit, id);
                try self.printLiteral("[");
                const entries = self.exprs.kv_pool.slice(node.entries);
                for (entries, 0..) |kv_id, i| {
                    if (i > 0) try self.printLiteral(", ");
                    const kv = self.exprs.KeyValue.get(kv_id);
                    try self.printExpr(kv.key);
                    try self.printLiteral(": ");
                    try self.printExpr(kv.value);
                }
                try self.printLiteral("]");
            },
            .NamedArg => {
                const node = self.exprs.get(.NamedArg, id);
                try self.printLiteral(self.s(node.name));
                try self.printLiteral(" = ");
                try self.printExpr(node.value);
            },
            .Call => {
                const node = self.exprs.get(.Call, id);
                try self.printExpr(node.callee);
                const args = self.exprs.expr_pool.slice(node.args);
                if (args.len == 0) {
                    try self.printLiteral("()");
                } else if (node.trailing_arg_comma) {
                    try self.printLiteral("(");
                    self.indent += 4;
                    for (args) |arg| {
                        const arg_kind = self.exprs.kind(arg);
                        const arg_loc = exprLocFromId(self.exprs, arg, arg_kind);
                        try self.emitCommentsBefore(arg_loc.start);

                        if (!self.lastCharIsNewline()) try self.newline();
                        try self.ws();
                        try self.printExpr(arg);
                        try self.printLiteral(",");

                        var line_end = arg_loc.end;
                        while (line_end < self.source.len and self.source[line_end] != '\n') : (line_end += 1) {}
                        try self.flushComments(line_end);
                        self.last_written_loc = line_end;
                    }
                    self.indent -= 4;
                    if (!self.lastCharIsNewline()) try self.newline();
                    try self.ws();
                    try self.printLiteral(")");
                } else {
                    try self.printLiteral("(");
                    for (args, 0..) |arg, i| {
                        if (i > 0) try self.printLiteral(", ");
                        try self.printExpr(arg);
                    }
                    try self.printLiteral(")");
                }
            },
            .IndexAccess => {
                const node = self.exprs.get(.IndexAccess, id);
                try self.printExpr(node.collection);
                try self.printLiteral("[");
                try self.printExpr(node.index);
                try self.printLiteral("]");
            },
            .FieldAccess => {
                const node = self.exprs.get(.FieldAccess, id);
                try self.printExpr(node.parent);
                try self.printLiteral(".");
                try self.printLiteral(self.s(node.field));
            },
            .StructLit => {
                const node = self.exprs.get(.StructLit, id);
                if (!node.ty.isNone()) {
                    try self.printExpr(node.ty.unwrap());
                }
                const fields = self.exprs.sfv_pool.slice(node.fields);
                if (node.trailing_comma and fields.len > 0) {
                    try self.printLiteral("{");
                    self.indent += 4;
                    for (fields) |fid| {
                        const field = self.exprs.StructFieldValue.get(fid);
                        try self.emitCommentsBefore(self.locStart(field.loc));

                        if (!self.lastCharIsNewline()) try self.newline();
                        try self.ws();
                        if (!field.name.isNone()) {
                            try self.printLiteral(self.s(field.name.unwrap()));
                            try self.printLiteral(": ");
                        }
                        try self.printExpr(field.value);
                        try self.printLiteral(",");

                        var line_end = self.locEnd(field.loc);
                        while (line_end < self.source.len and self.source[line_end] != '\n') : (line_end += 1) {}
                        try self.flushComments(line_end);
                        self.last_written_loc = line_end;
                    }
                    self.indent -= 4;
                    if (!self.lastCharIsNewline()) try self.newline();
                    try self.ws();
                    try self.printLiteral("}");
                } else {
                    try self.printLiteral("{");
                    if (fields.len > 0) try self.printLiteral(" ");
                    for (fields, 0..) |fid, i| {
                        if (i > 0) try self.printLiteral(", ");
                        const field = self.exprs.StructFieldValue.get(fid);
                        if (!field.name.isNone()) {
                            try self.printLiteral(self.s(field.name.unwrap()));
                            try self.printLiteral(": ");
                        }
                        try self.printExpr(field.value);
                    }
                    if (fields.len > 0) try self.printLiteral(" ");
                    try self.printLiteral("}");
                }
            },
            .Function => {
                const node = self.exprs.get(.Function, id);
                try self.printAttrs(node.attrs, .Before);
                if (node.flags.is_async) try self.printLiteral("async ");
                if (node.flags.is_extern) try self.printLiteral("extern ");
                if (node.flags.is_proc) {
                    try self.printLiteral("proc");
                } else {
                    try self.printLiteral("fn");
                }
                try self.printLiteral("(");
                try self.printParams(node.params, node.flags.is_variadic, node.trailing_param_comma);
                try self.printLiteral(")");
                if (!node.result_ty.isNone()) {
                    try self.printLiteral(" ");
                    try self.printExpr(node.result_ty.unwrap());
                }
                if (!node.body.isNone()) {
                    try self.printLiteral(" ");
                    try self.printExpr(node.body.unwrap());
                } else if (!node.raw_asm.isNone()) {
                    try self.printLiteral(" asm ");
                    try self.printLiteral(self.s(node.raw_asm.unwrap()));
                }
            },
            .Comptime => {
                const node = self.exprs.get(.Comptime, id);
                try self.printLiteral("comptime ");
                try self.printExpr(node.payload);
            },
            .Code => {
                const node = self.exprs.get(.Code, id);
                try self.printLiteral("code ");
                try self.printExpr(node.block);
            },
            .Insert => {
                const node = self.exprs.get(.Insert, id);
                try self.printLiteral("insert ");
                try self.printExpr(node.expr);
            },

            .Mlir => {
                const node = self.exprs.get(.Mlir, id);
                try self.printLiteral("mlir");
                switch (node.kind) {
                    .Module => {},
                    .Attribute => try self.printLiteral(" attribute"),
                    .Type => try self.printLiteral(" type"),
                    .Operation => try self.printLiteral(" op"),
                }
                if (!node.args.isNone()) {
                    const args = self.exprs.expr_pool.slice(node.args.asRange());
                    try self.printLiteral("(");
                    for (args, 0..) |arg, i| {
                        if (i > 0) try self.printLiteral(", ");
                        try self.printExpr(arg);
                    }
                    try self.printLiteral(")");
                }

                if (!node.result_ty.isNone()) {
                    try self.printLiteral(" : ");
                    try self.printExpr(node.result_ty.unwrap());
                }

                if (node.pieces.len == 0) {
                    try self.printMlirBody(self.s(node.text));
                    return;
                }

                var tmp = std.ArrayList(u8){};
                defer tmp.deinit(self.gpa);

                const pieces = self.exprs.mlir_piece_pool.slice(node.pieces);
                for (pieces) |pid| {
                    const piece = self.exprs.MlirPiece.get(pid);
                    switch (piece.kind) {
                        .literal => try tmp.appendSlice(self.gpa, self.s(piece.text)),
                        .splice => {
                            try tmp.append(self.gpa, '`');
                            try tmp.appendSlice(self.gpa, self.s(piece.text));
                            try tmp.append(self.gpa, '`');
                        },
                    }
                }

                try self.printMlirBody(tmp.items);
            },
            .Return => {
                const node = self.exprs.get(.Return, id);
                try self.printLiteral("return");
                if (!node.value.isNone()) {
                    try self.printLiteral(" ");
                    try self.printExpr(node.value.unwrap());
                }
            },
            .If => {
                if (try self.tryFormatIfInline(id)) return;
                const node = self.exprs.get(.If, id);
                try self.printLiteral("if ");
                try self.printExpr(node.cond);
                try self.printLiteral(" ");
                try self.printExpr(node.then_block);
                if (!node.else_block.isNone()) {
                    try self.printLiteral(" else ");
                    try self.printExpr(node.else_block.unwrap());
                }
            },
            .While => {
                const node = self.exprs.get(.While, id);
                if (!node.label.isNone()) {
                    try self.printLiteral(self.s(node.label.unwrap()));
                    try self.printLiteral(": ");
                }
                try self.printLiteral("while ");
                if (node.is_pattern) {
                    try self.printLiteral("is ");
                    if (!node.pattern.isNone()) {
                        try self.printPattern(node.pattern.unwrap());
                        try self.printLiteral(" := ");
                    }
                }
                if (!node.cond.isNone()) {
                    try self.printExpr(node.cond.unwrap());
                }
                try self.printLiteral(" ");
                try self.printExpr(node.body);
            },
            .For => {
                const node = self.exprs.get(.For, id);
                if (!node.label.isNone()) {
                    try self.printLiteral(self.s(node.label.unwrap()));
                    try self.printLiteral(": ");
                }
                try self.printLiteral("for ");
                try self.printPattern(node.pattern);
                try self.printLiteral(" in ");
                try self.printExpr(node.iterable);
                try self.printLiteral(" ");
                try self.printExpr(node.body);
            },
            .Match => {
                const node = self.exprs.get(.Match, id);
                try self.printLiteral("match ");
                try self.printExpr(node.expr);
                try self.printLiteral(" {");
                const arms = self.exprs.arm_pool.slice(node.arms);
                for (arms) |aid| {
                    const arm = self.exprs.MatchArm.get(aid);
                    try self.newline();
                    self.indent += 4;
                    try self.ws();
                    try self.printPattern(arm.pattern);
                    if (!arm.guard.isNone()) {
                        try self.printLiteral(" if ");
                        try self.printExpr(arm.guard.unwrap());
                    }
                    try self.printLiteral(" => ");
                    try self.printExpr(arm.body);
                    self.indent -= 4;
                    try self.printLiteral(",");
                }
                try self.newline();
                try self.printLiteral("}");
            },
            .Break => {
                const node = self.exprs.get(.Break, id);
                try self.printLiteral("break");
                if (!node.label.isNone()) {
                    try self.printLiteral(" :");
                    try self.printLiteral(self.s(node.label.unwrap()));
                }
                if (!node.value.isNone()) {
                    try self.printLiteral(" ");
                    try self.printExpr(node.value.unwrap());
                }
            },
            .Continue => {
                const node = self.exprs.get(.Continue, id);
                try self.printLiteral("continue");
                if (!node.label.isNone()) {
                    try self.printLiteral(" :");
                    try self.printLiteral(self.s(node.label.unwrap()));
                }
            },
            .Unreachable => {
                _ = self.exprs.get(.Unreachable, id);
                try self.printLiteral("unreachable");
            },
            .Null => {
                _ = self.exprs.get(.Null, id);
                try self.printLiteral("null");
            },
            .Undefined => {
                _ = self.exprs.get(.Undefined, id);
                try self.printLiteral("undefined");
            },
            .Defer => {
                const node = self.exprs.get(.Defer, id);
                try self.printLiteral("defer ");
                try self.printExpr(node.expr);
            },
            .ErrDefer => {
                const node = self.exprs.get(.ErrDefer, id);
                try self.printLiteral("errdefer ");
                try self.printExpr(node.expr);
            },
            .ErrUnwrap => {
                const node = self.exprs.get(.ErrUnwrap, id);
                try self.printExpr(node.expr);
                try self.printLiteral("!");
            },
            .OptionalUnwrap => {
                const node = self.exprs.get(.OptionalUnwrap, id);
                try self.printExpr(node.expr);
                try self.printLiteral("?");
            },
            .Await => {
                const node = self.exprs.get(.Await, id);
                try self.printExpr(node.expr);
                try self.printLiteral(".await");
            },
            .Closure => {
                const node = self.exprs.get(.Closure, id);
                try self.printLiteral("|");
                try self.printParams(node.params, false, false);
                try self.printLiteral("|");
                if (!node.result_ty.isNone()) {
                    try self.printLiteral(" ");
                    try self.printExpr(node.result_ty.unwrap());
                }
                try self.printLiteral(" ");
                try self.printExpr(node.body);
            },
            .Async => {
                const node = self.exprs.get(.Async, id);
                try self.printLiteral("async ");
                try self.printExpr(node.body);
            },
            .Cast => {
                const node = self.exprs.get(.Cast, id);
                try self.printExpr(node.expr);
                switch (node.kind) {
                    .normal => {
                        try self.printLiteral(".(");
                        try self.printExpr(node.ty);
                        try self.printLiteral(")");
                    },
                    .bitcast => {
                        try self.printLiteral(".^");
                        try self.printExpr(node.ty);
                    },
                    .wrap => {
                        try self.printLiteral(".%");
                        try self.printExpr(node.ty);
                    },
                    .saturate => {
                        try self.printLiteral(".|");
                        try self.printExpr(node.ty);
                    },
                    .checked => {
                        try self.printLiteral(".?");
                        try self.printExpr(node.ty);
                    },
                }
            },
            .Catch => {
                const node = self.exprs.get(.Catch, id);
                try self.printExpr(node.expr);
                try self.printLiteral(" catch ");
                if (!node.binding_name.isNone()) {
                    try self.printLiteral("|");
                    try self.printLiteral(self.s(node.binding_name.unwrap()));
                    try self.printLiteral("| ");
                }
                try self.printExpr(node.handler);
            },
            .Import => {
                const node = self.exprs.get(.Import, id);
                try self.printLiteral("import \"");
                try self.printLiteral(self.s(node.path));
                try self.printLiteral("\"");
            },
            .TypeOf => {
                const node = self.exprs.get(.TypeOf, id);
                try self.printLiteral("typeof(");
                try self.printExpr(node.expr);
                try self.printLiteral(")");
            },
            .ArrayType => {
                const node = self.exprs.get(.ArrayType, id);
                try self.printLiteral("[");
                try self.printExpr(node.size);
                try self.printLiteral("]");
                try self.printExpr(node.elem);
            },
            .DynArrayType => {
                const node = self.exprs.get(.DynArrayType, id);
                try self.printLiteral("[dyn]");
                try self.printExpr(node.elem);
            },
            .MapType => {
                const node = self.exprs.get(.MapType, id);
                try self.printLiteral("[");
                try self.printExpr(node.key);
                try self.printLiteral(": ");
                try self.printExpr(node.value);
                try self.printLiteral("]");
            },
            .SliceType => {
                const node = self.exprs.get(.SliceType, id);
                try self.printLiteral("[]");
                if (node.is_const) try self.printLiteral("const ");
                try self.printExpr(node.elem);
            },
            .OptionalType => {
                const node = self.exprs.get(.OptionalType, id);
                try self.printLiteral("?");
                try self.printExpr(node.elem);
            },
            .ErrorSetType => {
                const node = self.exprs.get(.ErrorSetType, id);
                try self.printExpr(node.err);
                self.needs_indent = false;
                try self.builder.append(self.gpa, '!');
                self.needs_indent = false;
                try self.printExpr(node.value);
            },
            .StructType => {
                const node = self.exprs.get(.StructType, id);
                try self.printAttrs(node.attrs, .Before);
                if (node.is_extern) try self.printLiteral("extern ");
                try self.printLiteral("struct {");
                const fields = self.exprs.sfield_pool.slice(node.fields);
                if (node.trailing_field_comma and fields.len > 0) {
                    self.indent += 4;
                    for (fields) |fid| {
                        const field = self.exprs.StructField.get(fid);
                        try self.emitCommentsBefore(self.locStart(field.loc));

                        if (!self.lastCharIsNewline()) try self.newline();
                        try self.ws();
                        try self.printStructField(fid);
                        try self.printLiteral(",");

                        var line_end = self.locEnd(field.loc);
                        while (line_end < self.source.len and self.source[line_end] != '\n') : (line_end += 1) {}
                        try self.flushComments(line_end);
                        self.last_written_loc = line_end;
                    }
                    self.indent -= 4;
                    if (!self.lastCharIsNewline()) try self.newline();
                    try self.ws();
                } else if (fields.len > 0) {
                    for (fields, 0..) |fid, i| {
                        if (i > 0) try self.printLiteral(", ");
                        try self.printStructField(fid);
                    }
                }
                try self.printLiteral("}");
            },
            .EnumType => {
                const node = self.exprs.get(.EnumType, id);
                try self.printAttrs(node.attrs, .Before);
                if (node.is_extern) try self.printLiteral("extern ");
                try self.printLiteral("enum");
                if (!node.discriminant.isNone()) {
                    try self.printLiteral("(");
                    try self.printExpr(node.discriminant.unwrap());
                    try self.printLiteral(")");
                }
                try self.printLiteral(" {");
                const fields = self.exprs.efield_pool.slice(node.fields);
                if (node.trailing_field_comma and fields.len > 0) {
                    self.indent += 4;
                    for (fields) |eid| {
                        const field = self.exprs.EnumField.get(eid);
                        try self.emitCommentsBefore(self.locStart(field.loc));

                        if (!self.lastCharIsNewline()) try self.newline();
                        try self.ws();
                        try self.printAttrs(field.attrs, .Before);
                        try self.printLiteral(self.s(field.name));
                        if (!field.value.isNone()) {
                            try self.printLiteral(" = ");
                            try self.printExpr(field.value.unwrap());
                        }
                        try self.printLiteral(",");

                        var line_end = self.locEnd(field.loc);
                        while (line_end < self.source.len and self.source[line_end] != '\n') : (line_end += 1) {}
                        try self.flushComments(line_end);
                        self.last_written_loc = line_end;
                    }
                    self.indent -= 4;
                    if (!self.lastCharIsNewline()) try self.newline();
                    try self.ws();
                } else if (fields.len > 0) {
                    for (fields, 0..) |eid, i| {
                        if (i > 0) try self.printLiteral(", ");
                        const field = self.exprs.EnumField.get(eid);
                        try self.printAttrs(field.attrs, .Before);
                        try self.printLiteral(self.s(field.name));
                        if (!field.value.isNone()) {
                            try self.printLiteral(" = ");
                            try self.printExpr(field.value.unwrap());
                        }
                    }
                }
                try self.printLiteral("}");
            },
            .VariantLikeType => {
                const node = self.exprs.get(.VariantLikeType, id);
                try self.printLiteral("variant {");
                const fields = self.exprs.vfield_pool.slice(node.fields);
                if (node.trailing_field_comma and fields.len > 0) {
                    self.indent += 4;
                    for (fields) |fid| {
                        const field = self.exprs.VariantField.get(fid);
                        try self.emitCommentsBefore(self.locStart(field.loc));

                        if (!self.lastCharIsNewline()) try self.newline();
                        try self.ws();
                        try self.printVariantField(fid);
                        try self.printLiteral(",");

                        var line_end = self.locEnd(field.loc);
                        while (line_end < self.source.len and self.source[line_end] != '\n') : (line_end += 1) {}
                        try self.flushComments(line_end);
                        self.last_written_loc = line_end;
                    }
                    self.indent -= 4;
                    if (!self.lastCharIsNewline()) try self.newline();
                    try self.ws();
                } else if (fields.len > 0) {
                    for (fields, 0..) |fid, i| {
                        if (i > 0) try self.printLiteral(", ");
                        try self.printVariantField(fid);
                    }
                }
                try self.printLiteral("}");
            },
            .ErrorType => {
                const node = self.exprs.get(.ErrorType, id);
                try self.printLiteral("error {");
                const fields = self.exprs.vfield_pool.slice(node.fields);
                if (node.trailing_field_comma and fields.len > 0) {
                    self.indent += 4;
                    for (fields) |fid| {
                        const field = self.exprs.VariantField.get(fid);
                        try self.emitCommentsBefore(self.locStart(field.loc));

                        if (!self.lastCharIsNewline()) try self.newline();
                        try self.ws();
                        try self.printVariantField(fid);
                        try self.printLiteral(",");

                        var line_end = self.locEnd(field.loc);
                        while (line_end < self.source.len and self.source[line_end] != '\n') : (line_end += 1) {}
                        try self.flushComments(line_end);
                        self.last_written_loc = line_end;
                    }
                    self.indent -= 4;
                    if (!self.lastCharIsNewline()) try self.newline();
                    try self.ws();
                } else if (fields.len > 0) {
                    for (fields, 0..) |fid, i| {
                        if (i > 0) try self.printLiteral(", ");
                        try self.printVariantField(fid);
                    }
                }
                try self.printLiteral("}");
            },
            .UnionType => {
                const node = self.exprs.get(.UnionType, id);
                try self.printAttrs(node.attrs, .Before);
                if (node.is_extern) try self.printLiteral("extern ");
                try self.printLiteral("union {");
                const fields = self.exprs.sfield_pool.slice(node.fields);
                if (node.trailing_field_comma and fields.len > 0) {
                    self.indent += 4;
                    for (fields) |fid| {
                        const field = self.exprs.StructField.get(fid);
                        try self.emitCommentsBefore(self.locStart(field.loc));

                        if (!self.lastCharIsNewline()) try self.newline();
                        try self.ws();
                        try self.printStructField(fid);
                        try self.printLiteral(",");

                        var line_end = self.locEnd(field.loc);
                        while (line_end < self.source.len and self.source[line_end] != '\n') : (line_end += 1) {}
                        try self.flushComments(line_end);
                        self.last_written_loc = line_end;
                    }
                    self.indent -= 4;
                    if (!self.lastCharIsNewline()) try self.newline();
                    try self.ws();
                } else if (fields.len > 0) {
                    for (fields, 0..) |fid, i| {
                        if (i > 0) try self.printLiteral(", ");
                        try self.printStructField(fid);
                    }
                }
                try self.printLiteral("}");
            },
            .PointerType => {
                const node = self.exprs.get(.PointerType, id);
                try self.printLiteral("*");
                if (node.is_const) try self.printLiteral("const ");
                try self.printExpr(node.elem);
            },
            .SimdType => {
                const node = self.exprs.get(.SimdType, id);
                try self.printLiteral("simd(");
                try self.printExpr(node.lanes);
                try self.printLiteral(", ");
                try self.printExpr(node.elem);
                try self.printLiteral(")");
            },
            .ComplexType => {
                const node = self.exprs.get(.ComplexType, id);
                try self.printLiteral("complex(");
                try self.printExpr(node.elem);
                try self.printLiteral(")");
            },
            .TensorType => {
                const node = self.exprs.get(.TensorType, id);
                try self.printLiteral("tensor(");
                const shape = self.exprs.expr_pool.slice(node.shape);
                for (shape, 0..) |si, i| {
                    if (i > 0) try self.printLiteral(", ");
                    try self.printExpr(si);
                }
                try self.printLiteral(", ");
                try self.printExpr(node.elem);
                try self.printLiteral(")");
            },
            .TypeType => {
                _ = self.exprs.get(.TypeType, id);
                try self.printLiteral("type");
            },
            .AnyType => {
                _ = self.exprs.get(.AnyType, id);
                try self.printLiteral("any");
            },
            .NoreturnType => {
                _ = self.exprs.get(.NoreturnType, id);
                try self.printLiteral("noreturn");
            },
        }
    }

    // ------------------------------------------------------------
    // Helpers for expressions / patterns
    // ------------------------------------------------------------
    /// Emit the parameter list described by `r`.
    fn printParams(self: *Formatter, r: cst.RangeOf(cst.ParamId), is_variadic: bool, trailing: bool) !void {
        _ = is_variadic;
        const params = self.exprs.param_pool.slice(r);
        if (trailing and params.len > 0) {
            self.indent += 4;
            for (params) |pid| {
                const param = self.exprs.Param.get(pid);
                const start = self.locStart(param.loc);
                try self.emitCommentsBefore(start);

                if (!self.lastCharIsNewline()) try self.newline();
                try self.ws();
                try self.printAttrs(param.attrs, .After);
                if (param.is_comptime) {
                    try self.printLiteral("comptime ");
                }
                if (!param.pat.isNone()) {
                    try self.printExpr(param.pat.unwrap());
                }
                if (!param.pat.isNone() and !param.ty.isNone()) {
                    try self.printLiteral(": ");
                }
                if (!param.ty.isNone()) {
                    try self.printExpr(param.ty.unwrap());
                }
                if (!param.value.isNone()) {
                    try self.printLiteral(" = ");
                    try self.printExpr(param.value.unwrap());
                }
                try self.printLiteral(",");

                var line_end = self.locEnd(param.loc);
                while (line_end < self.source.len and self.source[line_end] != '\n') : (line_end += 1) {}
                try self.flushComments(line_end);
                self.last_written_loc = line_end;
            }
            self.indent -= 4;
            if (!self.lastCharIsNewline()) try self.newline();
            try self.ws();
            return;
        }

        for (params, 0..) |pid, i| {
            if (i > 0) try self.printLiteral(", ");
            const param = self.exprs.Param.get(pid);
            try self.printAttrs(param.attrs, .After);
            if (param.is_comptime) {
                try self.printLiteral("comptime ");
            }
            if (!param.pat.isNone()) {
                try self.printExpr(param.pat.unwrap());
            }
            if (!param.pat.isNone() and !param.ty.isNone()) {
                try self.printLiteral(": ");
            }
            if (!param.ty.isNone()) {
                try self.printExpr(param.ty.unwrap());
            }
            if (!param.value.isNone()) {
                try self.printLiteral(" = ");
                try self.printExpr(param.value.unwrap());
            }
        }
    }

    /// Print a struct field declaration with its type/attrs.
    fn printStructField(self: *Formatter, id: cst.StructFieldId) !void {
        const field = self.exprs.StructField.get(id);
        try self.printAttrs(field.attrs, .Before);
        try self.printLiteral(self.s(field.name));
        try self.printLiteral(": ");
        try self.printExpr(field.ty);
        if (!field.value.isNone()) {
            try self.printLiteral(" = ");
            try self.printExpr(field.value.unwrap());
        }
    }

    /// Print a variant payload field description.
    fn printVariantField(self: *Formatter, id: cst.VariantFieldId) !void {
        const field = self.exprs.VariantField.get(id);
        try self.printAttrs(field.attrs, .Before);
        try self.printLiteral(self.s(field.name));
        switch (field.ty_tag) {
            .none => {},
            .Tuple => {
                const elems = self.exprs.expr_pool.slice(field.tuple_elems);
                if (field.tuple_trailing_comma and elems.len > 0) {
                    try self.printLiteral("(");
                    self.indent += 4;
                    for (elems) |eid| {
                        try self.newline();
                        try self.ws();
                        try self.printExpr(eid);
                        try self.printLiteral(",");
                    }
                    self.indent -= 4;
                    try self.newline();
                    try self.ws();
                    try self.printLiteral(")");
                } else {
                    try self.printLiteral("(");
                    try self.printExprs(field.tuple_elems, ", ");
                    try self.printLiteral(")");
                }
            },
            .Struct => {
                const payload_fields = self.exprs.sfield_pool.slice(field.struct_fields);
                if (field.struct_trailing_comma and payload_fields.len > 0) {
                    try self.printLiteral(" {");
                    self.indent += 4;
                    for (payload_fields) |fid| {
                        try self.newline();
                        try self.ws();
                        try self.printStructField(fid);
                        try self.printLiteral(",");
                    }
                    self.indent -= 4;
                    try self.newline();
                    try self.ws();
                    try self.printLiteral("}");
                } else {
                    try self.printLiteral(" {");
                    for (payload_fields, 0..) |fid, i| {
                        if (i > 0) try self.printLiteral(", ");
                        try self.printStructField(fid);
                    }
                    try self.printLiteral("}");
                }
            },
        }
        if (!field.value.isNone()) {
            try self.printLiteral(" = ");
            try self.printExpr(field.value.unwrap());
        }
    }

    /// Print every expression in `r`, separating them with `sep`.
    fn printExprs(self: *Formatter, r: cst.RangeOf(cst.ExprId), sep: []const u8) !void {
        const ids = self.exprs.expr_pool.slice(r);
        for (ids, 0..) |eid, i| {
            if (i > 0) try self.printLiteral(sep);
            try self.printExpr(eid);
        }
    }

    /// Positions that dictate whether attributes precede or follow the declaration.
    const AttrPos = enum {
        /// Emit attributes before the declaration/pattern.
        Before,
        /// Emit attributes after the declaration/pattern.
        After,
    };
    /// Print attributes associated with declarations/patterns at `pos`.
    fn printAttrs(self: *Formatter, opt_r: cst.OptRangeAttr, pos: AttrPos) anyerror!void {
        if (opt_r.isNone()) return;
        const r = opt_r.asRange();
        const attrs = self.exprs.attr_pool.slice(r);
        if (attrs.len == 0) return;

        try self.printLiteral("@[");
        for (attrs, 0..) |aid, i| {
            if (i > 0) try self.printLiteral(", ");
            const attr = self.exprs.Attribute.get(aid);
            try self.ws();
            try self.printLiteral(self.s(attr.name));
            if (!attr.value.isNone()) {
                try self.printLiteral(" = ");
                try self.printExpr(attr.value.unwrap());
            }
            _ = pos;
        }
        try self.printLiteral("] ");
    }

    // ------------------------------------------------------------
    // Patterns
    // ------------------------------------------------------------
    /// Format the pattern `id`, recursing for nested structures.
    fn printPattern(self: *Formatter, id: cst.PatternId) anyerror!void {
        const kind = self.pats.kind(id);
        switch (kind) {
            .Wildcard => try self.printLiteral("_"),
            .Literal => {
                const node = self.pats.get(.Literal, id);
                try self.printExpr(node.expr);
            },
            .Path => {
                const node = self.pats.get(.Path, id);
                const segs = self.pats.seg_pool.slice(node.segments);
                for (segs, 0..) |sid, i| {
                    if (i > 0) try self.printLiteral(".");
                    const seg = self.pats.PathSeg.get(sid);
                    try self.printLiteral(self.s(seg.name));
                }
            },
            .Binding => {
                const node = self.pats.get(.Binding, id);
                if (node.by_ref) try self.printLiteral("ref ");
                if (node.is_mut) try self.printLiteral("mut ");
                try self.printLiteral(self.s(node.name));
            },
            .Parenthesized => {
                const node = self.pats.get(.Parenthesized, id);
                try self.printLiteral("(");
                try self.printPattern(node.pattern);
                try self.printLiteral(")");
            },
            .Tuple => {
                const node = self.pats.get(.Tuple, id);
                try self.printLiteral("(");
                const elems = self.pats.pat_pool.slice(node.elems);
                for (elems, 0..) |pid, i| {
                    if (i > 0) try self.printLiteral(", ");
                    try self.printPattern(pid);
                }
                try self.printLiteral(")");
            },
            .Slice => {
                const node = self.pats.get(.Slice, id);
                try self.printLiteral("[");
                const elems = self.pats.pat_pool.slice(node.elems);
                for (elems, 0..) |pid, i| {
                    if (i > 0) try self.printLiteral(", ");
                    if (node.has_rest and node.rest_index == i) {
                        try self.printLiteral("..");
                        if (!node.rest_binding.isNone()) {
                            try self.printPattern(node.rest_binding.unwrap());
                        }
                        if (i < elems.len) try self.printLiteral(", ");
                    }
                    try self.printPattern(pid);
                }
                if (node.has_rest and node.rest_index == elems.len) {
                    if (elems.len > 0) try self.printLiteral(", ");
                    try self.printLiteral("..");
                    if (!node.rest_binding.isNone()) {
                        try self.printPattern(node.rest_binding.unwrap());
                    }
                }
                try self.printLiteral("]");
            },
            .Struct => {
                const node = self.pats.get(.Struct, id);
                try self.printPatternPath(node.path);
                try self.printLiteral(" {");
                const fields = self.pats.field_pool.slice(node.fields);
                for (fields, 0..) |fid, i| {
                    if (i > 0) try self.printLiteral(", ");
                    try self.printPatternField(fid);
                }
                if (node.has_rest) {
                    if (fields.len > 0) try self.printLiteral(", ");
                    try self.printLiteral("..");
                }
                try self.printLiteral("}");
            },
            .VariantTuple => {
                const node = self.pats.get(.VariantTuple, id);
                try self.printPatternPath(node.path);
                try self.printLiteral("(");
                const elems = self.pats.pat_pool.slice(node.elems);
                for (elems, 0..) |pid, i| {
                    if (i > 0) try self.printLiteral(", ");
                    try self.printPattern(pid);
                }
                try self.printLiteral(")");
            },
            .VariantStruct => {
                const node = self.pats.get(.VariantStruct, id);
                try self.printPatternPath(node.path);
                try self.printLiteral(" {");
                const fields = self.pats.field_pool.slice(node.fields);
                for (fields, 0..) |fid, i| {
                    if (i > 0) try self.printLiteral(", ");
                    try self.printPatternField(fid);
                }
                if (node.has_rest) {
                    if (fields.len > 0) try self.printLiteral(", ");
                    try self.printLiteral("..");
                }
                try self.printLiteral("}");
            },
            .Range => {
                const node = self.pats.get(.Range, id);
                if (!node.start.isNone()) try self.printExpr(node.start.unwrap());
                if (node.inclusive_right) {
                    try self.printLiteral("..=");
                } else {
                    try self.printLiteral("..");
                }
                if (!node.end.isNone()) try self.printExpr(node.end.unwrap());
            },
            .Or => {
                const node = self.pats.get(.Or, id);
                const alts = self.pats.pat_pool.slice(node.alts);
                for (alts, 0..) |pid, i| {
                    if (i > 0) try self.printLiteral(" | ");
                    try self.printPattern(pid);
                }
            },
            .At => {
                const node = self.pats.get(.At, id);
                try self.printLiteral(self.s(node.binder));
                try self.printLiteral(" @ ");
                try self.printPattern(node.pattern);
            },
        }
    }

    /// Print the segments of `path` joined by dots.
    fn printPatternPath(self: *Formatter, path: cst.RangeOf(cst.PathSegId)) !void {
        const segs = self.pats.seg_pool.slice(path);
        for (segs, 0..) |sid, i| {
            if (i > 0) try self.printLiteral(".");
            const seg = self.pats.PathSeg.get(sid);
            try self.printLiteral(self.s(seg.name));
        }
    }

    /// Print a pattern field entry (name + nested pattern).
    fn printPatternField(self: *Formatter, id: cst.PatFieldId) !void {
        const field = self.pats.StructField.get(id);
        try self.printLiteral(self.s(field.name));
        try self.printLiteral(": ");
        try self.printPattern(field.pattern);
    }
};

/// Return the textual representation of a prefix operator.
fn prefixOpStr(op: cst.PrefixOp) []const u8 {
    return switch (op) {
        .plus => "+",
        .minus => "-",
        .address_of => "&",
        .logical_not => "!",
        .range => "..",
        .range_inclusive => "..=",
    };
}

/// Return the textual representation of an infix operator.
fn infixOpStr(op: cst.InfixOp) []const u8 {
    return switch (op) {
        .add => "+",
        .sub => "-",
        .mul => "*",
        .div => "/",
        .mod => "%",
        .shl => "<<",
        .shr => ">>",
        .add_sat => "+|",
        .add_wrap => "+%",
        .sub_sat => "-|",
        .sub_wrap => "-%",
        .mul_sat => "*|",
        .mul_wrap => "*%",
        .shl_sat => "<<|",
        .b_and => "&",
        .b_or => "|",
        .b_xor => "^",
        .eq => "==",
        .neq => "!=",
        .lt => "<",
        .lte => "<=",
        .gt => ">",
        .gte => ">=",
        .logical_and => "and",
        .logical_or => "or",
        .range => "..",
        .range_inclusive => "..=",
        .assign => "=",
        .error_union => "!",
        .error_catch => "catch",
        .unwrap_orelse => "orelse",
        .add_assign => "+=",
        .sub_assign => "-=",
        .mul_assign => "*=",
        .div_assign => "/=",
        .mod_assign => "%=",
        .shl_assign => "<<=",
        .shr_assign => ">>=",
        .and_assign => "&=",
        .or_assign => "|=",
        .xor_assign => "^=",
        .mul_wrap_assign => "*%=",
        .add_wrap_assign => "+%=",
        .sub_wrap_assign => "-%=",
        .mul_sat_assign => "*|=",
        .add_sat_assign => "+|=",
        .sub_sat_assign => "-|=",
        .shl_sat_assign => "<<|=",
        .contains => "in",
    };
}
