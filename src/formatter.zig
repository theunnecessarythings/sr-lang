const std = @import("std");
const cst = @import("cst.zig");
const Parser = @import("parser.zig").Parser;
const compile = @import("compile.zig");
const diag = @import("diagnostics.zig");
const Loc = @import("lexer.zig").Token.Loc;

/// Format a single source buffer and return the formatted text.
pub fn formatSource(gpa: std.mem.Allocator, source: [:0]const u8, file_path: []const u8) ![]u8 {
    var ctx = compile.Context.init(gpa);
    defer ctx.deinit();
    ctx.load_imports = false;

    const file_id = try ctx.source_manager.setVirtualSourceByPath(file_path, source);
    defer ctx.source_manager.clearVirtualSource(file_id);

    var diagnostics = diag.Diagnostics.init(gpa, ctx.type_store, ctx.interner);
    defer diagnostics.deinit();

    var parser = Parser.init(gpa, source, file_id, &diagnostics, &ctx);
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

const Formatter = struct {
    gpa: std.mem.Allocator,
    source: []const u8,
    exprs: *cst.ExprStore,
    pats: *cst.PatternStore,
    program: cst.ProgramDO,
    comments: []const cst.Comment,
    locs: *cst.LocStore,

    builder: std.ArrayList(u8) = .{},
    indent: usize = 0,
    needs_indent: bool = true,
    comment_idx: usize = 0,

    // Tracks the end index of the last printed token/node.
    last_written_loc: usize = 0,

    fn format(self: *Formatter) ![]u8 {
        self.builder = .{};
        self.last_written_loc = 0;
        self.comment_idx = 0;
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
    fn ws(self: *Formatter) !void {
        if (!self.needs_indent) return;
        var i: usize = 0;
        while (i < self.indent) : (i += 1) {
            try self.builder.append(self.gpa, ' ');
        }
        self.needs_indent = false;
    }

    fn newline(self: *Formatter) !void {
        try self.builder.append(self.gpa, '\n');
        self.needs_indent = true;
    }

    fn lastCharIsNewline(self: *Formatter) bool {
        return self.builder.items.len > 0 and self.builder.items[self.builder.items.len - 1] == '\n';
    }

    fn endsWithDoubleNewline(self: *Formatter) bool {
        return self.builder.items.len >= 2 and
            self.builder.items[self.builder.items.len - 1] == '\n' and
            self.builder.items[self.builder.items.len - 2] == '\n';
    }

    fn printf(self: *Formatter, comptime fmt: []const u8, args: anytype) !void {
        try self.ws();
        try std.fmt.format(self.builder.writer(self.gpa), fmt, args);
    }

    inline fn s(self: *const Formatter, id: cst.StrId) []const u8 {
        return self.exprs.strs.get(id);
    }

    inline fn locStart(self: *const Formatter, loc: cst.LocId) usize {
        return self.locs.get(loc).start;
    }

    inline fn locEnd(self: *const Formatter, loc: cst.LocId) usize {
        return self.locs.get(loc).end;
    }

    fn updateLastWritten(self: *Formatter, loc: cst.LocId) void {
        const end = self.locEnd(loc);
        if (end > self.last_written_loc) self.last_written_loc = end;
    }

    fn emitCommentsBefore(self: *Formatter, pos: usize) !void {
        try self.flushComments(pos);
    }

    // Scans backwards in the source to determine if the comment is on a new line.
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

    fn flushComments(self: *Formatter, limit: usize) !void {
        while (self.comment_idx < self.comments.len) {
            const c = self.comments[self.comment_idx];
            const loc = self.locs.get(c.loc);

            if (loc.start >= limit) break;

            const is_line_comment = self.isLineComment(loc.start);
            const gap_has_blank = self.gapHasExtraBlank(self.last_written_loc, loc.start);

            if (is_line_comment) {
                // Only add newline if we're not at the very start of the file
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
                if (self.builder.items.len > 0 and
                    self.builder.items[self.builder.items.len - 1] != ' ' and
                    self.builder.items[self.builder.items.len - 1] != '\n')
                {
                    try self.builder.append(self.gpa, ' ');
                }
            }

            try self.printCommentBody(c, loc);

            switch (c.kind) {
                .line, .doc, .container_doc => {
                    try self.newline();
                },
                .block => {
                    // Inline block comments do not force a newline
                },
            }

            self.last_written_loc = loc.end;
            self.comment_idx += 1;
        }
    }

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
            .block => {
                try self.builder.appendSlice(self.gpa, text);
            },
        }
    }

    fn gapHasExtraBlank(self: *Formatter, start: usize, end: usize) bool {
        if (start >= end or end > self.source.len) return false;
        const slice = self.source[start..end];
        var nl: usize = 0;
        for (slice) |byte| {
            if (byte == '\n') nl += 1;
            if (nl >= 2) return true;
        }
        return false;
    }

    // ------------------------------------------------------------
    // Program / Decl printing
    // ------------------------------------------------------------
    fn printProgram(self: *Formatter) !void {
        if (!self.program.package_name.isNone() and !self.program.package_loc.isNone()) {
            const pkg_loc_id = self.program.package_loc.unwrap();
            const pkg_loc = self.locs.get(pkg_loc_id);
            const text = self.source[pkg_loc.start..pkg_loc.end];

            if (std.mem.eql(u8, text, "package")) {
                try self.emitCommentsBefore(pkg_loc.start);
                try self.printf("package {s}", .{self.s(self.program.package_name.unwrap())});

                // Find the end of the line to handle any inline comments
                var line_end = pkg_loc.end;
                while (line_end < self.source.len and self.source[line_end] != '\n') : (line_end += 1) {}

                // Emit any comments on the same line as the package declaration
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
            const is_import = self.isImportDecl(did);
            const is_function = self.isFunctionDecl(did);
            const has_body = self.isFunctionWithBody(did);
            const kind: u8 = if (is_import) 1 else if (is_function) 2 else 3;

            var needs_blank = false;
            if (i > 0) {
                // Rule: Blank line when transitioning from imports to other declarations
                if (prev_kind == 1 and kind != 1) {
                    needs_blank = true;
                }
                // Rule: Blank line between functions with bodies (not extern declarations)
                if (has_body and prev_has_body) {
                    needs_blank = true;
                }
                // Rule: Respect manual blank lines in source
                if (self.gapHasExtraBlank(self.last_written_loc, start_loc)) {
                    needs_blank = true;
                }
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

            self.updateLastWritten(row.loc);
            prev_kind = kind;
            prev_has_body = has_body;
        }
        try self.newline();
    }

    fn isImportDecl(self: *Formatter, did: cst.DeclId) bool {
        const row = self.exprs.Decl.get(did);
        const rhs_kind = self.exprs.index.kinds.items[row.rhs.toRaw()];
        return rhs_kind == .Import;
    }

    fn isFunctionDecl(self: *Formatter, did: cst.DeclId) bool {
        const row = self.exprs.Decl.get(did);
        const rhs_kind = self.exprs.index.kinds.items[row.rhs.toRaw()];
        return rhs_kind == .Function;
    }

    fn isFunctionWithBody(self: *Formatter, did: cst.DeclId) bool {
        const row = self.exprs.Decl.get(did);
        const rhs_kind = self.exprs.index.kinds.items[row.rhs.toRaw()];
        if (rhs_kind != .Function) return false;

        const func = self.exprs.get(.Function, row.rhs);
        return !func.body.isNone();
    }

    fn printDecl(self: *Formatter, id: cst.DeclId) !void {
        const row = self.exprs.Decl.get(id);
        try self.emitCommentsBefore(self.locStart(row.loc));

        if (!row.lhs.isNone()) {
            try self.printExpr(row.lhs.unwrap());
        }

        if (!row.ty.isNone()) {
            try self.printf(": ", .{});
            try self.printExpr(row.ty.unwrap());
            if (row.flags.is_const) {
                try self.printf(" : ", .{});
            } else {
                try self.printf(" = ", .{});
            }
            try self.printExpr(row.rhs);
            return;
        }

        if (!row.lhs.isNone()) {
            if (row.flags.is_const) {
                try self.printf(" :: ", .{});
            } else if (row.flags.is_assign) {
                try self.printf(" = ", .{});
            } else {
                try self.printf(" := ", .{});
            }
            try self.printExpr(row.rhs);
            return;
        }

        try self.printExpr(row.rhs);
    }

    inline fn exprLocFromId(exprs: *cst.ExprStore, eid: cst.ExprId) Loc {
        @setEvalBranchQuota(10000);
        const k = exprs.index.kinds.items[eid.toRaw()];
        return switch (k) {
            inline else => |x| exprs.locs.get(exprs.get(x, eid).loc),
        };
    }

    // ------------------------------------------------------------
    // Expressions
    // ------------------------------------------------------------
    pub fn printExpr(self: *Formatter, id: cst.ExprId) anyerror!void {
        const kind = self.exprs.index.kinds.items[id.toRaw()];

        // Auto-update cursor at the end of the expression
        defer {
            @setEvalBranchQuota(100000);
            const loc = exprLocFromId(self.exprs, id);
            if (loc.end > self.last_written_loc) {
                self.last_written_loc = loc.end;
            }
        }

        switch (kind) {
            .Block => {
                const node = self.exprs.get(.Block, id);
                const block_loc = self.exprs.locs.get(node.loc);

                try self.printf("{{", .{});

                // Update cursor past '{'
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
                    // Preserve blank lines inside blocks
                    if (self.gapHasExtraBlank(self.last_written_loc, start)) {
                        if (!self.endsWithDoubleNewline()) try self.newline();
                    }

                    try self.printDecl(did);
                    self.updateLastWritten(row.loc);
                }

                try self.emitCommentsBefore(block_loc.end);

                self.indent -= 4;
                if (!self.lastCharIsNewline()) {
                    try self.newline();
                }
                try self.printf("}}", .{});
            },
            .Literal => {
                const node = self.exprs.get(.Literal, id);
                try self.printf("{s}", .{self.s(node.value)});
            },
            .Ident => {
                const node = self.exprs.get(.Ident, id);
                try self.printf("{s}", .{self.s(node.name)});
            },
            .Prefix => {
                const node = self.exprs.get(.Prefix, id);
                try self.printf("{s}", .{prefixOpStr(node.op)});
                try self.printExpr(node.right);
            },
            .Infix => {
                const node = self.exprs.get(.Infix, id);
                try self.printExpr(node.left);
                try self.printf(" {s} ", .{infixOpStr(node.op)});
                try self.printExpr(node.right);
            },
            .Deref => {
                const node = self.exprs.get(.Deref, id);
                try self.printExpr(node.expr);
                try self.printf(".*", .{});
            },
            .ArrayLit => {
                const node = self.exprs.get(.ArrayLit, id);
                try self.printf("[", .{});
                const elems = self.exprs.expr_pool.slice(node.elems);
                if (node.trailing_comma and elems.len > 0) {
                    self.indent += 4;
                    for (elems) |el| {
                        try self.newline();
                        try self.ws();
                        try self.printExpr(el);
                        try self.printf(",", .{});
                    }
                    self.indent -= 4;
                    try self.newline();
                    try self.ws();
                } else {
                    for (elems, 0..) |el, i| {
                        if (i > 0) try self.printf(", ", .{});
                        try self.printExpr(el);
                    }
                }
                try self.printf("]", .{});
            },
            .Tuple => {
                const node = self.exprs.get(.Tuple, id);
                try self.printf("(", .{});
                const elems = self.exprs.expr_pool.slice(node.elems);
                for (elems, 0..) |el, i| {
                    if (i > 0) try self.printf(", ", .{});
                    try self.printExpr(el);
                }
                try self.printf(")", .{});
            },
            .Parenthesized => {
                const node = self.exprs.get(.Parenthesized, id);
                try self.printf("(", .{});
                try self.printExpr(node.inner);
                try self.printf(")", .{});
            },
            .MapLit => {
                const node = self.exprs.get(.MapLit, id);
                try self.printf("[", .{});
                const entries = self.exprs.kv_pool.slice(node.entries);
                for (entries, 0..) |kv_id, i| {
                    if (i > 0) try self.printf(", ", .{});
                    const kv = self.exprs.KeyValue.get(kv_id);
                    try self.printExpr(kv.key);
                    try self.printf(": ", .{});
                    try self.printExpr(kv.value);
                }
                try self.printf("]", .{});
            },
            .Call => {
                const node = self.exprs.get(.Call, id);
                try self.printExpr(node.callee);
                const args = self.exprs.expr_pool.slice(node.args);
                if (args.len == 0) {
                    try self.printf("()", .{});
                } else if (node.trailing_arg_comma) {
                    try self.printf("(", .{});
                    self.indent += 4;
                    for (args) |arg| {
                        try self.newline();
                        try self.ws();
                        try self.printExpr(arg);
                        try self.printf(",", .{});
                    }
                    self.indent -= 4;
                    try self.newline();
                    try self.ws();
                    try self.printf(")", .{});
                } else {
                    try self.printf("(", .{});
                    for (args, 0..) |arg, i| {
                        if (i > 0) try self.printf(", ", .{});
                        try self.printExpr(arg);
                    }
                    try self.printf(")", .{});
                }
            },
            .IndexAccess => {
                const node = self.exprs.get(.IndexAccess, id);
                try self.printExpr(node.collection);
                try self.printf("[", .{});
                try self.printExpr(node.index);
                try self.printf("]", .{});
            },
            .FieldAccess => {
                const node = self.exprs.get(.FieldAccess, id);
                try self.printExpr(node.parent);
                try self.printf(".{s}", .{self.s(node.field)});
            },
            .StructLit => {
                const node = self.exprs.get(.StructLit, id);
                if (!node.ty.isNone()) {
                    try self.printExpr(node.ty.unwrap());
                    // try self.printf(" ", .{}); // Removed space
                }
                const fields = self.exprs.sfv_pool.slice(node.fields);
                if (node.trailing_comma and fields.len > 0) {
                    try self.printf("{{", .{});
                    self.indent += 4;
                    for (fields) |fid| {
                        const field = self.exprs.StructFieldValue.get(fid);
                        try self.newline();
                        try self.ws();
                        if (!field.name.isNone()) {
                            try self.printf("{s}: ", .{self.s(field.name.unwrap())});
                        }
                        try self.printExpr(field.value);
                        try self.printf(",", .{});
                    }
                    self.indent -= 4;
                    try self.newline();
                    try self.ws();
                    try self.printf("}}", .{});
                } else {
                    try self.printf("{{", .{});
                    if (fields.len > 0) try self.printf(" ", .{});
                    for (fields, 0..) |fid, i| {
                        if (i > 0) try self.printf(", ", .{});
                        const field = self.exprs.StructFieldValue.get(fid);
                        if (!field.name.isNone()) {
                            try self.printf("{s}: ", .{self.s(field.name.unwrap())});
                        }
                        try self.printExpr(field.value);
                    }
                    if (fields.len > 0) try self.printf(" ", .{});
                    try self.printf("}}", .{});
                }
            },
            .Function => {
                const node = self.exprs.get(.Function, id);
                try self.printAttrs(node.attrs, .Before);
                if (node.flags.is_async) try self.printf("async ", .{});
                if (node.flags.is_extern) try self.printf("extern ", .{});
                if (node.flags.is_proc) {
                    try self.printf("proc", .{});
                } else {
                    try self.printf("fn", .{});
                }
                try self.printf("(", .{});
                try self.printParams(node.params, node.flags.is_variadic, node.trailing_param_comma);
                try self.printf(")", .{});
                if (!node.result_ty.isNone()) {
                    try self.printf(" ", .{});
                    try self.printExpr(node.result_ty.unwrap());
                }
                if (!node.body.isNone()) {
                    try self.printf(" ", .{});
                    try self.printExpr(node.body.unwrap());
                } else if (!node.raw_asm.isNone()) {
                    try self.printf(" asm {s}", .{self.s(node.raw_asm.unwrap())});
                }
            },
            .Comptime => {
                const node = self.exprs.get(.Comptime, id);
                try self.printf("comptime ", .{});
                try self.printExpr(node.payload);
            },
            .Code => {
                const node = self.exprs.get(.Code, id);
                try self.printf("code ", .{});
                try self.printExpr(node.block);
            },
            .Insert => {
                const node = self.exprs.get(.Insert, id);
                try self.printf("insert ", .{});
                try self.printExpr(node.expr);
            },
            .Mlir => {
                const node = self.exprs.get(.Mlir, id);
                const k = switch (node.kind) {
                    .Module => "",
                    .Attribute => " attribute",
                    .Type => " type",
                    .Operation => " op",
                };
                try self.printf("mlir{s}", .{k});
                if (!node.args.isNone()) {
                    const args = self.exprs.expr_pool.slice(node.args.asRange());
                    try self.printf("(", .{});
                    for (args, 0..) |arg, i| {
                        if (i > 0) try self.printf(", ", .{});
                        try self.printExpr(arg);
                    }
                    try self.printf(")", .{});
                }
                if (node.pieces.len == 0) {
                    try self.printf(" {{ {s} }}", .{self.s(node.text)});
                } else {
                    try self.printf(" {{ ", .{});
                    const pieces = self.exprs.mlir_piece_pool.slice(node.pieces);
                    for (pieces) |pid| {
                        const piece = self.exprs.MlirPiece.get(pid);
                        switch (piece.kind) {
                            .literal => try self.printf("{s}", .{self.s(piece.text)}),
                            .splice => try self.printf("${s}", .{self.s(piece.text)}),
                        }
                    }
                    try self.printf(" }}", .{});
                }
            },
            .Return => {
                const node = self.exprs.get(.Return, id);
                try self.printf("return", .{});
                if (!node.value.isNone()) {
                    try self.printf(" ", .{});
                    try self.printExpr(node.value.unwrap());
                }
            },
            .If => {
                const node = self.exprs.get(.If, id);
                try self.printf("if ", .{});
                try self.printExpr(node.cond);
                try self.printf(" ", .{});
                try self.printExpr(node.then_block);
                if (!node.else_block.isNone()) {
                    try self.printf(" else ", .{});
                    try self.printExpr(node.else_block.unwrap());
                }
            },
            .While => {
                const node = self.exprs.get(.While, id);
                if (!node.label.isNone()) try self.printf("{s}: ", .{self.s(node.label.unwrap())});
                try self.printf("while ", .{});
                if (node.is_pattern) {
                    try self.printf("is ", .{});
                    if (!node.pattern.isNone()) {
                        try self.printPattern(node.pattern.unwrap());
                        try self.printf(" := ", .{});
                    }
                }
                if (!node.cond.isNone()) {
                    try self.printExpr(node.cond.unwrap());
                }
                try self.printf(" ", .{});
                try self.printExpr(node.body);
            },
            .For => {
                const node = self.exprs.get(.For, id);
                if (!node.label.isNone()) try self.printf("{s}: ", .{self.s(node.label.unwrap())});
                try self.printf("for ", .{});
                try self.printPattern(node.pattern);
                try self.printf(" in ", .{});
                try self.printExpr(node.iterable);
                try self.printf(" ", .{});
                try self.printExpr(node.body);
            },
            .Match => {
                const node = self.exprs.get(.Match, id);
                try self.printf("match ", .{});
                try self.printExpr(node.expr);
                try self.printf(" {{", .{});
                const arms = self.exprs.arm_pool.slice(node.arms);
                for (arms) |aid| {
                    try self.printf(",", .{});
                    const arm = self.exprs.MatchArm.get(aid);
                    try self.newline();
                    self.indent += 4;
                    try self.ws();
                    try self.printPattern(arm.pattern);
                    if (!arm.guard.isNone()) {
                        try self.printf(" if ", .{});
                        try self.printExpr(arm.guard.unwrap());
                    }
                    try self.printf(" => ", .{});
                    try self.printExpr(arm.body);
                    self.indent -= 4;
                }
                try self.newline();
                try self.printf("}}", .{});
            },
            .Break => {
                const node = self.exprs.get(.Break, id);
                try self.printf("break", .{});
                if (!node.label.isNone()) try self.printf(" :{s}", .{self.s(node.label.unwrap())});
                if (!node.value.isNone()) {
                    try self.printf(" ", .{});
                    try self.printExpr(node.value.unwrap());
                }
            },
            .Continue => {
                _ = self.exprs.get(.Continue, id);
                try self.printf("continue", .{});
            },
            .Unreachable => {
                _ = self.exprs.get(.Unreachable, id);
                try self.printf("unreachable", .{});
            },
            .Null => {
                _ = self.exprs.get(.Null, id);
                try self.printf("null", .{});
            },
            .Undefined => {
                _ = self.exprs.get(.Undefined, id);
                try self.printf("undefined", .{});
            },
            .Defer => {
                const node = self.exprs.get(.Defer, id);
                try self.printf("defer ", .{});
                try self.printExpr(node.expr);
            },
            .ErrDefer => {
                const node = self.exprs.get(.ErrDefer, id);
                try self.printf("errdefer ", .{});
                try self.printExpr(node.expr);
            },
            .ErrUnwrap => {
                const node = self.exprs.get(.ErrUnwrap, id);
                try self.printExpr(node.expr);
                try self.printf("!", .{});
            },
            .OptionalUnwrap => {
                const node = self.exprs.get(.OptionalUnwrap, id);
                try self.printExpr(node.expr);
                try self.printf("?", .{});
            },
            .Await => {
                const node = self.exprs.get(.Await, id);
                try self.printExpr(node.expr);
                try self.printf(".await", .{});
            },
            .Closure => {
                const node = self.exprs.get(.Closure, id);
                try self.printf("|", .{});
                try self.printParams(node.params, false, false);
                try self.printf("|", .{});
                if (!node.result_ty.isNone()) {
                    try self.printf(" ", .{});
                    try self.printExpr(node.result_ty.unwrap());
                }
                try self.printf(" ", .{});
                try self.printExpr(node.body);
            },
            .Async => {
                const node = self.exprs.get(.Async, id);
                try self.printf("async ", .{});
                try self.printExpr(node.body);
            },
            .Cast => {
                const node = self.exprs.get(.Cast, id);
                try self.printExpr(node.expr);
                switch (node.kind) {
                    .normal => {
                        try self.printf(".(", .{});
                        try self.printExpr(node.ty);
                        try self.printf(")", .{});
                    },
                    .bitcast => {
                        try self.printf(".^", .{});
                        try self.printExpr(node.ty);
                    },
                    .wrap => {
                        try self.printf(".%", .{});
                        try self.printExpr(node.ty);
                    },
                    .saturate => {
                        try self.printf(".|", .{});
                        try self.printExpr(node.ty);
                    },
                    .checked => {
                        try self.printf(".?", .{});
                        try self.printExpr(node.ty);
                    },
                }
            },
            .Catch => {
                const node = self.exprs.get(.Catch, id);
                try self.printExpr(node.expr);
                try self.printf(" catch ", .{});
                if (!node.binding_name.isNone()) {
                    try self.printf("|{s}| ", .{self.s(node.binding_name.unwrap())});
                }
                try self.printExpr(node.handler);
            },
            .Import => {
                const node = self.exprs.get(.Import, id);
                try self.printf("import \"{s}\"", .{self.s(node.path)});
            },
            .TypeOf => {
                const node = self.exprs.get(.TypeOf, id);
                try self.printf("typeof(", .{});
                try self.printExpr(node.expr);
                try self.printf(")", .{});
            },
            .ArrayType => {
                const node = self.exprs.get(.ArrayType, id);
                try self.printf("[", .{});
                try self.printExpr(node.size);
                try self.printf("]", .{});
                try self.printExpr(node.elem);
            },
            .DynArrayType => {
                const node = self.exprs.get(.DynArrayType, id);
                try self.printf("[dyn]", .{});
                try self.printExpr(node.elem);
            },
            .MapType => {
                const node = self.exprs.get(.MapType, id);
                try self.printf("[", .{});
                try self.printExpr(node.key);
                try self.printf(": ", .{});
                try self.printExpr(node.value);
                try self.printf("]", .{});
            },
            .SliceType => {
                const node = self.exprs.get(.SliceType, id);
                try self.printf("[]", .{});
                if (node.is_const) try self.printf("const ", .{});
                try self.printExpr(node.elem);
            },
            .OptionalType => {
                const node = self.exprs.get(.OptionalType, id);
                try self.printf("?", .{});
                try self.printExpr(node.elem);
            },
            .ErrorSetType => {
                const node = self.exprs.get(.ErrorSetType, id);
                try self.printExpr(node.err);
                try self.printf("!", .{});
                try self.printExpr(node.value);
            },
            .StructType => {
                const node = self.exprs.get(.StructType, id);
                try self.printAttrs(node.attrs, .Before);
                if (node.is_extern) try self.printf("extern ", .{});
                try self.printf("struct {{", .{});
                const fields = self.exprs.sfield_pool.slice(node.fields);
                if (node.trailing_field_comma and fields.len > 0) {
                    self.indent += 4;
                    for (fields) |fid| {
                        try self.newline();
                        try self.ws();
                        try self.printStructField(fid);
                        try self.printf(",", .{});
                    }
                    self.indent -= 4;
                    try self.newline();
                    try self.ws();
                } else if (fields.len > 0) {
                    for (fields, 0..) |fid, i| {
                        if (i > 0) try self.printf(", ", .{});
                        try self.printStructField(fid);
                    }
                }
                try self.printf("}}", .{});
            },
            .EnumType => {
                const node = self.exprs.get(.EnumType, id);
                try self.printAttrs(node.attrs, .Before);
                if (node.is_extern) try self.printf("extern ", .{});
                try self.printf("enum", .{});
                if (!node.discriminant.isNone()) {
                    try self.printf("(", .{});
                    try self.printExpr(node.discriminant.unwrap());
                    try self.printf(")", .{});
                }
                try self.printf(" {{", .{});
                const fields = self.exprs.efield_pool.slice(node.fields);
                if (node.trailing_field_comma and fields.len > 0) {
                    self.indent += 4;
                    for (fields) |eid| {
                        const field = self.exprs.EnumField.get(eid);
                        try self.newline();
                        try self.ws();
                        try self.printAttrs(field.attrs, .Before);
                        try self.printf("{s}", .{self.s(field.name)});
                        if (!field.value.isNone()) {
                            try self.printf(" = ", .{});
                            try self.printExpr(field.value.unwrap());
                        }
                        try self.printf(",", .{});
                    }
                    self.indent -= 4;
                    try self.newline();
                    try self.ws();
                } else if (fields.len > 0) {
                    for (fields, 0..) |eid, i| {
                        if (i > 0) try self.printf(", ", .{});
                        const field = self.exprs.EnumField.get(eid);
                        try self.printAttrs(field.attrs, .Before);
                        try self.printf("{s}", .{self.s(field.name)});
                        if (!field.value.isNone()) {
                            try self.printf(" = ", .{});
                            try self.printExpr(field.value.unwrap());
                        }
                    }
                }
                try self.printf("}}", .{});
            },
            .VariantLikeType => {
                const node = self.exprs.get(.VariantLikeType, id);
                try self.printf("variant {{", .{});
                const fields = self.exprs.vfield_pool.slice(node.fields);
                if (node.trailing_field_comma and fields.len > 0) {
                    self.indent += 4;
                    for (fields) |fid| {
                        try self.newline();
                        try self.ws();
                        try self.printVariantField(fid);
                        try self.printf(",", .{});
                    }
                    self.indent -= 4;
                    try self.newline();
                    try self.ws();
                } else if (fields.len > 0) {
                    for (fields, 0..) |fid, i| {
                        if (i > 0) try self.printf(", ", .{});
                        try self.printVariantField(fid);
                    }
                }
                try self.printf("}}", .{});
            },
            .ErrorType => {
                const node = self.exprs.get(.ErrorType, id);
                try self.printf("error {{", .{});
                const fields = self.exprs.vfield_pool.slice(node.fields);
                if (node.trailing_field_comma and fields.len > 0) {
                    self.indent += 4;
                    for (fields) |fid| {
                        try self.newline();
                        try self.ws();
                        try self.printVariantField(fid);
                        try self.printf(",", .{});
                    }
                    self.indent -= 4;
                    try self.newline();
                    try self.ws();
                } else if (fields.len > 0) {
                    for (fields, 0..) |fid, i| {
                        if (i > 0) try self.printf(", ", .{});
                        try self.printVariantField(fid);
                    }
                }
                try self.printf("}}", .{});
            },
            .UnionType => {
                const node = self.exprs.get(.UnionType, id);
                try self.printAttrs(node.attrs, .Before);
                if (node.is_extern) try self.printf("extern ", .{});
                try self.printf("union {{", .{});
                const fields = self.exprs.sfield_pool.slice(node.fields);
                if (node.trailing_field_comma and fields.len > 0) {
                    self.indent += 4;
                    for (fields) |fid| {
                        try self.newline();
                        try self.ws();
                        try self.printStructField(fid);
                        try self.printf(",", .{});
                    }
                    self.indent -= 4;
                    try self.newline();
                    try self.ws();
                } else if (fields.len > 0) {
                    for (fields, 0..) |fid, i| {
                        if (i > 0) try self.printf(", ", .{});
                        try self.printStructField(fid);
                    }
                }
                try self.printf("}}", .{});
            },
            .PointerType => {
                const node = self.exprs.get(.PointerType, id);
                try self.printf("*", .{});
                if (node.is_const) try self.printf("const ", .{});
                try self.printExpr(node.elem);
            },
            .SimdType => {
                const node = self.exprs.get(.SimdType, id);
                try self.printf("simd(", .{});
                try self.printExpr(node.lanes);
                try self.printf(", ", .{});
                try self.printExpr(node.elem);
                try self.printf(")", .{});
            },
            .ComplexType => {
                const node = self.exprs.get(.ComplexType, id);
                try self.printf("complex(", .{});
                try self.printExpr(node.elem);
                try self.printf(")", .{});
            },
            .TensorType => {
                const node = self.exprs.get(.TensorType, id);
                try self.printf("tensor(", .{});
                const shape = self.exprs.expr_pool.slice(node.shape);
                for (shape, 0..) |si, i| {
                    if (i > 0) try self.printf(", ", .{});
                    try self.printExpr(si);
                }
                try self.printf(", ", .{});
                try self.printExpr(node.elem);
                try self.printf(")", .{});
            },
            .TypeType => {
                _ = self.exprs.get(.TypeType, id);
                try self.printf("type", .{});
            },
            .AnyType => {
                _ = self.exprs.get(.AnyType, id);
                try self.printf("any", .{});
            },
            .NoreturnType => {
                _ = self.exprs.get(.NoreturnType, id);
                try self.printf("noreturn", .{});
            },
        }
    }

    // ------------------------------------------------------------
    // Helpers for expressions / patterns
    // ------------------------------------------------------------
    fn printParams(self: *Formatter, r: cst.RangeOf(cst.ParamId), is_variadic: bool, trailing: bool) !void {
        _ = is_variadic;
        const params = self.exprs.param_pool.slice(r);
        if (trailing and params.len > 0) {
            self.indent += 4;
            for (params) |pid| {
                const param = self.exprs.Param.get(pid);
                try self.newline();
                try self.ws();
                try self.printAttrs(param.attrs, .After);
                if (param.is_comptime) {
                    try self.printf("comptime ", .{});
                }
                if (!param.pat.isNone()) {
                    try self.printExpr(param.pat.unwrap());
                }
                if (!param.pat.isNone() and !param.ty.isNone()) {
                    try self.printf(": ", .{});
                }
                if (!param.ty.isNone()) {
                    try self.printExpr(param.ty.unwrap());
                }
                if (!param.value.isNone()) {
                    try self.printf(" = ", .{});
                    try self.printExpr(param.value.unwrap());
                }
                try self.printf(",", .{});
            }
            self.indent -= 4;
            try self.newline();
            try self.ws();
            return;
        }

        for (params, 0..) |pid, i| {
            if (i > 0) try self.printf(", ", .{});
            const param = self.exprs.Param.get(pid);
            try self.printAttrs(param.attrs, .After);
            if (param.is_comptime) {
                try self.printf("comptime ", .{});
            }
            if (!param.pat.isNone()) {
                try self.printExpr(param.pat.unwrap());
            }
            if (!param.pat.isNone() and !param.ty.isNone()) {
                try self.printf(": ", .{});
            }
            if (!param.ty.isNone()) {
                try self.printExpr(param.ty.unwrap());
            }
            if (!param.value.isNone()) {
                try self.printf(" = ", .{});
                try self.printExpr(param.value.unwrap());
            }
        }
    }

    fn printStructField(self: *Formatter, id: cst.StructFieldId) !void {
        const field = self.exprs.StructField.get(id);
        try self.printAttrs(field.attrs, .Before);
        try self.printf("{s}: ", .{self.s(field.name)});
        try self.printExpr(field.ty);
        if (!field.value.isNone()) {
            try self.printf(" = ", .{});
            try self.printExpr(field.value.unwrap());
        }
    }

    fn printVariantField(self: *Formatter, id: cst.VariantFieldId) !void {
        const field = self.exprs.VariantField.get(id);
        try self.printAttrs(field.attrs, .Before);
        try self.printf("{s}", .{self.s(field.name)});
        switch (field.ty_tag) {
            .none => {},
            .Tuple => {
                const elems = self.exprs.expr_pool.slice(field.tuple_elems);
                if (field.tuple_trailing_comma and elems.len > 0) {
                    try self.printf("(", .{});
                    self.indent += 4;
                    for (elems) |eid| {
                        try self.newline();
                        try self.ws();
                        try self.printExpr(eid);
                        try self.printf(",", .{});
                    }
                    self.indent -= 4;
                    try self.newline();
                    try self.ws();
                    try self.printf(")", .{});
                } else {
                    try self.printf("(", .{});
                    try self.printExprs(field.tuple_elems, ", ");
                    try self.printf(")", .{});
                }
            },
            .Struct => {
                const payload_fields = self.exprs.sfield_pool.slice(field.struct_fields);
                if (field.struct_trailing_comma and payload_fields.len > 0) {
                    try self.printf(" {{", .{});
                    self.indent += 4;
                    for (payload_fields) |fid| {
                        try self.newline();
                        try self.ws();
                        try self.printStructField(fid);
                        try self.printf(",", .{});
                    }
                    self.indent -= 4;
                    try self.newline();
                    try self.ws();
                    try self.printf("}}", .{});
                } else {
                    try self.printf(" {{", .{});
                    for (payload_fields, 0..) |fid, i| {
                        if (i > 0) try self.printf(", ", .{});
                        try self.printStructField(fid);
                    }
                    try self.printf("}}", .{});
                }
            },
        }
        if (!field.value.isNone()) {
            try self.printf(" = ", .{});
            try self.printExpr(field.value.unwrap());
        }
    }

    fn printExprs(self: *Formatter, r: cst.RangeOf(cst.ExprId), sep: []const u8) !void {
        const ids = self.exprs.expr_pool.slice(r);
        for (ids, 0..) |eid, i| {
            if (i > 0) try self.printf("{s}", .{sep});
            try self.printExpr(eid);
        }
    }

    const AttrPos = enum { Before, After };
    fn printAttrs(self: *Formatter, opt_r: cst.OptRangeAttr, pos: AttrPos) anyerror!void {
        if (opt_r.isNone()) return;
        const r = opt_r.asRange();
        const attrs = self.exprs.attr_pool.slice(r);
        if (attrs.len == 0) return;

        try self.printf("@[", .{});
        for (attrs, 0..) |aid, i| {
            if (i > 0) try self.printf(", ", .{});
            const attr = self.exprs.Attribute.get(aid);
            try self.ws();
            try self.printf("{s}", .{self.s(attr.name)});
            if (!attr.value.isNone()) {
                try self.printf(" = ", .{});
                try self.printExpr(attr.value.unwrap());
            }
            _ = pos;
        }
        try self.printf("] ", .{});
    }

    // ------------------------------------------------------------
    // Patterns
    // ------------------------------------------------------------
    fn printPattern(self: *Formatter, id: cst.PatternId) anyerror!void {
        const kind = self.pats.index.kinds.items[id.toRaw()];
        switch (kind) {
            .Wildcard => try self.printf("_", .{}),
            .Literal => {
                const node = self.pats.get(.Literal, id);
                try self.printExpr(node.expr);
            },
            .Path => {
                const node = self.pats.get(.Path, id);
                const segs = self.pats.seg_pool.slice(node.segments);
                for (segs, 0..) |sid, i| {
                    if (i > 0) try self.printf(".", .{});
                    const seg = self.pats.PathSeg.get(sid);
                    try self.printf("{s}", .{self.s(seg.name)});
                }
            },
            .Binding => {
                const node = self.pats.get(.Binding, id);
                if (node.by_ref) try self.printf("ref ", .{});
                if (node.is_mut) try self.printf("mut ", .{});
                try self.printf("{s}", .{self.s(node.name)});
            },
            .Tuple => {
                const node = self.pats.get(.Tuple, id);
                try self.printf("(", .{});
                const elems = self.pats.pat_pool.slice(node.elems);
                for (elems, 0..) |pid, i| {
                    if (i > 0) try self.printf(", ", .{});
                    try self.printPattern(pid);
                }
                try self.printf(")", .{});
            },
            .Slice => {
                const node = self.pats.get(.Slice, id);
                try self.printf("[", .{});
                const elems = self.pats.pat_pool.slice(node.elems);
                for (elems, 0..) |pid, i| {
                    if (i > 0) try self.printf(", ", .{});
                    if (node.has_rest and node.rest_index == i) {
                        try self.printf("..", .{});
                        if (!node.rest_binding.isNone()) {
                            try self.printPattern(node.rest_binding.unwrap());
                        }
                        if (i < elems.len) try self.printf(", ", .{});
                    }
                    try self.printPattern(pid);
                }
                try self.printf("]", .{});
            },
            .Struct => {
                const node = self.pats.get(.Struct, id);
                try self.printPatternPath(node.path);
                try self.printf(" {{", .{});
                const fields = self.pats.field_pool.slice(node.fields);
                for (fields, 0..) |fid, i| {
                    if (i > 0) try self.printf(", ", .{});
                    try self.printPatternField(fid);
                }
                if (node.has_rest) {
                    if (fields.len > 0) try self.printf(", ", .{});
                    try self.printf("..", .{});
                }
                try self.printf("}}", .{});
            },
            .VariantTuple => {
                const node = self.pats.get(.VariantTuple, id);
                try self.printPatternPath(node.path);
                try self.printf("(", .{});
                const elems = self.pats.pat_pool.slice(node.elems);
                for (elems, 0..) |pid, i| {
                    if (i > 0) try self.printf(", ", .{});
                    try self.printPattern(pid);
                }
                try self.printf(")", .{});
            },
            .VariantStruct => {
                const node = self.pats.get(.VariantStruct, id);
                try self.printPatternPath(node.path);
                try self.printf(" {{", .{});
                const fields = self.pats.field_pool.slice(node.fields);
                for (fields, 0..) |fid, i| {
                    if (i > 0) try self.printf(", ", .{});
                    try self.printPatternField(fid);
                }
                if (node.has_rest) {
                    if (fields.len > 0) try self.printf(", ", .{});
                    try self.printf("..", .{});
                }
                try self.printf("}}", .{});
            },
            .Range => {
                const node = self.pats.get(.Range, id);
                if (!node.start.isNone()) try self.printExpr(node.start.unwrap());
                if (node.inclusive_right) {
                    try self.printf("..=", .{});
                } else {
                    try self.printf("..", .{});
                }
                if (!node.end.isNone()) try self.printExpr(node.end.unwrap());
            },
            .Or => {
                const node = self.pats.get(.Or, id);
                const alts = self.pats.pat_pool.slice(node.alts);
                for (alts, 0..) |pid, i| {
                    if (i > 0) try self.printf(" | ", .{});
                    try self.printPattern(pid);
                }
            },
            .At => {
                const node = self.pats.get(.At, id);
                try self.printf("{s} @ ", .{self.s(node.binder)});
                try self.printPattern(node.pattern);
            },
        }
    }

    fn printPatternPath(self: *Formatter, path: cst.RangeOf(cst.PathSegId)) !void {
        const segs = self.pats.seg_pool.slice(path);
        for (segs, 0..) |sid, i| {
            if (i > 0) try self.printf(".", .{});
            const seg = self.pats.PathSeg.get(sid);
            try self.printf("{s}", .{self.s(seg.name)});
        }
    }

    fn printPatternField(self: *Formatter, id: cst.PatFieldId) !void {
        const field = self.pats.StructField.get(id);
        try self.printf("{s}: ", .{self.s(field.name)});
        try self.printPattern(field.pattern);
    }
};

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
