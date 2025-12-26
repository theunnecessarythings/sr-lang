const std = @import("std");
const Lexer = @import("lexer.zig").Tokenizer;
const Token = @import("lexer.zig").Token;
const Loc = Token.Loc;
const cst = @import("cst.zig");
const compile = @import("compile.zig");
const diag = @import("diagnostics.zig");
const List = std.ArrayList;

pub const Parser = @This();

/// Allocator used for CST storage, interner operations, and diagnostics.
gpa: std.mem.Allocator,
/// Source buffer currently parsed.
src: []const u8,
/// Tokenizer instance producing lexical tokens.
lex: Lexer,
/// Current token being consumed.
cur: Token,
/// Lookahead token.
nxt: Token,
/// Counter used to synthesize unique names for `test` declarations.
test_counter: usize = 0,

/// CST being built/returned to the caller.
cst_u: cst.CST,
/// Shared compilation context for access to interner/locations.
context: *compile.Context,
/// Diagnostic sink for parser errors, warnings, notes.
diags: *diag.Diagnostics,

/// Contextual parsing mode for Pratt table recursion (expressions vs type expressions).
const ParseMode = enum { expr, type, expr_no_struct };

// ---------- lifecycle ----------
/// Build a parser that will lex `source` associated with `file_id`, wiring diagnostics/context.
pub fn init(
    gpa: std.mem.Allocator,
    source: [:0]const u8,
    file_id: u32,
    diags: *diag.Diagnostics,
    context: *compile.Context,
) Parser {
    var parser = Parser{
        .gpa = gpa,
        .src = source,
        .lex = .init(source, file_id, .semi),
        .cur = undefined,
        .nxt = undefined,
        .context = context,
        .diags = diags,
        .cst_u = .init(gpa, context.interner, context.loc_store),
    };
    parser.cur = parser.fetchNext();
    parser.nxt = parser.fetchNext();
    return parser;
}

// ---------- entry ----------
/// Parse the entire source file and return the constructed CST (or error).
pub fn parse(self: *Parser) !cst.CST {
    try self.parseProgram();
    return self.cst_u;
}

//=================================================================
// Utilities
// =================================================================
/// Move `cur`/`nxt` forward by consuming the current token.
inline fn advance(self: *Parser) void {
    self.cur = self.nxt;
    self.nxt = self.fetchNext();
}
/// If the current token matches `tag`, consume it and return true.
inline fn consumeIf(self: *Parser, tag: Token.Tag) bool {
    if (self.cur.tag != tag) return false;
    self.advance();
    return true;
}
/// Demand that the current token is `tag`, otherwise emit an error.
inline fn expect(self: *Parser, tag: Token.Tag) !void {
    if (self.cur.tag != tag) {
        self.errorNote(
            self.cur.loc,
            .unexpected_token,
            .{ tag, self.cur.tag },
            self.cur.loc,
            .token_cannot_start_expression,
        );
        return error.UnexpectedToken;
    }
    self.advance();
}
/// Return the source slice representing `token`.
inline fn slice(self: *const Parser, token: Token) []const u8 {
    return self.src[token.loc.start..token.loc.end];
}
/// Return true when `tag` corresponds to a comment/literature node.
fn isComment(tag: Token.Tag) bool {
    return switch (tag) {
        .line_comment, .block_comment, .doc_comment, .container_doc_comment => true,
        else => false,
    };
}
/// Record the comment `tok` into the CST's comment list.
fn recordComment(self: *Parser, tok: Token) void {
    const kind = switch (tok.tag) {
        .line_comment => cst.CommentKind.line,
        .block_comment => cst.CommentKind.block,
        .doc_comment => cst.CommentKind.doc,
        .container_doc_comment => cst.CommentKind.container_doc,
        else => unreachable,
    };
    _ = self.cst_u.comments.add(self.gpa, .{ .kind = kind, .loc = self.toLocId(tok.loc) });
}
/// Fetch the next non-comment token from the lexer.
fn fetchNext(self: *Parser) Token {
    var tok = self.lex.next();
    while (true) {
        if (!isComment(tok.tag)) return tok;
        self.recordComment(tok);
        tok = self.lex.next();
    }
}
/// Intern `bytes` as an identifier string for the CST.
fn intern(self: *Parser, bytes: []const u8) cst.StrId {
    return self.cst_u.exprs.strs.intern(bytes);
}
/// Convert a token location into the CST module's `LocId`.
fn toLocId(self: *Parser, tl: Token.Loc) cst.LocId {
    return self.cst_u.exprs.locs.add(self.gpa, tl);
}

//=================================================================
// Diagnostics helpers
//=================================================================
/// Emit `error_code` at `loc` and attach `note_code` as a follow-up note.
inline fn errorNote(
    self: *Parser,
    loc: Loc,
    comptime error_code: diag.DiagnosticCode,
    args: anytype,
    note_loc: ?Loc,
    comptime note_code: diag.NoteCode,
) void {
    const before = self.diags.count();
    _ = self.diags.addError(loc, error_code, args) catch {};
    if (self.diags.count() > before) {
        const idx = self.diags.count() - 1;
        _ = self.diags.attachNote(idx, note_loc, note_code) catch {};
    }
}

/// Return true when current token can end a statement.
inline fn isStmtTerminator(self: *const Parser) bool {
    return switch (self.cur.tag) {
        .eos, .rcurly, .eof => true,
        else => false,
    };
}
/// Returns true when the current identifier is the `_` discard token.
inline fn isUnderscore(self: *const Parser) bool {
    return self.cur.tag == .identifier and std.mem.eql(u8, self.slice(self.cur), "_");
}
/// Expect the keyword `tag` followed by `(` and return the location of the keyword.
inline fn beginKeywordParen(self: *Parser, comptime tag: Token.Tag) !Loc {
    const start = self.cur.loc;
    try self.expect(tag);
    try self.expect(.lparen);
    return start;
}
/// Expect a closing parenthesis, emitting diagnostics on mismatch.
inline fn endParen(self: *Parser) !void {
    try self.expect(.rparen);
}
/// Expect `{` and return its start location.
inline fn beginBrace(self: *Parser) !Loc {
    const start = self.cur.loc;
    try self.expect(.lcurly);
    return start;
}
/// Consume `}` and return the token it replaced.
inline fn endBrace(self: *Parser) !Loc {
    const tok = self.cur;
    try self.expect(.rcurly);
    return tok.loc;
}
/// Return true if `tag` denotes a literal token.
inline fn isLiteralTag(_: *const Parser, tag: Token.Tag) bool {
    return switch (tag) {
        .char_literal, .string_literal, .raw_string_literal, .raw_asm_block => true,
        .integer_literal, .float_literal, .imaginary_literal, .keyword_true, .keyword_false => true,
        else => false,
    };
}
/// Determine whether `expr_id` stores an integer literal (used during numeric parsing).
inline fn exprIsIntegerLiteral(self: *Parser, expr_id: cst.ExprId) bool {
    const kind = self.cst_u.kind(expr_id);
    if (kind != .Literal) return false;
    const lit = self.cst_u.exprs.get(.Literal, expr_id);
    return lit.tag_small == litTag(.integer_literal);
}
/// Return true if the lookahead token can terminate a list or expression.
inline fn nextIsTerminator(self: *const Parser) bool {
    return isTerminator(self, self.nxt.tag);
}
/// Add a CST expression node of `kind` and return its ID.
inline fn addExpr(self: *Parser, comptime kind: cst.ExprKind, value: cst.RowT(kind)) cst.ExprId {
    return self.cst_u.exprs.add(kind, value);
}
/// Add a CST pattern node of `kind` and return its ID.
inline fn addPat(self: *Parser, comptime kind: cst.PatternKind, value: cst.PatRowT(kind)) cst.PatternId {
    return self.cst_u.pats.add(kind, value);
}

// ===============================================================
// Pratt tables / token helpers
// ===============================================================
/// Return true when token `t` represents a literal in the Pratt table.
fn isLiteral(_: *const Parser, t: Token.Tag) bool {
    return switch (t) {
        .char_literal, .string_literal, .raw_string_literal, .integer_literal, .float_literal, .imaginary_literal, .keyword_true, .keyword_false => true,
        else => false,
    };
}
/// Convert a token literal tag into the CST literal kind.
fn litTag(t: Token.Tag) cst.LiteralKind {
    return switch (t) {
        .integer_literal => .int,
        .float_literal => .float,
        .string_literal => .string,
        .raw_string_literal => .raw_string,
        .char_literal => .char,
        .imaginary_literal => .imaginary,
        .keyword_true => .true,
        .keyword_false => .false,
        else => unreachable,
    };
}

const prefix_bp_table = std.enums.directEnumArrayDefault(Token.Tag, u8, 0, 0, .{
    .plus = 90,
    .minus = 90,
    .b_and = 90,
    .bang = 90,
    .dotdot = 90,
    .dotdoteq = 90,
});
const postfix_bp_table = std.enums.directEnumArrayDefault(Token.Tag, ?u8, @as(?u8, null), 0, .{
    .lparen = 95,
    .lsquare = 95,
    .lcurly = 95,
    .dot = 95,
    .dotlparen = 95,
    .dotdot = 95,
    .dotstar = 95,
    .dotdoteq = 95,
    .bang = 95,
    .question = 95,
    // Make `catch` bind looser than `orelse` so `a orelse b catch c`
    // parses as `(a orelse b) catch c` instead of `a orelse (b catch c)`.
    .keyword_catch = 10,
});
const infix_bp_table = std.enums.directEnumArrayDefault(
    Token.Tag,
    ?struct { u8, u8 },
    @as(?struct { u8, u8 }, null),
    0,
    .{
        .star = .{ 80, 81 },
        .slash = .{ 80, 81 },
        .percent = .{ 80, 81 },
        .star_pipe = .{ 80, 81 },
        .star_percent = .{ 80, 81 },
        .plus = .{ 70, 71 },
        .plus_pipe = .{ 70, 71 },
        .plus_percent = .{ 70, 71 },
        .minus = .{ 70, 71 },
        .minus_percent = .{ 70, 71 },
        .minus_pipe = .{ 70, 71 },
        .ltlt = .{ 60, 61 },
        .gtgt = .{ 60, 61 },
        .shl_pipe = .{ 60, 61 },
        .less_than = .{ 50, 51 },
        .less_equal = .{ 50, 51 },
        .greater_than = .{ 50, 51 },
        .greater_equal = .{ 50, 51 },
        .equal_equal = .{ 45, 46 },
        .not_equal = .{ 45, 46 },
        .keyword_in = .{ 42, 43 },
        .b_and = .{ 40, 41 },
        .caret = .{ 35, 36 },
        .b_or = .{ 30, 31 },
        .dotdot = .{ 27, 28 },
        .dotdoteq = .{ 27, 28 },
        .keyword_and = .{ 25, 26 },
        .keyword_or = .{ 20, 21 },
        .bang = .{ 15, 16 }, // for error union
        .keyword_orelse = .{ 12, 11 },
        // do not treat 'catch' as an infix operator; it's a postfix form with optional binder
        .plus_equal = .{ 10, 9 },
        .minus_equal = .{ 10, 9 },
        .star_equal = .{ 10, 9 },
        .slash_equal = .{ 10, 9 },
        .percent_equal = .{ 10, 9 },
        .shl_equal = .{ 10, 9 },
        .shr_equal = .{ 10, 9 },
        .and_equal = .{ 10, 9 },
        .or_equal = .{ 10, 9 },
        .caret_equal = .{ 10, 9 },
        .star_pipe_equal = .{ 10, 9 },
        .plus_pipe_equal = .{ 10, 9 },
        .minus_pipe_equal = .{ 10, 9 },
        .shl_pipe_equal = .{ 10, 9 },
        .star_percent_equal = .{ 10, 9 },
        .plus_percent_equal = .{ 10, 9 },
        .minus_percent_equal = .{ 10, 9 },
    },
);

/// Return true if `tag` can begin a type expression (generic, builtin, pointer, etc.).
fn isTypeStart(_: *const Parser, tag: Token.Tag) bool {
    return switch (tag) {
        .identifier,
        .raw_identifier,
        .star,
        .question,
        .lsquare,
        .lparen,
        .keyword_any,
        .keyword_type,
        .keyword_noreturn,
        .keyword_struct,
        .keyword_union,
        .keyword_enum,
        .keyword_variant,
        .keyword_error,
        .keyword_simd,
        .keyword_tensor,
        .keyword_proc,
        .keyword_fn,
        => true,
        else => false,
    };
}

/// Map a punctuator token `t` into the corresponding CST prefix operator.
fn toPrefixOp(_: *const Parser, t: Token.Tag) cst.PrefixOp {
    return switch (t) {
        .plus => .plus,
        .minus => .minus,
        .b_and => .address_of,
        .bang => .logical_not,
        .dotdot => .range,
        .dotdoteq => .range_inclusive,
        else => unreachable,
    };
}
/// Map token `tag` into the corresponding CST infix operator enum.
inline fn toInfixOp(_: *const Parser, tag: Token.Tag) cst.InfixOp {
    return switch (tag) {
        .plus => .add,
        .minus => .sub,
        .star => .mul,
        .slash => .div,
        .percent => .mod,
        .ltlt => .shl,
        .gtgt => .shr,
        .star_pipe => .mul_sat,
        .plus_pipe => .add_sat,
        .minus_pipe => .sub_sat,
        .shl_pipe => .shl_sat,
        .star_percent => .mul_wrap,
        .plus_percent => .add_wrap,
        .minus_percent => .sub_wrap,
        .less_than => .lt,
        .less_equal => .lte,
        .greater_than => .gt,
        .greater_equal => .gte,
        .equal_equal => .eq,
        .not_equal => .neq,
        .b_and => .b_and,
        .caret => .b_xor,
        .b_or => .b_or,
        .keyword_in => .contains,
        .keyword_and => .logical_and,
        .keyword_or => .logical_or,
        .dotdot => .range,
        .dotdoteq => .range_inclusive,
        .plus_equal => .add_assign,
        .minus_equal => .sub_assign,
        .star_equal => .mul_assign,
        .slash_equal => .div_assign,
        .percent_equal => .mod_assign,
        .shl_equal => .shl_assign,
        .shr_equal => .shr_assign,
        .and_equal => .and_assign,
        .or_equal => .or_assign,
        .caret_equal => .xor_assign,
        .star_pipe_equal => .mul_sat_assign,
        .plus_pipe_equal => .add_sat_assign,
        .minus_pipe_equal => .sub_sat_assign,
        .shl_pipe_equal => .shl_sat_assign,
        .star_percent_equal => .mul_wrap_assign,
        .plus_percent_equal => .add_wrap_assign,
        .minus_percent_equal => .sub_wrap_assign,
        .bang => .error_union,
        .keyword_orelse => .unwrap_orelse,
        else => unreachable,
    };
}

/// Return true when `t` terminates an expression or declaration.
fn isTerminator(_: *const Parser, t: Token.Tag) bool {
    return switch (t) {
        .comma, .rsquare, .rparen, .rcurly, .eos, .eof => true,
        else => false,
    };
}

/// Convenience helper to fetch the row data of `id` when its kind is `kind`.
inline fn exprGet(self: *Parser, comptime kind: cst.ExprKind, id: cst.ExprId) cst.RowT(kind) {
    return self.cst_u.exprs.get(kind, id);
}

/// Determine whether expression `id` resembles a constructor head (ident/field chain).
fn looksLikeCtorHead(self: *Parser, id: cst.ExprId) bool {
    const kind = self.cst_u.kind(id);
    return switch (kind) {
        .Ident, .FieldAccess => true,
        .Call => self.looksLikeCtorHead(self.exprGet(.Call, id).callee),
        .IndexAccess => self.looksLikeCtorHead(self.exprGet(.IndexAccess, id).collection),
        .Tuple => blk: {
            const t = self.exprGet(.Tuple, id);
            if (t.elems.len != 1) break :blk false;
            const only = self.cst_u.exprs.expr_pool.slice(t.elems)[0];
            break :blk self.looksLikeCtorHead(only);
        },
        else => false,
    };
}

//=================================================================
// Parsing
//=================================================================
/// Fast-forward to the next occurrence of `tag`, used for error recovery.
fn sync(self: *Parser, comptime tag: Token.Tag) void {
    while (self.cur.tag != tag and self.cur.tag != .eof) {
        self.advance();
    }
    if (self.cur.tag == tag) self.advance();
}

/// Parse top-level declarations until end-of-stream, populating the CST.
/// Parse top-level declarations until EOF, recording package metadata.
fn parseProgram(self: *Parser) !void {
    var decls: List(cst.DeclId) = .empty;
    defer decls.deinit(self.gpa);
    const default_pkg = self.intern("main");

    // Optional package declaration
    if (self.cur.tag == .keyword_package) {
        const start = self.cur.loc;
        self.advance(); // "package"
        const name_tok = self.cur;
        try self.expect(.identifier);
        const pkg_name = self.intern(self.slice(name_tok));
        try self.expect(.eos);
        self.cst_u.program.package_name = .some(pkg_name);
        self.cst_u.program.package_loc = .some(self.toLocId(start));
    } else {
        // default package, set to "main"
        self.cst_u.program.package_name = .some(default_pkg);
        self.cst_u.program.package_loc = .some(self.toLocId(self.cur.loc));
    }

    // Top-level declarations
    while (self.cur.tag != .eof) {
        const decl = self.parseDecl() catch |e| {
            // self.sync(.eos);
            if (e == error.UnexpectedToken) continue else return e;
        };
        try decls.append(self.gpa, decl);
    }
    const range = self.cst_u.exprs.decl_pool.pushMany(self.gpa, decls.items);
    self.cst_u.program.top_decls = range;
}

/// Parse a declaration (function, const, import, etc.) and return its CST id.
fn parseDecl(self: *Parser) anyerror!cst.DeclId {
    if (self.cur.tag == .keyword_test) return self.parseTestDecl();

    const loc = self.toLocId(self.cur.loc);
    const lhs_or_rhs = try self.parseExpr(0, .expr);
    var flags: cst.Rows.DeclFlags = .{ .is_const = false, .is_assign = false };
    var ty_opt: cst.OptExprId = .none();
    var lhs_opt: cst.OptExprId = .none();
    var rhs_id = lhs_or_rhs;
    var method_path: cst.OptRangeMethodPathSeg = .none();
    const finishStmt = struct {
        fn call(p: *Parser) !void {
            if (p.cur.tag == .eos) {
                p.advance();
            } else if (p.cur.tag != .rcurly and p.cur.tag != .eof) {
                try p.expect(.eos);
            }
        }
    }.call;

    switch (self.cur.tag) {
        .coloncolon => { // constant: x :: (type)? (= rhs)?
            self.advance();
            flags.is_const = true;
            rhs_id = try self.parseExpr(0, .expr);
            try finishStmt(self);
            lhs_opt = .some(lhs_or_rhs);
        },
        .coloneq => { // x := rhs
            self.advance();
            rhs_id = try self.parseExpr(0, .expr);
            try finishStmt(self);
            lhs_opt = .some(lhs_or_rhs);
        },
        .colon => { // x : T (=|::) rhs

            self.advance();
            const ty_id = try self.parseExpr(0, .type);
            ty_opt = .some(ty_id);
            switch (self.cur.tag) {
                .equal => {
                    self.advance();
                    rhs_id = try self.parseExpr(0, .expr);
                    try finishStmt(self);
                    lhs_opt = .some(lhs_or_rhs);
                },
                .colon => {
                    self.advance();
                    flags.is_const = true;
                    rhs_id = try self.parseExpr(0, .expr);
                    try finishStmt(self);
                    lhs_opt = .some(lhs_or_rhs);
                },
                .eos, .rcurly, .eof => {
                    // Allow type-only declaration: synthesize 'undefined' initializer
                    // to let later phases run and diagnose type issues (e.g., array size).
                    _ = self.consumeIf(.eos);
                    const u_loc = self.toLocId(self.cur.loc);
                    const undef_id = self.addExpr(.Undefined, .{ .loc = u_loc });
                    rhs_id = undef_id;
                    lhs_opt = .some(lhs_or_rhs);
                },
                else => {
                    self.errorNote(self.cur.loc, .expected_type_in_declaration, .{self.cur.tag}, self.cur.loc, .did_you_mean_equal);
                    self.sync(.eos);
                    return error.UnexpectedToken;
                },
            }
        },
        .equal => { // x = rhs (assignment; LHS may be lvalue expression)
            self.advance();
            flags.is_assign = true;
            rhs_id = try self.parseExpr(0, .expr);
            try finishStmt(self);
            lhs_opt = .some(lhs_or_rhs);
        },
        .eos, .rcurly, .eof => {
            // expression statement: treat as decl { lhs: none, rhs: expr }
            _ = self.consumeIf(.eos);
        },
        else => {
            // expression statement w/o terminator: still accept; caller may sync
        },
    }

    if (flags.is_const and !lhs_opt.isNone()) {
        method_path = try self.tryMethodPath(lhs_opt.unwrap());
    }

    return self.cst_u.exprs.addDeclRow(.{
        .lhs = lhs_opt,
        .rhs = rhs_id,
        .ty = ty_opt,
        .method_path = method_path,
        .flags = flags,
        .loc = loc,
    });
}

/// Parse a `test "name" { ... }` declaration by desugaring into a const procedure with a test attribute.
fn parseTestDecl(self: *Parser) anyerror!cst.DeclId {
    const start_loc = self.cur.loc;
    self.advance(); // consume 'test'

    const name_tok = self.cur;
    const name_tag = name_tok.tag;
    if (name_tag != .string_literal and name_tag != .raw_string_literal) {
        try self.expect(.string_literal); // emits diagnostic
        return error.UnexpectedToken;
    }

    const name_loc = self.toLocId(name_tok.loc);
    const name_str = self.slice(name_tok);
    const lit_id = self.addExpr(.Literal, .{
        .value = self.intern(name_str),
        .tag_small = litTag(name_tag),
        .loc = name_loc,
    });
    self.advance();

    // Build @[test="name"] attribute list.
    const test_attr_name = self.intern("test");
    const attr_id = self.cst_u.exprs.addAttrRow(.{
        .name = test_attr_name,
        .value = .some(lit_id),
        .loc = name_loc,
    });
    const attr_range = self.cst_u.exprs.attr_pool.pushMany(self.gpa, &[_]cst.AttributeId{attr_id});

    // Require a block body.
    const body_expr = try self.parseBlockExpr();

    // Result type: Error!void
    const err_ident = self.addExpr(.Ident, .{
        .name = self.intern("Error"),
        .loc = self.toLocId(start_loc),
    });
    const void_ident = self.addExpr(.Ident, .{
        .name = self.intern("void"),
        .loc = self.toLocId(start_loc),
    });
    const result_ty = self.addExpr(.Infix, .{
        .op = .error_union,
        .left = err_ident,
        .right = void_ident,
        .loc = self.toLocId(start_loc),
    });

    // Synthesize a unique identifier to bind the test procedure.
    const idx = self.test_counter;
    self.test_counter += 1;
    var name_buf: [48]u8 = undefined;
    const sym_name = std.fmt.bufPrint(&name_buf, "__test_{d}_{d}", .{ self.lex.file_id, idx }) catch unreachable;
    const lhs_ident = self.addExpr(.Ident, .{ .name = self.intern(sym_name), .loc = self.toLocId(start_loc) });

    const fn_id = self.addExpr(.Function, .{
        .params = cst.RangeOf(cst.ParamId).empty(),
        .result_ty = .some(result_ty),
        .body = .some(body_expr),
        .raw_asm = .none(),
        .attrs = .some(attr_range),
        .flags = .{ .is_proc = true, .is_async = false, .is_variadic = false, .is_extern = false, .is_test = true },
        .trailing_param_comma = false,
        .loc = self.toLocId(start_loc),
    });

    // Consume optional semicolon after the block, mirroring normal decl handling.
    if (self.cur.tag == .eos) {
        self.advance();
    } else if (self.cur.tag != .rcurly and self.cur.tag != .eof) {
        try self.expect(.eos);
    }

    const row: cst.Rows.Decl = .{
        .lhs = .some(lhs_ident),
        .rhs = fn_id,
        .ty = .none(),
        .method_path = .none(),
        .flags = .{ .is_const = true, .is_assign = false },
        .loc = self.toLocId(start_loc),
    };
    return self.cst_u.exprs.addDeclRow(row);
}

/// Attempt to extract a method path from `lhs_expr`, returning optional range.
fn tryMethodPath(self: *Parser, lhs_expr: cst.ExprId) !cst.OptRangeMethodPathSeg {
    var segs: List(cst.Rows.MethodPathSeg) = .empty;
    defer segs.deinit(self.gpa);

    const ok = try self.collectMethodPathSegments(lhs_expr, &segs);
    if (!ok or segs.items.len < 2) return cst.OptRangeMethodPathSeg.none();

    var ids = std.ArrayListUnmanaged(cst.MethodPathSegId){};
    defer ids.deinit(self.gpa);
    try ids.ensureTotalCapacity(self.gpa, segs.items.len);
    for (segs.items) |seg| {
        ids.appendAssumeCapacity(self.cst_u.exprs.addMethodPathSegRow(seg));
    }

    const range = self.cst_u.exprs.method_path_pool.pushMany(self.gpa, ids.items);
    return cst.OptRangeMethodPathSeg.some(range);
}

/// Collect the chain of identifiers composing `expr` for method resolution.
fn collectMethodPathSegments(
    self: *Parser,
    expr: cst.ExprId,
    segs: *List(cst.Rows.MethodPathSeg),
) anyerror!bool {
    const kind = self.cst_u.kind(expr);
    return switch (kind) {
        .Ident => blk: {
            const row = self.cst_u.exprs.get(.Ident, expr);
            try segs.append(self.gpa, .{ .name = row.name, .loc = row.loc });
            break :blk true;
        },
        .FieldAccess => blk: {
            const row = self.cst_u.exprs.get(.FieldAccess, expr);
            if (row.is_tuple) break :blk false;
            if (!try self.collectMethodPathSegments(row.parent, segs)) break :blk false;
            try segs.append(self.gpa, .{ .name = row.field, .loc = row.loc });
            break :blk true;
        },
        else => false,
    };
}

/// Parse prefix expressions (nud) driven by Pratt parsing rules.
fn nud(self: *Parser, tag: Token.Tag, comptime mode: ParseMode) anyerror!cst.ExprId {
    // -------- prefix operators --------
    switch (tag) {
        .plus, .minus, .b_and, .bang, .dotdot, .dotdoteq => {
            const loc = self.toLocId(self.cur.loc);
            const op = self.toPrefixOp(tag);
            self.advance();
            const rhs = try self.parseExpr(prefix_bp_table[@intFromEnum(tag)], mode);
            return self.addExpr(.Prefix, .{ .right = rhs, .op = op, .loc = loc });
        },
        .b_or => return try self.parseClosure(),
        .keyword_comptime => return try self.parseComptime(),
        .keyword_code => return try self.parseCodeBlock(),
        .keyword_mlir => return try self.parseMlir(),
        .keyword_insert => return try self.parseInsert(),
        else => {},
    }

    // -------- literals --------
    if (self.isLiteralTag(tag)) {
        const loc = self.toLocId(self.cur.loc);
        const value = self.intern(self.slice(self.cur));
        const tag_small = litTag(tag);
        self.advance();
        return self.addExpr(.Literal, .{ .value = value, .tag_small = tag_small, .loc = loc });
    }

    // -------- everything else --------
    return switch (tag) {
        // types (pointer/optional are unary)
        .star => try self.parsePointerType(),
        .question => try self.parseOptionalType(),
        .at => try self.parseAnnotated(mode),

        // name / primary
        .identifier, .raw_identifier => blk: {
            const loc = self.toLocId(self.cur.loc);
            const name = self.intern(self.slice(self.cur));
            self.advance();
            const next = self.nxt.tag;
            // Special case: labeled loop
            if (self.cur.tag == .colon and (next == .keyword_for or next == .keyword_while)) {
                self.advance();
                break :blk try self.parseLabeledLoop(.some(name));
            }
            break :blk self.addExpr(.Ident, .{ .name = name, .loc = loc });
        },

        // grouping / collections / blocks
        .lsquare => try self.parseArrayLike(mode),
        .lparen => try self.parseParenExpr(),
        .lcurly => try self.parseBlockExpr(),

        // functions / extern
        .keyword_proc, .keyword_fn => try self.parseFunctionLike(self.cur.tag, false, false),
        .keyword_extern => try self.parseExternDecl(),

        // simple builtin types
        .keyword_any => blk: {
            const loc = self.toLocId(self.cur.loc);
            self.advance();
            break :blk self.addExpr(.AnyType, .{ .loc = loc });
        },
        .keyword_type => blk: {
            const loc = self.toLocId(self.cur.loc);
            self.advance();
            break :blk self.addExpr(.TypeType, .{ .loc = loc });
        },
        .keyword_noreturn => blk: {
            const loc = self.toLocId(self.cur.loc);
            self.advance();
            break :blk self.addExpr(.NoreturnType, .{ .loc = loc });
        },
        .keyword_complex => try self.parseComplexType(),
        .keyword_simd => try self.parseSimdType(),
        .keyword_tensor => try self.parseTensorType(),
        .keyword_struct => try self.parseStructLikeType(.keyword_struct, false),
        .keyword_union => try self.parseStructLikeType(.keyword_union, false),
        .keyword_enum => try self.parseEnumType(false),
        .keyword_variant => try self.parseVariantType(),
        .keyword_error => try self.parseErrorType(),

        // control / meta
        .keyword_return => try self.parseReturn(),
        .keyword_import => try self.parseImport(),
        .keyword_typeof => blk: {
            const start = try self.beginKeywordParen(.keyword_typeof);
            const e = try self.parseExpr(0, .expr);
            try self.endParen();
            break :blk self.addExpr(.TypeOf, .{ .expr = e, .loc = self.toLocId(start) });
        },
        .keyword_async => blk: {
            const loc = self.toLocId(self.cur.loc);
            self.advance();
            if (self.cur.tag == .keyword_proc or self.cur.tag == .keyword_fn) {
                break :blk try self.parseFunctionLike(self.cur.tag, false, true);
            }
            const body = try self.parseBlockExpr();
            break :blk self.addExpr(.Async, .{ .body = body, .loc = loc });
        },
        .keyword_if => try self.parseIfExpr(),
        .keyword_while => try self.parseWhileExpr(),
        .keyword_match => try self.parseMatchExpr(),
        .keyword_for => try self.parseForExpr(),
        .keyword_break => blk: {
            const tok = self.cur;
            const loc = self.toLocId(tok.loc);
            self.advance();
            var label: cst.OptStrId = .none();
            var value: cst.OptExprId = .none();

            if (self.cur.tag == .colon) {
                self.advance();
                const name = self.cur;
                try self.expect(.identifier);
                label = .some(self.intern(self.slice(name)));
            }
            if (!self.isStmtTerminator()) {
                value = .some(try self.parseExpr(0, .expr));
            }
            break :blk self.addExpr(.Break, .{ .label = label, .value = value, .loc = loc });
        },
        .keyword_continue => blk: {
            const loc = self.toLocId(self.cur.loc);
            self.advance();
            var label: cst.OptStrId = .none();
            if (self.cur.tag == .colon) {
                self.advance();
                const name = self.cur;
                try self.expect(.identifier);
                label = .some(self.intern(self.slice(name)));
            }
            break :blk self.addExpr(.Continue, .{ .label = label, .loc = loc });
        },
        .keyword_unreachable => blk: {
            const loc = self.toLocId(self.cur.loc);
            self.advance();
            break :blk self.addExpr(.Unreachable, .{ .loc = loc });
        },
        .keyword_null => blk: {
            const loc = self.toLocId(self.cur.loc);
            self.advance();
            break :blk self.addExpr(.Null, .{ .loc = loc });
        },
        .keyword_undefined => blk: {
            const loc = self.toLocId(self.cur.loc);
            self.advance();
            break :blk self.addExpr(.Undefined, .{ .loc = loc });
        },
        .keyword_defer => blk: {
            const loc = self.toLocId(self.cur.loc);
            self.advance();
            const e = try self.parseExpr(0, .expr);
            break :blk self.addExpr(.Defer, .{ .expr = e, .loc = loc });
        },
        .keyword_errdefer => blk: {
            const loc = self.toLocId(self.cur.loc);
            self.advance();
            const e = try self.parseExpr(0, .expr);
            break :blk self.addExpr(.ErrDefer, .{ .expr = e, .loc = loc });
        },
        else => {
            const got = self.cur;
            self.errorNote(self.cur.loc, .unexpected_token_in_expression, .{tag}, got.loc, .token_cannot_start_expression);
            self.sync(.eos);
            return error.UnexpectedToken;
        },
    };
}

/// Parse an expression using Pratt parsing with binding power `min_bp` and mode `mode`.
fn parseExpr(self: *Parser, min_bp: u8, comptime mode: ParseMode) anyerror!cst.ExprId {
    var left = try self.nud(self.cur.tag, mode);

    while (true) {
        const tag = self.cur.tag;

        // ---------- Postfix ----------
        if (postfix_bp_table[@intFromEnum(tag)]) |l_bp| {
            // never treat '!' as postfix in type context
            if (tag == .bang and mode == .type) {
                // skip; might be infix type operator
            } else if (l_bp >= min_bp) {
                // block struct-literal when not allowed
                if (tag == .lcurly and (mode == .type or mode == .expr_no_struct)) break;
                if (tag == .lcurly and !self.looksLikeCtorHead(left)) break;

                // SPECIAL-CASE: for '!' in expr modes
                // If next token looks like a type start, let infix handle error-union (T ! E)
                // Otherwise, treat as postfix error unwrap.
                if (tag == .bang and mode != .type) {
                    if (self.isTypeStart(self.nxt.tag)) {
                        // do not consume here; infix phase will handle
                    } else {
                        const loc = self.toLocId(self.cur.loc);
                        self.advance();
                        left = self.addExpr(.ErrUnwrap, .{ .expr = left, .loc = loc });
                        continue;
                    }
                }

                // Range postfix still defers to infix when it’s actually x..y or x..=y
                const should_let_infix_win = (tag == .dotdot or tag == .dotdoteq) and !self.nextIsTerminator();

                // Special-case: skip postfix consumption for '!' when used as infix error-union in expr mode
                if (tag == .bang and mode != .type and self.isTypeStart(self.nxt.tag)) {
                    // Do nothing here; the infix phase below will consume and build error_union
                } else if (!should_let_infix_win) {
                    const tok_loc = self.cur.loc;
                    self.advance();
                    left = switch (tag) {
                        .lparen => try self.parseCall(left),
                        .lsquare => try self.parseIndex(left),
                        .dot => try self.parsePostfixAfterDot(left),
                        .dotlparen => try self.parseCastParen(left),
                        .lcurly => blk: {
                            break :blk try self.parseStructLiteralWithHead(left, tok_loc);
                        },
                        .dotstar => try self.parseDeref(left),
                        .question => try self.parseOptionalUnwrap(left),
                        .keyword_catch => try self.parseCatchExpr(left),
                        else => {
                            const got = self.cur;
                            self.errorNote(self.cur.loc, .unexpected_postfix_operator, .{tag}, got.loc, .operator_cannot_be_used_here);
                            self.sync(.eos);
                            return error.UnexpectedToken;
                        },
                    };
                    continue;
                }
            }
        }
        // ---------- Infix ----------
        if (infix_bp_table[@intFromEnum(tag)]) |bp| {
            // Allow infix '!' as error-union in type mode,
            // or in expr mode when the next token begins a type.
            if (tag == .bang and !(mode == .type or self.isTypeStart(self.nxt.tag))) break;
            const l_bp, const r_bp = bp;
            if (l_bp < min_bp) break;

            const loc = self.toLocId(self.cur.loc);
            const op = self.toInfixOp(tag);
            self.advance();
            const right = try self.parseExpr(r_bp, mode);
            left = self.addExpr(.Infix, .{ .op = op, .left = left, .right = right, .loc = loc });
            continue;
        }

        break;
    }
    return left;
}

//=================================================================
// Common element parsers
//=================================================================
/// Parse a struct literal without a preceding type head (i.e. anonymous literal).
fn parseStructLiteral(self: *Parser, lcurly_loc: Token.Loc) !cst.ExprId {
    const start_loc = lcurly_loc;

    var sfv_ids: List(cst.StructFieldValueId) = .empty;
    defer sfv_ids.deinit(self.gpa);
    var trailing = false;

    while (self.cur.tag != .rcurly and self.cur.tag != .eof) {
        const field_tok = self.cur;
        var name_opt: cst.OptStrId = .none();
        if ((self.cur.tag == .identifier or self.cur.tag == .raw_identifier) and self.nxt.tag == .colon) {
            name_opt = .some(self.intern(self.slice(field_tok)));
            self.advance();
            try self.expect(.colon);
        }

        const value = try self.parseExpr(0, .expr);
        const entry_loc = self.toLocId(field_tok.loc);

        try sfv_ids.append(self.gpa, self.cst_u.exprs.addStructFieldValue(.{
            .name = name_opt,
            .value = value,
            .loc = entry_loc,
        }));

        trailing = self.consumeIf(.comma);
        if (!trailing or self.cur.tag == .rcurly) break;
    }
    const end_loc = self.cur.loc;
    try self.expect(.rcurly);

    const fields_range = self.cst_u.exprs.sfv_pool.pushMany(self.gpa, sfv_ids.items);
    const loc_id = self.toLocId(start_loc.merge(end_loc));
    return self.addExpr(.StructLit, .{ .fields = fields_range, .ty = .none(), .trailing_comma = trailing, .loc = loc_id });
}

/// Parse a struct literal that follows a type head (`T { ... }`).
fn parseStructLiteralWithHead(self: *Parser, head: cst.ExprId, lcurly_loc: Token.Loc) !cst.ExprId {
    // Current token is '{' (already consumed by caller switch advance)
    const start_loc = lcurly_loc;

    var sfv_ids: List(cst.StructFieldValueId) = .empty;
    defer sfv_ids.deinit(self.gpa);
    var trailing = false;

    while (self.cur.tag != .rcurly and self.cur.tag != .eof) {
        const field_tok = self.cur;
        var name_opt: cst.OptStrId = .none();
        if ((self.cur.tag == .identifier or self.cur.tag == .raw_identifier) and self.nxt.tag == .colon) {
            name_opt = .some(self.intern(self.slice(field_tok)));
            self.advance();
            try self.expect(.colon);
        }

        const value = try self.parseExpr(0, .expr);
        const entry_loc = self.toLocId(field_tok.loc);

        try sfv_ids.append(self.gpa, self.cst_u.exprs.addStructFieldValue(.{
            .name = name_opt,
            .value = value,
            .loc = entry_loc,
        }));

        trailing = self.consumeIf(.comma);
        if (!trailing or self.cur.tag == .rcurly) break;
    }
    const end_loc = self.cur.loc;
    try self.expect(.rcurly);

    const fields_range = self.cst_u.exprs.sfv_pool.pushMany(self.gpa, sfv_ids.items);
    const loc_id = self.toLocId(start_loc.merge(end_loc));
    return self.addExpr(.StructLit, .{ .fields = fields_range, .ty = .some(head), .trailing_comma = trailing, .loc = loc_id });
}

/// Parse an index access expression using `collection` as the base.
fn parseIndex(self: *Parser, collection: cst.ExprId) anyerror!cst.ExprId {
    // '[' was already consumed.
    const loc = self.toLocId(self.cur.loc);
    const index = try self.parseExpr(0, .expr);
    try self.expect(.rsquare);
    return self.addExpr(.IndexAccess, .{ .collection = collection, .index = index, .loc = loc });
}

/// Parse a field access or method call candidate on `parent`.
fn parseField(self: *Parser, parent: cst.ExprId) !cst.ExprId {
    // '.' was already consumed.
    const tok = self.cur;
    var is_tuple = false;

    switch (tok.tag) {
        .identifier, .raw_identifier => self.advance(),
        .integer_literal => {
            is_tuple = true;
            self.advance();
        },
        else => {
            self.errorNote(self.cur.loc, .expected_field_name_or_index, .{tok.tag}, tok.loc, .expected_field_name_or_index_note);
            self.sync(.eos);
            return error.UnexpectedToken;
        },
    }

    const loc = self.toLocId(tok.loc);
    const name = self.intern(self.slice(tok));
    return self.addExpr(.FieldAccess, .{ .parent = parent, .field = name, .is_tuple = is_tuple, .loc = loc });
}

/// Parse comma-separated expressions until `end_tag`, returning range + trailing flag.
fn parseCommaExprListUntil(self: *Parser, comptime end_tag: Token.Tag) anyerror!struct { range: cst.RangeOf(cst.ExprId), trailing: bool } {
    var items: List(cst.ExprId) = .empty;
    defer items.deinit(self.gpa);

    var trailing = false;
    if (self.cur.tag != end_tag) {
        while (true) {
            try items.append(self.gpa, try self.parseExpr(0, .expr));
            trailing = self.consumeIf(.comma);
            if (!trailing or self.cur.tag == end_tag) break;
        }
    }
    try self.expect(end_tag);
    return .{
        .range = self.cst_u.exprs.expr_pool.pushMany(self.gpa, items.items),
        .trailing = trailing,
    };
}

// '(' was already consumed. This parses args and emits the Call row.
/// Parse a call expression with previously parsed `callee`.
fn parseCall(self: *Parser, callee: cst.ExprId) !cst.ExprId {
    const loc = self.toLocId(self.cur.loc);
    const args = try self.parseCommaExprListUntil(.rparen);
    return self.addExpr(.Call, .{ .callee = callee, .args = args.range, .trailing_arg_comma = args.trailing, .loc = loc });
}

// ================================
// Statements / blocks
// ================================

/// Parse dereference (`*expr` or `expr.*`) syntax.
inline fn parseDeref(self: *Parser, expr: cst.ExprId) !cst.ExprId {
    const loc = self.toLocId(self.cur.loc); // '. *' already consumed
    return self.addExpr(.Deref, .{ .expr = expr, .loc = loc });
}

/// Parse optional unwrap (`expr?`) expressions.
inline fn parseOptionalUnwrap(self: *Parser, expr: cst.ExprId) !cst.ExprId {
    const loc = self.toLocId(self.cur.loc); // '?' already consumed
    return self.addExpr(.OptionalUnwrap, .{ .expr = expr, .loc = loc });
}

/// Parse postfix operations that follow a dot (field/method access).
inline fn parsePostfixAfterDot(self: *Parser, left: cst.ExprId) anyerror!cst.ExprId {
    return switch (self.cur.tag) {
        .keyword_await => try self.parseAwait(left),
        .caret, .b_or, .percent, .question => try self.parseCastSigil(left),
        else => try self.parseField(left),
    };
}

/// Handle casts written as `(type) expr`.
fn parseCastParen(self: *Parser, expr: cst.ExprId) !cst.ExprId {
    const loc = self.toLocId(self.cur.loc); // '.(' already consumed
    const ty = try self.parseExpr(0, .type);
    try self.expect(.rparen);
    return self.addExpr(.Cast, .{ .expr = expr, .ty = ty, .kind = .normal, .loc = loc });
}

/// Parse signed/unsigned cast sigils (using `&`/`!`).
fn parseCastSigil(self: *Parser, expr: cst.ExprId) anyerror!cst.ExprId {
    const loc = self.toLocId(self.cur.loc);
    const kind: cst.CastKind = switch (self.cur.tag) {
        .caret => .bitcast,
        .b_or => .saturate,
        .percent => .wrap,
        .question => .checked,
        else => unreachable,
    };
    self.advance();
    const ty = try self.parseExpr(postfix_bp_table[@intFromEnum(Token.Tag.dot)].?, .type);
    return self.addExpr(.Cast, .{ .expr = expr, .ty = ty, .kind = kind, .loc = loc });
}

/// Parse an `await` expression operating on `expr`.
inline fn parseAwait(self: *Parser, expr: cst.ExprId) !cst.ExprId {
    const loc = self.toLocId(self.cur.loc);
    try self.expect(.keyword_await);
    return self.addExpr(.Await, .{ .expr = expr, .loc = loc });
}

/// Parse a `return` expression (with optional value).
inline fn parseReturn(self: *Parser) !cst.ExprId {
    const tok = self.cur;
    const loc = self.toLocId(tok.loc);
    self.advance(); // 'return'
    const value: cst.OptExprId = if (!self.isStmtTerminator())
        .some(try self.parseExpr(0, .expr))
    else
        .none();
    if (!self.isStmtTerminator()) try self.expect(.eos);
    return self.addExpr(.Return, .{ .value = value, .loc = loc });
}

// Make block emit a Block expr directly.
/// Parse a block expression `{ ... }`, building a `Block` node.
fn parseBlock(self: *Parser) !cst.ExprId {
    var decl_ids: List(cst.DeclId) = .empty;
    defer decl_ids.deinit(self.gpa);

    const brace_loc = try self.beginBrace(); // returns Token.Loc
    while (self.cur.tag != .rcurly and self.cur.tag != .eof) {
        const did = self.parseDecl() catch {
            // self.sync(.eos);
            continue;
        };
        try decl_ids.append(self.gpa, did);
    }
    const close_loc = try self.endBrace();

    const range = self.cst_u.exprs.decl_pool.pushMany(self.gpa, decl_ids.items);
    return self.addExpr(.Block, .{ .items = range, .loc = self.toLocId(brace_loc.merge(close_loc)) });
}

/// Parse an expression that may either be a block or inline expression.
fn parseBlockExpr(self: *Parser) !cst.ExprId {
    return self.parseBlock();
}

/// Parse either an expression or a block expression, whichever matches.
inline fn parseExprOrBlock(self: *Parser) !cst.ExprId {
    if (self.cur.tag == .lcurly) return self.parseBlock();
    return self.parseExpr(0, .expr);
}

// -------------------- Closures --------------------
/// Parse a closure literal (proc or fn) starting with `{ }`.
fn parseClosure(self: *Parser) !cst.ExprId {
    const loc = self.toLocId(self.cur.loc);
    try self.expect(.b_or);

    var param_ids: List(cst.ParamId) = .empty;
    defer param_ids.deinit(self.gpa);

    if (self.cur.tag != .b_or) {
        const p = infix_bp_table[@intFromEnum(Token.Tag.b_or)].?; // { l_bp, r_bp }
        const r_bp: u8 = p[1];
        const barrier: u8 = r_bp + 1;

        while (true) {
            const start_tok = self.cur;
            const is_comptime = self.cur.tag == .keyword_comptime;
            if (is_comptime) self.advance();
            const p_loc = self.toLocId(start_tok.loc);
            const pat_expr = try self.parseExpr(barrier, .expr_no_struct);

            var ty_opt: cst.OptExprId = .none();
            var val_opt: cst.OptExprId = .none();

            if (self.cur.tag == .colon) {
                self.advance();
                ty_opt = .some(try self.parseExpr(barrier, .type));
            }
            if (self.cur.tag == .equal) {
                self.advance();
                val_opt = .some(try self.parseExpr(0, .expr));
            }

            try param_ids.append(self.gpa, self.cst_u.exprs.addParamRow(.{
                .pat = .some(pat_expr),
                .ty = ty_opt,
                .value = val_opt,
                .attrs = .none(),
                .is_comptime = is_comptime,
                .loc = p_loc,
            }));

            if (self.consumeIf(.comma)) continue;
            if (self.cur.tag == .b_or) break;

            const got = self.cur;
            self.errorNote(self.cur.loc, .expected_closure_param_separator, .{got.tag}, got.loc, .separate_parameters);
            self.sync(.b_or);
            return error.UnexpectedToken;
        }
    }
    try self.expect(.b_or);

    var result_ty: cst.OptExprId = .none();
    var body: cst.ExprId = undefined;

    if (self.cur.tag == .lcurly) {
        body = try self.parseBlock();
    } else {
        const ty_or_body = try self.parseExpr(0, .type);
        if (self.cur.tag == .lcurly) {
            result_ty = .some(ty_or_body);
            body = try self.parseBlock();
        } else {
            body = ty_or_body; // expression-bodied closure
        }
    }

    const params_range = self.cst_u.exprs.param_pool.pushMany(self.gpa, param_ids.items);
    return self.addExpr(.Closure, .{
        .params = params_range,
        .result_ty = result_ty,
        .body = body,
        .loc = loc,
    });
}

// -------------------- catch postfix --------------------
/// Parse a catch-expression `expr catch |name| handler`.
fn parseCatchExpr(self: *Parser, expr: cst.ExprId) !cst.ExprId {
    const loc = self.toLocId(self.cur.loc); // 'catch' was consumed by caller
    var b_name: cst.OptStrId = .none();
    var b_loc: cst.OptLocId = .none();

    if (self.cur.tag == .b_or) {
        self.advance();
        const name_tok = self.cur;
        const name_loc = self.toLocId(name_tok.loc);
        try self.expect(.identifier);
        const name = self.slice(name_tok);
        b_name = .some(self.intern(name));
        b_loc = .some(name_loc);
        try self.expect(.b_or);
    }

    const handler = try self.parseExprOrBlock();
    return self.addExpr(.Catch, .{
        .expr = expr,
        .binding_name = b_name,
        .binding_loc = b_loc,
        .handler = handler,
        .loc = loc,
    });
}

/// Parse an `import` expression (path literal + optional config).
fn parseImport(self: *Parser) !cst.ExprId {
    const loc = self.toLocId(self.cur.loc);
    self.advance(); // 'import'

    // Grab the raw string literal contents.
    const name_raw = std.mem.trim(u8, self.slice(self.cur), "\"");
    try self.expect(.string_literal);

    const path_id = self.intern(name_raw);
    return self.addExpr(.Import, .{ .path = path_id, .loc = loc });
}

/// Entry point invoked by worker threads to parse one CST unit.
pub fn run(
    parser: *Parser,
) !void {
    try parser.parseProgram();
}

// -------------------- if / while / for --------------------
/// Parse an `if` expression, including condition, then-branch, and optional else/elif.
fn parseIfExpr(self: *Parser) !cst.ExprId {
    const if_loc = self.toLocId(self.cur.loc);
    self.advance(); // "if"
    const cond = try self.parseExpr(0, .expr_no_struct);
    const then_block = try self.parseBlock();

    const else_opt: cst.OptExprId = if (self.cur.tag == .keyword_else) blk: {
        self.advance();
        break :blk .some(try self.parseExprOrBlock());
    } else .none();
    return self.addExpr(.If, .{
        .cond = cond,
        .then_block = then_block,
        .else_block = else_opt,
        .loc = if_loc,
    });
}

/// Parse a `while` loop, optionally labeled with `label`.
fn parseWhileExprWithLabel(self: *Parser, label: cst.OptStrId) !cst.ExprId {
    const w_loc = self.toLocId(self.cur.loc);
    self.advance(); // "while"

    var cond_opt: cst.OptExprId = .none();
    var pat_opt: cst.SentinelIndex(cst.PatTag) = .none();
    var is_pat: bool = false;

    switch (self.cur.tag) {
        .keyword_is => {
            self.advance();
            const pat = try self.parsePattern();
            try self.expect(.coloneq);
            const cond = try self.parseExpr(0, .expr_no_struct);
            cond_opt = .some(cond);
            pat_opt = .some(pat);
            is_pat = true;
        },
        .lcurly => {
            // forever loop: no condition
        },
        else => {
            cond_opt = .some(try self.parseExpr(0, .expr_no_struct));
        },
    }

    const body = try self.parseBlock();
    return self.addExpr(.While, .{
        .cond = cond_opt,
        .pattern = pat_opt,
        .body = body,
        .is_pattern = is_pat,
        .label = label,
        .loc = w_loc,
    });
}

/// Parse a `while` loop expression, possibly with labels or pattern subjects.
fn parseWhileExpr(self: *Parser) !cst.ExprId {
    return self.parseWhileExprWithLabel(.none());
}

/// Parse a `match` expression with multiple arms.
fn parseMatchExpr(self: *Parser) !cst.ExprId {
    const start_loc_tok = self.cur; // "match"
    self.advance();
    const scrutinee = try self.parseExpr(0, .expr_no_struct);
    try self.expect(.lcurly);

    // Collect arm ids, then commit them contiguously into the arm_pool.
    var tmp_arms: List(cst.MatchArmId) = .empty;
    defer tmp_arms.deinit(self.gpa);

    while (self.cur.tag != .rcurly and self.cur.tag != .eof) {
        const pat_id = try self.parsePattern(); // PatternId
        // optional guard
        var guard_opt: cst.OptExprId = .none();
        if (self.cur.tag == .keyword_if) {
            self.advance();
            const gexpr = try self.parseExpr(0, .expr_no_struct);
            guard_opt = .some(gexpr);
        }
        try self.expect(.fatarrow);

        // body (expr or block)
        const body_id = try self.parseExprOrBlock();
        try self.expect(.comma);

        // arm row → id
        try tmp_arms.append(self.gpa, self.cst_u.exprs.addMatchArmRow(.{
            .pattern = pat_id,
            .guard = guard_opt,
            .body = body_id,
            .loc = self.toLocId(self.cur.loc),
        }));
    }

    try self.expect(.rcurly);

    // Commit arm ids into a contiguous range in the arm_pool.
    const arms_range = self.cst_u.exprs.arm_pool.pushMany(self.gpa, tmp_arms.items);

    // Build the Match expr.
    return self.addExpr(.Match, .{
        .expr = scrutinee,
        .arms = arms_range,
        .loc = self.toLocId(start_loc_tok.loc),
    });
}

/// Parse a `for` loop (pattern+iterable) optionally labeled.
fn parseForExprWithLabel(self: *Parser, label: cst.OptStrId) !cst.ExprId {
    const f_loc = self.toLocId(self.cur.loc);
    self.advance(); // "for"
    const pat = try self.parsePattern();
    try self.expect(.keyword_in);
    const it = try self.parseExpr(0, .expr_no_struct);
    const body = try self.parseBlock();

    return self.addExpr(.For, .{
        .pattern = pat,
        .iterable = it,
        .body = body,
        .label = label,
        .loc = f_loc,
    });
}

/// Parse a `for` loop, including pattern binding and iterable.
fn parseForExpr(self: *Parser) !cst.ExprId {
    return self.parseForExprWithLabel(.none());
}

// label: for/while ...
/// Parse a loop that may carry a label `lbl`.
fn parseLabeledLoop(self: *Parser, lbl: cst.OptStrId) !cst.ExprId {
    return switch (self.cur.tag) {
        .keyword_for => self.parseForExprWithLabel(lbl),
        .keyword_while => self.parseWhileExprWithLabel(lbl),
        else => {
            const got = self.cur;
            self.errorNote(
                self.cur.loc,
                .expected_loop_after_label,
                .{got.tag},
                got.loc,
                .labeled_loops,
            );
            self.sync(.eos);
            return error.UnexpectedToken;
        },
    };
}

// =============================
// Patterns
// =============================
/// Parse a pattern literal (used in match/let destructuring).
fn parsePattern(self: *Parser) !cst.PatternId {
    return try self.parsePatOr();
}

/// Parse pattern disjunctions separated by `|`.
fn parsePatOr(self: *Parser) !cst.PatternId {
    const loc = self.toLocId(self.cur.loc);
    const first = try self.parsePatRange();
    if (self.cur.tag != .b_or) return first;

    var alts: List(cst.PatternId) = .empty;
    defer alts.deinit(self.gpa);

    try alts.append(self.gpa, first);
    while (self.cur.tag == .b_or) {
        self.advance();
        try alts.append(self.gpa, try self.parsePatRange());
    }
    const alts_range = self.cst_u.pats.pat_pool.pushMany(self.gpa, alts.items);
    return self.addPat(.Or, .{ .alts = alts_range, .loc = loc });
}

/// Determine if token `tag` can start a pattern literal.
fn canStartPattern(self: *Parser, tag: Token.Tag) bool {
    if (self.isLiteralTag(tag)) return true;
    return switch (tag) {
        .plus, .minus, .dotdot, .dotdoteq, .lsquare, .lparen, .lcurly, .keyword_proc, .keyword_fn, .keyword_extern, .keyword_any, .keyword_type, .keyword_noreturn, .keyword_complex, .keyword_simd, .keyword_tensor, .keyword_struct, .keyword_union, .keyword_enum, .keyword_variant, .keyword_error, .keyword_return, .keyword_import, .keyword_typeof, .keyword_async, .keyword_if, .keyword_while, .keyword_match, .keyword_for, .keyword_break, .keyword_continue, .keyword_unreachable, .keyword_null, .keyword_undefined, .keyword_defer, .keyword_errdefer => true,
        else => false,
    };
}

/// Parse a numeric range pattern `start..end`.
fn parsePatRange(self: *Parser) !cst.PatternId {
    // prefix/open: ..X or ..=X
    if (self.cur.tag == .dotdot or self.cur.tag == .dotdoteq) {
        const loc = self.toLocId(self.cur.loc);
        const inclusive = (self.cur.tag == .dotdoteq);
        self.advance();
        const end_expr = try self.parseConstExprForRangeEnd();
        return self.addPat(.Range, .{
            .start = .none(),
            .end = .some(end_expr),
            .inclusive_right = inclusive,
            .loc = loc,
        });
    }

    // otherwise parse left atom
    const left = try self.parsePatAt();

    // infix: LEFT .. RIGHT
    if (self.cur.tag == .dotdot or self.cur.tag == .dotdoteq) {
        const loc = self.toLocId(self.cur.loc);
        const inclusive = (self.cur.tag == .dotdoteq);
        self.advance();

        var end_expr_opt: cst.OptExprId = .none();
        if (self.canStartPattern(self.cur.tag)) {
            end_expr_opt = .some(try self.parseConstExprForRangeEnd());
        }

        const lhs_expr = try self.patternToConstExpr(left);

        return self.addPat(.Range, .{
            .start = .some(lhs_expr),
            .end = end_expr_opt,
            .inclusive_right = inclusive,
            .loc = loc,
        });
    }

    return left;
}

/// Convert literal pattern `pat` into a constant expression for analysis.
fn patternToConstExpr(self: *Parser, pat: cst.PatternId) !cst.ExprId {
    const kind = self.cst_u.kind(pat);
    return switch (kind) {
        .Literal => self.cst_u.pats.get(.Literal, pat).expr,
        .Path => blk: {
            const r = self.cst_u.pats.get(.Path, pat).segments;
            break :blk try self.pathToConstExpr(r);
        },
        .Binding => blk: {
            const row = self.cst_u.pats.get(.Binding, pat);
            break :blk self.addExpr(.Ident, .{ .name = row.name, .loc = row.loc });
        },
        .Parenthesized => blk: {
            const row = self.cst_u.pats.get(.Parenthesized, pat);
            break :blk try self.patternToConstExpr(row.pattern);
        },
        .Wildcard => {
            self.errorNote(self.cur.loc, .underscore_not_const_in_range_pattern, .{}, null, .use_literal_constant_or_binding);
            self.sync(.eos);
            return error.UnexpectedToken;
        },
        else => {
            self.errorNote(self.cur.loc, .left_side_not_const_like_in_range_pattern, .{}, null, .use_literal_constant_or_simple_binding);
            self.sync(.eos);
            return error.UnexpectedToken;
        },
    };
}

/// Extract the binding name associated with a `@` pattern, if any.
fn patternToBindingName(self: *Parser, pat: cst.PatternId) !cst.StrId {
    const kind = self.cst_u.kind(pat);
    return switch (kind) {
        .Binding => self.cst_u.pats.get(.Binding, pat).name,

        .Path => blk: {
            const p = self.cst_u.pats.get(.Path, pat);
            // p.segments : RangeOf(PathSegId)
            const ids = self.cst_u.pats.seg_pool.slice(p.segments); // []const PathSegId
            if (ids.len == 1) {
                const seg0 = self.cst_u.pats.PathSeg.get(ids[0]); // row lookup
                break :blk seg0.name; // StrId
            }
            self.errorNote(self.cur.loc, .invalid_binding_name_in_at_pattern, .{}, null, .use_single_identifier);
            return error.InvalidPatternForBinding;
        },
        .Parenthesized => blk: {
            const row = self.cst_u.pats.get(.Parenthesized, pat);
            break :blk try self.patternToBindingName(row.pattern);
        },

        else => {
            self.errorNote(self.cur.loc, .invalid_binding_name_in_at_pattern, .{}, null, .use_single_identifier);
            return error.InvalidPatternForBinding;
        },
    };
}

/// Parse an `@binder pattern` form.
fn parsePatAt(self: *Parser) !cst.PatternId {
    const p = try self.parsePatPrimary();

    if (self.cur.tag == .at) { // '@'
        const loc = self.toLocId(self.cur.loc);
        self.advance();
        const sub = try self.parsePatAt(); // right-assoc
        const binder = try self.patternToBindingName(p);
        return self.addPat(.At, .{ .binder = binder, .pattern = sub, .loc = loc });
    }
    return p;
}

/// Parse primary pattern forms (literal, identifier, tuple, struct, etc.).
fn parsePatPrimary(self: *Parser) !cst.PatternId {
    switch (self.cur.tag) {
        .char_literal, .string_literal, .raw_string_literal, .integer_literal, .float_literal, .keyword_true, .keyword_false => {
            const lit_expr = try self.nud(self.cur.tag, .expr_no_struct); // will consume token
            const loc = self.toLocId(self.cur.loc);
            return self.addPat(.Literal, .{ .expr = lit_expr, .loc = loc });
        },
        .plus, .minus => {
            const lit_expr = try self.nud(self.cur.tag, .expr_no_struct);
            const loc = self.toLocId(self.cur.loc);
            return self.addPat(.Literal, .{ .expr = lit_expr, .loc = loc });
        },
        .lparen => return try self.parseTuplePattern(),
        .lsquare => return try self.parseSlicePattern(), // use your DOD version
        .dotdot, .dotdoteq => {
            const loc = self.toLocId(self.cur.loc);
            const inclusive = (self.cur.tag == .dotdoteq);
            self.advance();
            const end_expr = try self.parseConstExprForRangeEnd();
            return self.addPat(.Range, .{
                .start = .none(),
                .end = .some(end_expr),
                .inclusive_right = inclusive,
                .loc = loc,
            });
        },
        .identifier => return try self.parsePathishPattern(),
        else => {
            self.errorNote(self.cur.loc, .unexpected_token_in_pattern, .{self.cur.tag}, null, .token_cannot_start_pattern);
            self.sync(.eos);
            return error.UnexpectedToken;
        },
    }
}

/// Parse tuple-like pattern `(p1, p2, ...)`.
fn parseTuplePattern(self: *Parser) anyerror!cst.PatternId {
    const loc_tok = self.cur.loc;
    try self.expect(.lparen);

    var elems: List(cst.PatternId) = .empty;
    defer elems.deinit(self.gpa);

    var trailing_comma = false;
    if (self.cur.tag != .rparen) {
        while (true) {
            try elems.append(self.gpa, try self.parsePattern());
            trailing_comma = self.consumeIf(.comma);
            if (!trailing_comma or self.cur.tag == .rparen) break;
        }
    }
    try self.expect(.rparen);

    if (elems.items.len == 1 and !trailing_comma) {
        return self.addPat(.Parenthesized, .{ .pattern = elems.items[0], .loc = self.toLocId(loc_tok) });
    }

    const range = self.cst_u.pats.pat_pool.pushMany(self.gpa, elems.items);
    return self.addPat(.Tuple, .{ .elems = range, .loc = self.toLocId(loc_tok) });
}

/// Parse path-like patterns referencing constructors or fields.
fn parsePathishPattern(self: *Parser) anyerror!cst.PatternId {
    // collect dotted path: Foo.Bar.Baz
    var seg_ids: List(cst.PathSegId) = .empty;
    defer seg_ids.deinit(self.gpa);

    const first_loc = self.cur.loc;

    while (true) {
        const tok = self.cur;
        try self.expect(.identifier);
        const name = self.intern(self.slice(tok));
        const seg = self.cst_u.pats.addPathSeg(.{ .name = name, .loc = self.toLocId(tok.loc) });
        try seg_ids.append(self.gpa, seg);

        if (!self.consumeIf(.dot)) break;
        if (self.cur.tag != .identifier) break;
    }

    const path_range = self.cst_u.pats.seg_pool.pushMany(self.gpa, seg_ids.items);

    switch (self.cur.tag) {
        .lparen => {
            const loc_tok = self.cur.loc;
            self.advance();
            var elems: List(cst.PatternId) = .empty;
            defer elems.deinit(self.gpa);

            if (self.cur.tag != .rparen) {
                while (true) {
                    try elems.append(self.gpa, try self.parsePattern());
                    if (!self.consumeIf(.comma)) break;
                }
            }
            try self.expect(.rparen);

            const elems_range = self.cst_u.pats.pat_pool.pushMany(self.gpa, elems.items);
            return self.addPat(.VariantTuple, .{
                .path = path_range,
                .elems = elems_range,
                .loc = self.toLocId(loc_tok),
            });
        },
        .lcurly => {
            self.advance();
            var fields: List(cst.PatFieldId) = .empty;
            defer fields.deinit(self.gpa);

            var has_rest = false;
            const ploc = self.toLocId(self.cur.loc);

            while (self.cur.tag != .rcurly and self.cur.tag != .eof) {
                if (self.cur.tag == .dotdot) {
                    has_rest = true;
                    self.advance();
                    if (self.cur.tag == .comma) self.advance();
                    break;
                }

                const name_tok = self.cur;
                try self.expect(.identifier);
                const name = self.intern(self.slice(name_tok));
                const nloc = self.toLocId(name_tok.loc);

                var p: cst.PatternId = undefined;
                if (self.cur.tag == .colon) {
                    self.advance();
                    p = try self.parsePattern();
                } else {
                    p = self.addPat(.Binding, .{ .name = name, .by_ref = false, .is_mut = false, .loc = nloc });
                }

                try fields.append(self.gpa, self.cst_u.pats.addPatField(.{ .name = name, .pattern = p, .loc = nloc }));

                if (!self.consumeIf(.comma)) break;
            }
            try self.expect(.rcurly);

            const fields_range = self.cst_u.pats.field_pool.pushMany(self.gpa, fields.items);
            return self.addPat(.VariantStruct, .{
                .path = path_range,
                .fields = fields_range,
                .has_rest = has_rest,
                .loc = ploc,
            });
        },
        .dotdot, .dotdoteq => {
            const inclusive = (self.cur.tag == .dotdoteq);
            const loc = self.toLocId(self.cur.loc);
            self.advance();
            const rhs = try self.parseConstExprForRangeEnd();
            const start_expr = try self.pathToConstExpr(path_range);
            return self.addPat(.Range, .{
                .start = .some(start_expr),
                .end = .some(rhs),
                .inclusive_right = inclusive,
                .loc = loc,
            });
        },
        else => {
            // bare identifier/path: wildcard / binding / path
            const seg_ids_slice = self.cst_u.pats.seg_pool.slice(path_range);
            if (seg_ids_slice.len == 1) {
                const seg_row = self.cst_u.pats.PathSeg.get(seg_ids_slice[0]); // FIX
                const seg_name_bytes = self.cst_u.exprs.strs.get(seg_row.name);
                if (std.mem.eql(u8, seg_name_bytes, "_")) {
                    return self.addPat(.Wildcard, .{ .loc = seg_row.loc });
                }
                return self.addPat(.Binding, .{
                    .name = seg_row.name,
                    .by_ref = false,
                    .is_mut = false,
                    .loc = seg_row.loc,
                });
            }
            return self.addPat(.Path, .{ .segments = path_range, .loc = self.toLocId(first_loc) });
        },
    }
}

//==============================================================
// Slice pattern  […, .. rest]
//==============================================================
/// Parse slice-style patterns (like `[head, ...rest]`).
fn parseSlicePattern(self: *Parser) anyerror!cst.PatternId {
    try self.expect(.lsquare);

    var elems: List(cst.PatternId) = .empty;
    defer elems.deinit(self.gpa);

    var has_rest: bool = false;
    var rest_index: u32 = 0;
    var rest_binding: cst.SentinelIndex(cst.PatTag) = .none();
    const loc = self.toLocId(self.cur.loc);

    if (self.cur.tag != .rsquare) {
        var i: u32 = 0;
        while (true) : (i += 1) {
            if (self.cur.tag == .dotdot) {
                has_rest = true;
                rest_index = i;
                self.advance();

                // Optional: `.. name`
                if (self.cur.tag == .identifier) {
                    const name_tok = self.cur;
                    self.advance();
                    if (!std.mem.eql(u8, self.slice(name_tok), "_")) {
                        const bind_id = self.addPat(.Binding, .{
                            .name = self.intern(self.slice(name_tok)),
                            .by_ref = false,
                            .is_mut = false,
                            .loc = self.toLocId(name_tok.loc),
                        });
                        rest_binding = .some(bind_id);
                    }
                }

                _ = self.consumeIf(.comma);
                break; // `..` consumes the remainder
            }
            try elems.append(self.gpa, try self.parsePattern());
            if (!self.consumeIf(.comma)) break;
        }
    }

    try self.expect(.rsquare);

    const elems_range = self.cst_u.pats.pat_pool.pushMany(self.gpa, elems.items);
    return self.addPat(.Slice, .{
        .elems = elems_range,
        .has_rest = has_rest,
        .rest_index = rest_index,
        .rest_binding = rest_binding,
        .loc = loc,
    });
}

//==============================================================
// Const-expr helper for ranges
//==============================================================
/// Parse the expression used for the end of a range pattern.
fn parseConstExprForRangeEnd(self: *Parser) !cst.ExprId {
    return self.parseExpr(0, .expr_no_struct);
}

//==============================================================
// Path → const expr  (for temporary Name lists)
//==============================================================
/// Convert a path expression into the corresponding const expression.
fn pathToConstExpr(self: *Parser, segs_range: cst.RangeOf(cst.PathSegId)) !cst.ExprId {
    const ids = self.cst_u.pats.seg_pool.slice(segs_range); // []const PathSegId
    std.debug.assert(ids.len >= 1);

    // first segment → Ident
    const first = self.cst_u.pats.PathSeg.get(ids[0]);
    var e = self.addExpr(.Ident, .{
        .name = first.name, // StrId already
        .loc = first.loc, // LocId already
    });

    // remaining segments → FieldAccess chain
    var i: usize = 1;
    while (i < ids.len) : (i += 1) {
        const seg = self.cst_u.pats.PathSeg.get(ids[i]);
        e = self.addExpr(.FieldAccess, .{
            .parent = e,
            .field = seg.name, // StrId
            .is_tuple = false,
            .loc = seg.loc, // LocId
        });
    }
    return e;
}

//==============================================================
// Types: struct fields & aggregates
//==============================================================
/// Parse a struct literal or type field definition.
fn parseStructField(self: *Parser) !cst.StructFieldId {
    const start_loc = self.toLocId(self.cur.loc);

    if (self.cur.tag == .keyword_pub) self.advance();

    const field_attrs = try self.parseOptionalAttributesRange(); // DOD version below
    const name_tok = self.cur;
    if (self.cur.tag == .identifier or self.cur.tag == .raw_identifier) {
        self.advance();
    } else {
        try self.expect(.identifier);
    }
    const name = self.slice(name_tok);
    try self.expect(.colon);

    const ty = try self.parseExpr(0, .type);
    const value = try self.parseOptionalInitializer(.expr);

    return self.cst_u.exprs.addStructFieldRow(.{
        .name = self.intern(name),
        .ty = ty,
        .value = value,
        .attrs = field_attrs,
        .loc = start_loc,
    });
}

/// Parse a comma-separated list of struct-style fields until `end_tag`.
fn parseStructFieldList(self: *Parser, end_tag: Token.Tag) !struct { range: cst.RangeOf(cst.StructFieldId), trailing: bool } {
    var ids: List(cst.StructFieldId) = .empty;
    defer ids.deinit(self.gpa);

    var trailing = false;
    while (self.cur.tag != end_tag and self.cur.tag != .eof) {
        try ids.append(self.gpa, try self.parseStructField());
        trailing = self.consumeIf(.comma);
        if (!trailing or self.cur.tag == end_tag) break;
    }
    try self.expect(end_tag);

    return .{
        .range = self.cst_u.exprs.sfield_pool.pushMany(self.gpa, ids.items),
        .trailing = trailing,
    };
}

/// Parse struct/union/variant type declarations (`struct/union` keywords).
fn parseStructLikeType(self: *Parser, comptime tag: Token.Tag, comptime is_extern: bool) !cst.ExprId {
    const loc = self.toLocId(self.cur.loc);
    self.advance(); // "struct" / "union"

    try self.expect(.lcurly);
    const fields = try self.parseStructFieldList(.rcurly);

    return if (tag == .keyword_struct)
        self.addExpr(.StructType, .{ .fields = fields.range, .is_extern = is_extern, .attrs = .none(), .trailing_field_comma = fields.trailing, .loc = loc })
    else
        self.addExpr(.UnionType, .{ .fields = fields.range, .is_extern = is_extern, .attrs = .none(), .trailing_field_comma = fields.trailing, .loc = loc });
}

//==============================================================
// Types: pointer / optional / complex / simd / tensor
//==============================================================
/// Parse a pointer (`*T`) type expression.
fn parsePointerType(self: *Parser) !cst.ExprId {
    const tok = self.cur;
    self.advance(); // "*"

    var is_const = false;
    if (self.cur.tag == .keyword_const) {
        is_const = true;
        self.advance();
    }

    const elem = try self.parseExpr(0, .type);
    return self.addExpr(.PointerType, .{
        .elem = elem,
        .is_const = is_const,
        .loc = self.toLocId(tok.loc),
    });
}

/// Parse an optional type (`?T`) expression.
fn parseOptionalType(self: *Parser) !cst.ExprId {
    const tok = self.cur;
    self.advance(); // "?"
    const elem = try self.parseExpr(0, .type);
    return self.addExpr(.OptionalType, .{ .elem = elem, .loc = self.toLocId(tok.loc) });
}

/// Parse a complex number type expression.
fn parseComplexType(self: *Parser) !cst.ExprId {
    const start = try self.beginKeywordParen(.keyword_complex);
    const elem = try self.parseExpr(0, .type);
    try self.endParen();
    return self.addExpr(.ComplexType, .{ .elem = elem, .loc = self.toLocId(start) });
}

/// Parse a SIMD type expression with lane count.
fn parseSimdType(self: *Parser) !cst.ExprId {
    const start = try self.beginKeywordParen(.keyword_simd);
    const elem = try self.parseExpr(0, .type);
    try self.expect(.comma);
    const lanes = try self.parseExpr(0, .expr);
    try self.endParen();
    return self.addExpr(.SimdType, .{ .elem = elem, .lanes = lanes, .loc = self.toLocId(start) });
}

/// Parse a tensor type expression specifying rank/shape.
fn parseTensorType(self: *Parser) !cst.ExprId {
    const start = try self.beginKeywordParen(.keyword_tensor);

    var items: List(cst.ExprId) = .empty;
    defer items.deinit(self.gpa);

    while (self.cur.tag != .rparen and self.cur.tag != .eof) {
        try items.append(self.gpa, try self.parseExpr(0, .expr));
        if (!self.consumeIf(.comma)) break;
    }
    try self.expect(.rparen);

    if (items.items.len == 0) {
        self.errorNote(start, .tensor_missing_arguments, .{}, null, .provide_element_type_last);
        self.sync(.eos);
        return error.UnexpectedToken;
    }

    var elem_index_opt: ?usize = null;
    var scan: usize = items.items.len;
    while (scan > 0) {
        scan -= 1;
        if (!self.exprIsIntegerLiteral(items.items[scan])) {
            elem_index_opt = scan;
            break;
        }
    }

    const elem_index = elem_index_opt orelse {
        self.errorNote(start, .tensor_missing_arguments, .{}, null, .provide_element_type_last);
        self.sync(.eos);
        return error.UnexpectedToken;
    };

    const elem = items.items[elem_index];

    var dims: List(cst.ExprId) = .empty;
    defer dims.deinit(self.gpa);

    for (items.items, 0..) |expr_id, i| {
        if (i == elem_index) continue;
        try dims.append(self.gpa, expr_id);
    }

    const shape_range = self.cst_u.exprs.expr_pool.pushMany(self.gpa, dims.items);
    return self.addExpr(.TensorType, .{ .elem = elem, .shape = shape_range, .loc = self.toLocId(start) });
}

/// Parse an optional initializer expression following `=` or type annotations.
inline fn parseOptionalInitializer(self: *Parser, comptime mode: ParseMode) !cst.OptExprId {
    if (self.cur.tag != .equal) return .none();
    self.advance();
    return .some(try self.parseExpr(0, mode));
}

// Parse @[ ... ] into Attribute rows; return OptRangeAttr.
/// Parse optional attribute annotations attached to declarations.
fn parseOptionalAttributesRange(self: *Parser) !cst.OptRangeAttr {
    if (self.cur.tag != .at) return .none();

    try self.expect(.at);
    try self.expect(.lsquare);

    var ids: List(cst.AttributeId) = .empty;
    defer ids.deinit(self.gpa);

    while (self.cur.tag != .rsquare and self.cur.tag != .eof) {
        const tok = self.cur;
        const name_id: cst.StrId = if (tok.tag == .identifier) blk: {
            const name = self.intern(self.slice(tok));
            self.advance();
            break :blk name;
        } else if (Token.Tag.lexeme(tok.tag)) |lx| blk: {
            const name = self.intern(lx);
            self.advance();
            break :blk name;
        } else {
            self.errorNote(tok.loc, .expected_attribute_name, .{tok.tag}, tok.loc, .attribute_names_identifiers_or_keywords);
            self.sync(.rsquare);
            return error.UnexpectedToken;
        };

        var val: cst.OptExprId = .none();
        if (self.cur.tag == .equal) {
            self.advance();
            // Keep your original restriction (literal or ident) if you like;
            // or accept any expr. Here we accept any expr:
            val = .some(try self.parseExpr(0, .expr));
        }

        try ids.append(self.gpa, self.cst_u.exprs.addAttrRow(.{
            .name = name_id,
            .value = val,
            .loc = self.toLocId(tok.loc),
        }));

        if (!self.consumeIf(.comma)) break;
    }

    try self.expect(.rsquare);
    const range = self.cst_u.exprs.attr_pool.pushMany(self.gpa, ids.items);
    return .some(range);
}

//=================================================================
// Array-like / Map (type or literal) —
//=================================================================

/// Parse either a map literal or a map type beginning with `key_expr`.
fn parseMapTypeOrLiteral(self: *Parser, key_expr: cst.ExprId, start_loc: cst.LocId) !cst.ExprId {
    // caller consumed ":" already
    const value_expr = try self.parseExpr(0, .type);

    return switch (self.cur.tag) {
        .rsquare => blk: {
            try self.expect(.rsquare);
            // [K:V] => MapType
            break :blk self.addExpr(.MapType, .{
                .key = key_expr,
                .value = value_expr,
                .loc = start_loc,
            });
        },
        .comma => blk: {
            // literal form: [k:v, ...]
            self.advance();

            var kv_ids: List(cst.KeyValueId) = .empty;
            defer kv_ids.deinit(self.gpa);

            // first pair (we already parsed K:V)
            try kv_ids.append(self.gpa, self.cst_u.exprs.addKeyValue(.{
                .key = key_expr,
                .value = value_expr,
                .loc = start_loc,
            }));

            while (self.cur.tag != .rsquare and self.cur.tag != .eof) {
                const k = try self.parseExpr(0, .expr);
                try self.expect(.colon);
                const v = try self.parseExpr(0, .expr);
                try kv_ids.append(self.gpa, self.cst_u.exprs.addKeyValue(.{
                    .key = k,
                    .value = v,
                    .loc = self.toLocId(self.cur.loc),
                }));
                if (!self.consumeIf(.comma)) break;
            }
            try self.expect(.rsquare);

            const entries = self.cst_u.exprs.kv_pool.pushMany(self.gpa, kv_ids.items);
            break :blk self.addExpr(.MapLit, .{ .entries = entries, .loc = start_loc });
        },
        else => {
            self.errorNote(
                self.cur.loc,
                .expected_map_type_or_literal_continuation,
                .{self.cur.tag},
                null,
                .expected_map_type_or_literal_continuation_note,
            );
            self.sync(.eos);
            return error.UnexpectedToken;
        },
    };
}

/// Parse array, dynarray, or slice expressions/types depending on `mode`.
fn parseArrayLike(self: *Parser, comptime mode: ParseMode) !cst.ExprId {
    const lbrack_tok = self.cur;
    const start_loc = self.toLocId(lbrack_tok.loc);
    self.advance(); // "["

    return switch (self.cur.tag) {
        // "[]T" slice type OR "[]" empty array literal
        .rsquare => blk: {
            self.advance(); // "]"
            var slice_is_const = false;
            if (self.cur.tag == .keyword_const) {
                slice_is_const = true;
                self.advance();
            }
            const treat_as_type = slice_is_const or (mode == .type) or self.isTypeStart(self.cur.tag);
            if (treat_as_type) {
                const elem = try self.parseExpr(0, .type);
                break :blk self.addExpr(.SliceType, .{ .elem = elem, .is_const = slice_is_const, .loc = start_loc });
            } else {
                // [] => empty array literal in expression context
                break :blk self.addExpr(.ArrayLit, .{ .elems = .empty(), .trailing_comma = false, .loc = start_loc });
            }
        },

        // "[dyn]T" dynamic array type
        .keyword_dyn => blk: {
            self.advance();
            try self.expect(.rsquare);
            const elem = try self.parseExpr(0, .type);
            break :blk self.addExpr(.DynArrayType, .{ .elem = elem, .loc = start_loc });
        },

        // starts with expression -> could be:
        //   "[N]T" (ArrayType),
        //   "[K:V]" (MapType) / "[k:v, ...]" (MapLit),
        //   "[a, b, ...]" (ArrayLit)
        else => blk: {
            const first = try self.parseExpr(0, .expr);
            switch (self.cur.tag) {
                .rsquare => {
                    self.advance();
                    if (mode != .type and self.isTypeStart(self.cur.tag)) {
                        // [N]T in expression context → treat as array type
                        const elem = try self.parseExpr(0, .type);
                        break :blk self.addExpr(.ArrayType, .{ .elem = elem, .size = first, .loc = start_loc });
                    } else if (mode == .type) {
                        // [N]T in type context → array type
                        const elem = try self.parseExpr(0, .type);
                        break :blk self.addExpr(.ArrayType, .{ .elem = elem, .size = first, .loc = start_loc });
                    } else {
                        // [x] in expression context → single-element array literal
                        var items: List(cst.ExprId) = .empty;
                        defer items.deinit(self.gpa);
                        try items.append(self.gpa, first);
                        const elems = self.cst_u.exprs.expr_pool.pushMany(self.gpa, items.items);
                        break :blk self.addExpr(.ArrayLit, .{ .elems = elems, .trailing_comma = false, .loc = start_loc });
                    }
                },
                .colon => {
                    // map type or literal "[K:V]" or "[k:v, ...]"
                    self.advance(); // consume ":"
                    break :blk try self.parseMapTypeOrLiteral(first, start_loc);
                },
                .comma => {
                    // array literal "[a, b, ...]"
                    self.advance();

                    var items: List(cst.ExprId) = .empty;
                    defer items.deinit(self.gpa);

                    try items.append(self.gpa, first);
                    var trailing = false;
                    while (self.cur.tag != .rsquare and self.cur.tag != .eof) {
                        try items.append(self.gpa, try self.parseExpr(0, .expr));
                        if (!self.consumeIf(.comma)) {
                            trailing = false;
                            break;
                        }
                        trailing = true;
                    }
                    try self.expect(.rsquare);

                    const elems = self.cst_u.exprs.expr_pool.pushMany(self.gpa, items.items);
                    break :blk self.addExpr(.ArrayLit, .{ .elems = elems, .trailing_comma = trailing, .loc = start_loc });
                },
                else => {
                    self.errorNote(
                        self.cur.loc,
                        .expected_array_like_continuation,
                        .{self.cur.tag},
                        null,
                        .expected_array_type_or_literal_continuation,
                    );
                    self.sync(.eos);
                    return error.UnexpectedToken;
                },
            }
        },
    };
}

/// Parse a bracketed list of attributes and return their range.
fn parseAttributesList(self: *Parser) !cst.RangeOf(cst.AttributeId) {
    try self.expect(.at);
    try self.expect(.lsquare);

    var ids: List(cst.AttributeId) = .empty;
    defer ids.deinit(self.gpa);

    while (self.cur.tag != .rsquare and self.cur.tag != .eof) {
        const attr_loc_id = self.toLocId(self.cur.loc);

        // name: identifier or keyword-lexeme
        const tok = self.cur;
        var name_id: cst.StrId = undefined;
        if (tok.tag == .identifier) {
            name_id = self.intern(self.slice(tok));
            self.advance();
        } else if (Token.Tag.lexeme(tok.tag)) |lx| {
            name_id = self.intern(lx);
            self.advance();
        } else {
            self.errorNote(
                tok.loc,
                .expected_attribute_name,
                .{tok.tag},
                tok.loc,
                .attribute_names_identifiers_or_keywords,
            );
            self.sync(.rsquare);
            return error.UnexpectedToken;
        }

        // optional = value (only literal or ident allowed, same as original)
        var value_opt: cst.OptExprId = .none();
        if (self.cur.tag == .equal) {
            self.advance();
            const t = self.cur.tag;
            if (self.isLiteralTag(t) or t == .identifier) {
                const v = try self.parseExpr(0, .expr);
                value_opt = .some(v);
            } else {
                self.errorNote(
                    self.cur.loc,
                    .expected_attribute_value,
                    .{t},
                    self.cur.loc,
                    .attribute_values_literals_or_identifiers,
                );
                self.sync(.rsquare);
                return error.UnexpectedToken;
            }
        }

        try ids.append(self.gpa, self.cst_u.exprs.addAttrRow(.{
            .name = name_id,
            .value = value_opt,
            .loc = attr_loc_id,
        }));

        if (!self.consumeIf(.comma)) break;
    }

    try self.expect(.rsquare);

    return if (ids.items.len == 0)
        .empty()
    else
        self.cst_u.exprs.attr_pool.pushMany(self.gpa, ids.items);
}

/// Parse optional attributes (returning none when none present).
fn parseOptionalAttributes(self: *Parser) !cst.OptRangeAttr {
    if (self.cur.tag != .at) return .none();
    return .some(try self.parseAttributesList());
}

/// Parse an annotated expression (`@annot(...)` or similar metadata).
fn parseAnnotated(self: *Parser, comptime mode: ParseMode) !cst.ExprId {
    const some: cst.OptRangeAttr = .some(try self.parseAttributesList());
    while (self.cur.tag == .eos) self.advance();

    const id = try self.parseExpr(0, mode);
    const row = self.cst_u.exprs.index.rows.items[id.toRaw()];

    switch (self.cst_u.kind(id)) {
        .Function => self.cst_u.exprs.Function.col("attrs")[row] = some,
        .StructType => self.cst_u.exprs.StructType.col("attrs")[row] = some,
        .EnumType => self.cst_u.exprs.EnumType.col("attrs")[row] = some,
        .UnionType => self.cst_u.exprs.UnionType.col("attrs")[row] = some,
        else => {},
    }
    return id;
}

/// Parse a parenthesized expression, handling type tuples or grouping.
fn parseParenExpr(self: *Parser) !cst.ExprId {
    const loc = self.toLocId(self.cur.loc);
    self.advance(); // "("

    return switch (self.cur.tag) {
        .rparen => blk: {
            // empty tuple "()"
            self.advance();
            break :blk self.addExpr(.Tuple, .{ .elems = .empty(), .is_type = false, .loc = loc });
        },
        else => blk: {
            const first = try self.parseExpr(0, .expr);
            if (self.cur.tag == .comma) {
                self.advance();
                // tuple: (first, rest...)
                var items: List(cst.ExprId) = .empty;
                defer items.deinit(self.gpa);

                try items.append(self.gpa, first);
                while (self.cur.tag != .rparen and self.cur.tag != .eof) {
                    try items.append(self.gpa, try self.parseExpr(0, .expr));
                    if (!self.consumeIf(.comma)) break;
                }
                try self.expect(.rparen);

                const elems = self.cst_u.exprs.expr_pool.pushMany(self.gpa, items.items);
                break :blk self.addExpr(.Tuple, .{ .elems = elems, .is_type = false, .loc = loc });
            } else {
                // parenthesized expression: just return inner
                try self.expect(.rparen);
                break :blk self.addExpr(.Parenthesized, .{ .inner = first, .loc = loc });
            }
        },
    };
}

//=================================================================
// Functions (DOD)
//=================================================================

/// Parse optional return type annotation after function parameters.
inline fn parseOptionalReturnType(self: *Parser) !cst.OptExprId {
    if (self.cur.tag == .lcurly or self.cur.tag == .eos) return .none();
    return .some(try self.parseExpr(0, .type));
}

/// Parse an `extern` declaration attached to a function or variable.
fn parseExternDecl(self: *Parser) !cst.ExprId {
    self.advance(); // "extern"
    return switch (self.cur.tag) {
        .keyword_async => blk: {
            self.advance();
            if (self.cur.tag == .keyword_proc or self.cur.tag == .keyword_fn) {
                break :blk try self.parseFunctionLike(self.cur.tag, true, true);
            }
            self.errorNote(
                self.cur.loc,
                .expected_extern_async_function,
                .{self.cur.tag},
                null,
                .use_extern_async_proc_or_fn,
            );
            self.sync(.eos);
            return error.UnexpectedToken;
        },
        .keyword_proc, .keyword_fn => try self.parseFunctionLike(self.cur.tag, true, false),
        .keyword_struct => try self.parseStructLikeType(.keyword_struct, true),
        .keyword_enum => try self.parseEnumType(true),
        .keyword_union => try self.parseStructLikeType(.keyword_union, true),
        else => {
            self.errorNote(
                self.cur.loc,
                .expected_extern_declaration,
                .{self.cur.tag},
                null,
                .use_extern_proc_fn_or_type,
            );
            self.sync(.eos);
            return error.UnexpectedToken;
        },
    };
}

/// Parse a function or procedure declaration (optionally extern/async) identified by `tag`.
fn parseFunctionLike(self: *Parser, tag: Token.Tag, comptime is_extern: bool, is_async: bool) !cst.ExprId {
    const start_loc = self.toLocId(self.cur.loc);

    self.advance(); // "proc" or "fn"
    try self.expect(.lparen);

    var param_ids: List(cst.ParamId) = .empty;
    defer param_ids.deinit(self.gpa);

    var last_param_ty: cst.OptExprId = .none();
    var trailing_params = false;

    while (self.cur.tag != .rparen and self.cur.tag != .eof) {
        const attr_range = try self.parseOptionalAttributes(); // DOD: returns OptRangeAttr

        const param_loc = self.toLocId(self.cur.loc);
        const is_comptime = self.cur.tag == .keyword_comptime;
        if (is_comptime) self.advance();

        // Start by parsing something expr-like; it may be a pattern or a bare type.
        const pat_expr = try self.parseExpr(0, .expr);
        var pat_opt: cst.OptExprId = .some(pat_expr);
        var ty_opt: cst.OptExprId = .none();
        var val_opt: cst.OptExprId = .none();

        switch (self.cur.tag) {
            .colon => {
                // name: Type [= default]
                self.advance();
                const ty = try self.parseExpr(0, .type);
                ty_opt = .some(ty);
                if (self.cur.tag == .equal) {
                    self.advance();
                    const v = try self.parseExpr(0, .expr);
                    val_opt = .some(v);
                }
            },
            .comma, .rparen => {
                // Bare type param: treat the parsed node as the type, no pattern.
                ty_opt = .some(pat_expr);
                pat_opt = .none();
            },
            else => {
                self.errorNote(
                    self.cur.loc,
                    .expected_parameter_type_or_end,
                    .{self.cur.tag},
                    null,
                    .use_colon_for_type_or_comma_or_paren,
                );
                self.sync(.eos);
                return error.UnexpectedToken;
            },
        }

        // Remember the lcst param's type for variadic check.
        last_param_ty = ty_opt;

        const pid = self.cst_u.exprs.addParamRow(.{
            .pat = pat_opt,
            .ty = ty_opt,
            .value = val_opt,
            .attrs = attr_range,
            .is_comptime = is_comptime,
            .loc = param_loc,
        });
        try param_ids.append(self.gpa, pid);

        trailing_params = self.consumeIf(.comma);
        if (!trailing_params or self.cur.tag == .rparen) break;
    }
    try self.expect(.rparen);

    const result_ty = try self.parseOptionalReturnType();

    var body_opt: cst.OptExprId = .none();
    var raw_asm_opt: cst.OptStrId = .none();

    if (self.cur.tag == .lcurly) {
        const body_expr = try self.parseBlockExpr();
        body_opt = .some(body_expr);
    } else if (self.cur.tag == .keyword_asm) {
        self.advance(); // "asm"
        const tok = self.cur;
        try self.expect(.raw_asm_block);
        const raw = self.slice(tok);
        const s = self.intern(raw);
        raw_asm_opt = .some(s);
    }

    // Variadic if the lcst param type is `Any`.
    var is_variadic: bool = false;
    if (!last_param_ty.isNone()) {
        const lcst_ty = last_param_ty.unwrap();
        const k = self.cst_u.kind(lcst_ty);
        is_variadic = (k == .AnyType);
    }

    const params_range = if (param_ids.items.len == 0)
        cst.RangeOf(cst.ParamId).empty()
    else
        self.cst_u.exprs.param_pool.pushMany(self.gpa, param_ids.items);

    const flags = cst.Rows.FnFlags{
        .is_proc = (tag == .keyword_proc),
        .is_async = is_async,
        .is_variadic = is_variadic,
        .is_extern = is_extern,
        .is_test = false,
    };

    return self.addExpr(.Function, .{
        .params = params_range,
        .result_ty = result_ty,
        .body = body_opt,
        .raw_asm = raw_asm_opt,
        .attrs = .none(), // may be attached later via '@[...] <fn>'
        .flags = flags,
        .trailing_param_comma = trailing_params,
        .loc = start_loc,
    });
}

//=================================================================
// Metaprogramming (DOD)
//=================================================================

/// Parse a `comptime` block expression.
fn parseComptime(self: *Parser) !cst.ExprId {
    const loc = self.toLocId(self.cur.loc);
    self.advance(); // "comptime"
    if (self.cur.tag == .lcurly) {
        const blk = try self.parseBlockExpr();
        return self.addExpr(.Comptime, .{ .payload = blk, .is_block = true, .loc = loc });
    } else {
        const e = try self.parseExpr(0, .expr);
        return self.addExpr(.Comptime, .{ .payload = e, .is_block = false, .loc = loc });
    }
}

/// Parse a `code` block literal interpreted as raw code to embed.
fn parseCodeBlock(self: *Parser) !cst.ExprId {
    const loc = self.toLocId(self.cur.loc);
    self.advance(); // "code"
    const blk = try self.parseBlockExpr();
    return self.addExpr(.Code, .{ .block = blk, .loc = loc });
}

/// Parse an `insert` directive for macro-style code injection.
fn parseInsert(self: *Parser) !cst.ExprId {
    const loc = self.toLocId(self.cur.loc);
    self.advance(); // "insert"
    const e = try self.parseExpr(0, .expr);
    return self.addExpr(.Insert, .{ .expr = e, .loc = loc });
}

/// Parse an MLIR block literal embedded inside SR source.
fn parseMlir(self: *Parser) !cst.ExprId {
    self.advance(); // "mlir"

    var result_ty: cst.OptExprId = .none();
    var kind: cst.MlirKind = .Module;
    if (self.cur.tag == .identifier) {
        const kw = self.slice(self.cur);
        if (std.mem.eql(u8, kw, "attribute")) {
            kind = .Attribute;
            self.advance();
        } else if (std.mem.eql(u8, kw, "op") or std.mem.eql(u8, kw, "operation")) {
            kind = .Operation;
            self.advance();
        }
    } else if (self.cur.tag == .keyword_type) {
        kind = .Type;
        self.advance();
    }

    var args_range = cst.OptRangeOf(cst.ExprId).none();
    if (self.cur.tag == .lparen) {
        self.advance();
        args_range = .some((try self.parseCommaExprListUntil(.rparen)).range);
    }

    const lcurly_tok = self.cur;
    const file_id = lcurly_tok.loc.file_id;

    if (kind == .Operation and self.cur.tag == .colon) {
        self.advance();
        const t = try self.parseExpr(0, .type);
        result_ty = .some(t);
    }

    if (self.cur.tag == .lcurly) self.advance() else try self.expect(.lcurly);
    const start_index = self.cur.loc.start;
    var depth: usize = 1;
    var end_index: usize = start_index; // will be set when we see the matching '}'
    while (depth > 0) {
        switch (self.cur.tag) {
            .eof => {
                try self.expect(.rcurly);
                unreachable;
            },
            .lcurly => {
                depth += 1;
                self.advance();
            },
            .rcurly => {
                depth -= 1;
                end_index = self.cur.loc.end; // include the closing brace
                self.advance(); // consume '}'
                // If depth == 0, we break after consuming the matching '}'.
            },
            else => self.advance(),
        }
    }

    const mlir_loc: Loc = .{ .file_id = file_id, .start = start_index, .end = end_index - 1 };
    const raw_text = self.src[start_index .. end_index - 1];
    const text = self.intern(raw_text);

    const pieces_range = try self.buildMlirPieces(raw_text);
    return self.addExpr(.Mlir, .{
        .kind = kind,
        .text = text,
        .pieces = pieces_range,
        .args = args_range,
        .result_ty = result_ty,
        .loc = self.toLocId(mlir_loc),
    });
}

fn buildMlirPieces(self: *Parser, raw_text: []const u8) !cst.RangeOf(cst.MlirPieceId) {
    var piece_ids = std.ArrayListUnmanaged(cst.MlirPieceId){};
    defer piece_ids.deinit(self.gpa);

    const addPiece = struct {
        fn call(p: *Parser, list: *std.ArrayListUnmanaged(cst.MlirPieceId), kind: cst.MlirPieceKind, text: []const u8) void {
            const pid = p.cst_u.exprs.addMlirPieceRow(.{ .kind = kind, .text = p.intern(text) });
            list.append(p.gpa, pid) catch @panic("OOM");
        }
    }.call;

    var literal_start: usize = 0;
    var i: usize = 0;
    while (i < raw_text.len) {
        // Backtick-delimited splice: `Ident`
        if (raw_text[i] == '`') {
            // Flush any preceding literal chunk first.
            if (i > literal_start) addPiece(self, &piece_ids, .literal, raw_text[literal_start..i]);

            const closing = std.mem.indexOfScalarPos(u8, raw_text, i + 1, '`') orelse {
                // No closing backtick; treat the single backtick as literal.
                addPiece(self, &piece_ids, .literal, raw_text[i .. i + 1]);
                i += 1;
                literal_start = i;
                continue;
            };

            const ident_text = raw_text[(i + 1)..closing];
            // Only treat as splice if the content is a valid identifier.
            var is_ident = ident_text.len > 0 and isIdentStart(ident_text[0]);
            if (is_ident) {
                var k: usize = 1;
                while (k < ident_text.len) : (k += 1) {
                    if (!isIdentContinue(ident_text[k])) {
                        is_ident = false;
                        break;
                    }
                }
            }

            if (is_ident) {
                addPiece(self, &piece_ids, .splice, ident_text);
                // Resume scanning after the closing backtick.
                literal_start = closing + 1;
                i = closing + 1;
                continue;
            } else {
                // Not a valid identifier — emit the whole backtick pair as literal.
                addPiece(self, &piece_ids, .literal, raw_text[i .. closing + 1]);
                i = closing + 1;
                literal_start = i;
                continue;
            }
        }
        i += 1;
    }

    if (literal_start < raw_text.len) {
        addPiece(self, &piece_ids, .literal, raw_text[literal_start..]);
    }

    if (piece_ids.items.len == 0) {
        addPiece(self, &piece_ids, .literal, "");
    }

    return self.cst_u.exprs.mlir_piece_pool.pushMany(self.gpa, piece_ids.items);
}

/// Return true if `ch` is valid as the first character of an identifier.
fn isIdentStart(ch: u8) bool {
    return ch == '_' or std.ascii.isAlphabetic(ch);
}

/// Return true if `ch` can appear after the first character of an identifier.
fn isIdentContinue(ch: u8) bool {
    return ch == '_' or std.ascii.isAlphanumeric(ch);
}

//=================================================================
// Enums / Variants
//=================================================================

/// Parse an `enum` type declaration, possibly marked `extern`.
inline fn parseEnumType(self: *Parser, comptime is_extern: bool) !cst.ExprId {
    const start_loc = self.toLocId(self.cur.loc);
    self.advance(); // "enum"

    var backing: cst.OptExprId = .none();
    if (self.cur.tag == .lparen) {
        self.advance();
        const b = try self.parseExpr(0, .type);
        backing = .some(b);
        try self.expect(.rparen);
    }

    try self.expect(.lcurly);

    var field_ids: List(cst.EnumFieldId) = .empty;
    defer field_ids.deinit(self.gpa);

    var trailing = false;
    while (self.cur.tag != .rcurly and self.cur.tag != .eof) {
        const f_loc = self.toLocId(self.cur.loc);
        const attrs = try self.parseOptionalAttributes(); // OptRangeAttr
        const tok = self.cur;
        try self.expect(.identifier);
        const name_id = self.intern(self.slice(tok));
        const val = try self.parseOptionalInitializer(.expr);

        try field_ids.append(self.gpa, self.cst_u.exprs.addEnumFieldRow(.{
            .name = name_id,
            .value = val,
            .attrs = attrs,
            .loc = f_loc,
        }));

        trailing = self.consumeIf(.comma);
        if (!trailing) break;
        if (self.cur.tag == .rcurly) break;
    }

    try self.expect(.rcurly);

    const fields_range = if (field_ids.items.len == 0)
        cst.RangeOf(cst.EnumFieldId).empty()
    else
        self.cst_u.exprs.efield_pool.pushMany(self.gpa, field_ids.items);

    return self.addExpr(.EnumType, .{
        .fields = fields_range,
        .discriminant = backing,
        .is_extern = is_extern,
        .attrs = .none(), // attach via '@' before if needed
        .trailing_field_comma = trailing,
        .loc = start_loc,
    });
}

/// Parse an `error` type declaration.
inline fn parseErrorType(self: *Parser) !cst.ExprId {
    return self.parseVariantLikeType(true);
}

/// Parse a `variant` type declaration.
inline fn parseVariantType(self: *Parser) !cst.ExprId {
    return self.parseVariantLikeType(false);
}

/// Parse a variant-like or error type depending on `is_error`.
fn parseVariantLikeType(self: *Parser, comptime is_error: bool) !cst.ExprId {
    const start_loc = self.toLocId(self.cur.loc);
    self.advance(); // "variant"
    try self.expect(.lcurly);

    var vfield_ids: List(cst.VariantFieldId) = .empty;
    defer vfield_ids.deinit(self.gpa);

    var trailing = false;
    while (self.cur.tag != .rcurly and self.cur.tag != .eof) {
        const case_loc = self.toLocId(self.cur.loc);
        const attrs = try self.parseOptionalAttributes(); // OptRangeAttr
        while (self.cur.tag == .eos) self.advance();

        const nm_tok = self.cur;
        try self.expect(.identifier);
        const nm = self.slice(nm_tok);
        const name_id = self.intern(nm);

        var row = cst.Rows.VariantField{
            .name = name_id,
            .ty_tag = .none,
            .tuple_elems = .empty(),
            .struct_fields = .empty(),
            .value = .none(),
            .attrs = attrs,
            .tuple_trailing_comma = false,
            .struct_trailing_comma = false,
            .loc = case_loc,
        };

        switch (self.cur.tag) {
            .lparen => {
                // Tuple-like payload
                self.advance();
                var elems: List(cst.ExprId) = .empty;
                defer elems.deinit(self.gpa);

                if (self.cur.tag != .rparen) {
                    while (true) {
                        try elems.append(self.gpa, try self.parseExpr(0, .type));
                        if (!self.consumeIf(.comma)) break;
                        row.tuple_trailing_comma = true;
                        if (self.cur.tag == .rparen) break;
                    }
                }
                try self.expect(.rparen);

                row.ty_tag = .Tuple;
                row.value = try self.parseOptionalInitializer(.expr);
                row.tuple_elems = if (elems.items.len == 0)
                    cst.RangeOf(cst.ExprId).empty()
                else
                    self.cst_u.exprs.expr_pool.pushMany(self.gpa, elems.items);
            },
            .lcurly => {
                // Struct-like payload
                self.advance();
                const struct_fields = try self.parseStructFieldList(.rcurly); // returns RangeOf(StructFieldId)
                row.ty_tag = .Struct;
                row.struct_fields = struct_fields.range;
                row.struct_trailing_comma = struct_fields.trailing;
                row.value = try self.parseOptionalInitializer(.expr);
            },
            else => {
                // No payload
                row.value = try self.parseOptionalInitializer(.expr);
            },
        }

        try vfield_ids.append(self.gpa, self.cst_u.exprs.addVariantFieldRow(row));

        if (!self.consumeIf(.comma)) {
            trailing = false;
            break;
        }
        trailing = true;
    }

    try self.expect(.rcurly);

    const fields = if (vfield_ids.items.len == 0)
        cst.RangeOf(cst.VariantFieldId).empty()
    else
        self.cst_u.exprs.vfield_pool.pushMany(self.gpa, vfield_ids.items);

    if (is_error) {
        return self.addExpr(.ErrorType, .{ .fields = fields, .trailing_field_comma = trailing, .loc = start_loc });
    }
    return self.addExpr(.VariantLikeType, .{ .fields = fields, .trailing_field_comma = trailing, .loc = start_loc });
}
