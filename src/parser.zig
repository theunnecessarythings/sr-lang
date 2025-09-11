const std = @import("std");
const Lexer = @import("lexer.zig").Tokenizer;
const Token = @import("lexer.zig").Token;
const Loc = Token.Loc;
const cst = @import("cst.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;

pub const Parser = struct {
    allocator: std.mem.Allocator,
    source: []const u8,
    lexer: Lexer,
    current_token: Token,
    next_token: Token,
    diags: *Diagnostics,

    const ParseMode = enum { expr, type, expr_no_struct };

    pub fn init(allocator: std.mem.Allocator, source: [:0]const u8, diags: *Diagnostics) Parser {
        var lexer = Lexer.init(source);
        const current_token = lexer.next();
        const next_token = lexer.next();
        return .{ .allocator = allocator, .source = source, .lexer = lexer, .current_token = current_token, .next_token = next_token, .diags = diags };
    }

    //=================================================================
    // Utilities
    //=================================================================

    inline fn advance(self: *Parser) void {
        self.current_token = self.next_token;
        self.next_token = self.lexer.next();
    }

    inline fn list(self: *const Parser, comptime T: type) std.array_list.Managed(T) {
        return std.array_list.Managed(T).init(self.allocator);
    }

    inline fn consumeIf(self: *Parser, tag: Token.Tag) bool {
        if (self.current_token.tag == tag) {
            self.advance();
            return true;
        }
        return false;
    }

    inline fn expect(self: *Parser, tag: Token.Tag) !void {
        if (self.current_token.tag != tag) {
            self.errorNote(self.current_token.loc, "expected {s}, found {s}", .{ Token.Tag.symbol(tag), Token.Tag.symbol(self.current_token.tag) }, self.current_token.loc, "unexpected token here", .{});
            return error.UnexpectedToken;
        }
        self.advance();
    }

    inline fn current(self: *const Parser) Token {
        return self.current_token;
    }

    inline fn peek(self: *const Parser) Token {
        return self.next_token;
    }

    inline fn currentLoc(self: *const Parser) Loc {
        return self.current_token.loc;
    }

    inline fn slice(self: *const Parser, token: Token) []const u8 {
        return self.source[token.loc.start..token.loc.end];
    }

    inline fn alloc(self: *Parser, comptime T: type, value: T) !*T {
        const ptr = try self.allocator.create(T);
        ptr.* = value;
        return ptr;
    }

    //=================================================================
    // Diagnostics helpers
    //=================================================================

    inline fn errorNote(
        self: *Parser,
        loc: Loc,
        comptime fmt: []const u8,
        args: anytype,
        note_loc: ?Loc,
        comptime note_fmt: []const u8,
        note_args: anytype,
    ) void {
        const before = self.diags.count();
        _ = self.diags.addError(loc, fmt, args) catch {};
        if (self.diags.count() > before) {
            const idx = self.diags.count() - 1;
            _ = self.diags.attachNote(idx, note_loc, note_fmt, note_args) catch {};
        }
    }

    inline fn isStmtTerminator(self: *const Parser) bool {
        return switch (self.current().tag) {
            .eos, .rcurly, .eof => true,
            else => false,
        };
    }

    const Name = struct { bytes: []const u8, loc: Loc };

    inline fn expectIdent(self: *Parser) !Name {
        const tok = self.current();
        try self.expect(.identifier);
        return .{ .bytes = self.slice(tok), .loc = tok.loc };
    }

    inline fn isUnderscore(self: *Parser) bool {
        return self.current().tag == .identifier and std.mem.eql(u8, self.slice(self.current()), "_");
    }

    inline fn parseOptionalInitializer(self: *Parser, comptime mode: ParseMode) !?*cst.Expr {
        if (self.current().tag == .eq) {
            self.advance();
            return try self.parseExpr(0, mode);
        }
        return null;
    }

    inline fn beginKeywordParen(self: *Parser, comptime tag: Token.Tag) !Loc {
        const start = self.currentLoc();
        try self.expect(tag);
        try self.expect(.lparen);
        return start;
    }

    fn parseAttributesList(self: *Parser) !std.array_list.Managed(cst.Attribute) {
        var attrs = self.list(cst.Attribute);
        try self.expect(.at);
        try self.expect(.lsquare);
        while (self.current().tag != .rsquare and self.current().tag != .eof) {
            const attr_loc = self.currentLoc();
            // attribute name can be an identifier or a keyword name like 'align'
            var name_bytes: []const u8 = undefined;
            const tok = self.current();
            if (tok.tag == .identifier) {
                name_bytes = self.slice(tok);
                self.advance();
            } else if (Token.Tag.lexeme(tok.tag)) |lx| {
                name_bytes = lx;
                self.advance();
            } else {
                self.errorNote(tok.loc, "expected attribute name, found {s}", .{Token.Tag.symbol(tok.tag)}, tok.loc, "attribute names can be identifiers or keywords", .{});
                return error.UnexpectedToken;
            }
            var val: ?*cst.Expr = null;
            if (self.current().tag == .eq) {
                self.advance();
                // Only literals or identifiers are allowed
                const t = self.current().tag;
                if (isLiteralTag(t) or t == .identifier) {
                    val = try self.parseExpr(0, .expr);
                } else {
                    self.errorNote(
                        self.currentLoc(),
                        "expected literal or identifier after '=', found {s}",
                        .{Token.Tag.symbol(t)},
                        self.currentLoc(),
                        "attribute values must be literals or identifiers",
                        .{},
                    );
                    return error.UnexpectedToken;
                }
            }
            try attrs.append(.{ .name = name_bytes, .value = val, .loc = attr_loc });
            if (!self.consumeIf(.comma)) break;
        }
        try self.expect(.rsquare);
        return attrs;
    }

    fn parseOptionalAttributes(self: *Parser) !?std.array_list.Managed(cst.Attribute) {
        if (self.current().tag == .at) {
            return try self.parseAttributesList();
        }
        return null;
    }

    inline fn endParen(self: *Parser) !void {
        try self.expect(.rparen);
    }

    inline fn beginBrace(self: *Parser) !Loc {
        const start = self.currentLoc();
        try self.expect(.lcurly);
        return start;
    }

    inline fn endBrace(self: *Parser) !void {
        try self.expect(.rcurly);
    }

    inline fn isLiteralTag(tag: Token.Tag) bool {
        return switch (tag) {
            .char_literal, .string_literal, .raw_string_literal, .byte_literal, .byte_char_literal, .byte_string_literal, .raw_byte_string_literal, .raw_asm_block, .integer_literal, .float_literal, .imaginary_literal, .keyword_true, .keyword_false => true,
            else => false,
        };
    }

    inline fn nextIsTerminator(self: *const Parser) bool {
        return switch (self.peek().tag) {
            .comma, .rsquare, .rparen, .rcurly, .eos, .eof => true,
            else => false,
        };
    }

    inline fn toPrefixOp(tag: Token.Tag) cst.PrefixOp {
        return switch (tag) {
            .plus => .plus,
            .minus => .minus,
            .b_and => .address_of,
            .bang => .logical_not,
            .dotdot => .range,
            .dotdoteq => .range_inclusive,
            else => unreachable,
        };
    }

    inline fn infixBp(tag: Token.Tag) ?struct { u8, u8 } {
        return switch (tag) {
            .star, .slash, .percent, .star_pipe, .star_percent => .{ 80, 81 },
            .plus, .plus_pipe, .plus_percent, .minus, .minus_percent, .minus_pipe => .{ 70, 71 },
            .shl, .shr, .shl_pipe => .{ 60, 61 },
            .lt, .le, .gt, .ge => .{ 50, 51 },
            .eqeq, .ne => .{ 45, 46 },
            .b_and => .{ 40, 41 },
            .caret => .{ 35, 36 },
            .b_or => .{ 30, 31 },
            .dotdot, .dotdoteq => .{ 27, 28 },
            .keyword_and => .{ 25, 26 },
            .keyword_or => .{ 20, 21 },
            .bang => .{ 15, 16 }, // for error union
            .keyword_orelse => .{ 12, 11 },
            .plus_equal,
            .minus_equal,
            .star_equal,
            .slash_equal,
            .percent_equal,
            .shl_equal,
            .shr_equal,
            .and_equal,
            .or_equal,
            .caret_equal,
            .star_pipe_equal,
            .plus_pipe_equal,
            .minus_pipe_equal,
            .shl_pipe_equal,
            .star_percent_equal,
            .plus_percent_equal,
            .minus_percent_equal,
            => .{ 10, 9 },
            else => null,
        };
    }

    inline fn postfixBp(tag: Token.Tag) ?u8 {
        return switch (tag) {
            .lparen,
            .lsquare,
            .lcurly,
            .dot,
            .dot_lparen,
            .dotdot,
            .dotstar,
            .dotdoteq,
            .bang,
            .question,
            .keyword_catch,
            => 95,
            else => null,
        };
    }

    inline fn prefixBp(tag: Token.Tag) u8 {
        return switch (tag) {
            .plus, .minus, .b_and, .star, .question, .bang, .dotdot, .dotdoteq => 90,
            else => unreachable,
        };
    }

    fn looksLikeCtorHead(self: *Parser, expr: *cst.Expr) bool {
        return switch (expr.*) {
            // Type names and qualified paths: Foo{...}, pkg.Foo{...}, Event.Click{...}
            .Ident, .Field => true,
            // Generic/type-function: List(u8){...}, map[string]{} — allow, recurse on the *head*
            .Call => self.looksLikeCtorHead(expr.Call.callee),
            // Indexed type heads: Vec[3]{...}, Matrix[m,n]{...}
            .Index => self.looksLikeCtorHead(expr.Index.collection),
            // Parenthesized type heads if you ever wrap them
            .Tuple => expr.Tuple.elems.items.len == 1 and self.looksLikeCtorHead(expr.Tuple.elems.items[0]),
            else => false,
        };
    }

    //=================================================================
    // Parsing
    //=================================================================

    fn syncToStmtBoundary(self: *Parser) void {
        while (self.current().tag != .eos and self.current().tag != .rcurly and self.current().tag != .eof) {
            self.advance();
        }
        if (self.current().tag == .eos) self.advance();
    }

    pub fn parse(self: *Parser) !cst.Program {
        var decls = self.list(cst.Decl);
        var pkg_decl: ?cst.PackageDecl = null;
        if (self.current_token.tag == .keyword_package) {
            pkg_decl = self.parsePackageDecl() catch blk: {
                // Assume a more specific diagnostic was already added at the error site
                self.syncToStmtBoundary();
                break :blk null;
            };
        }
        while (self.current_token.tag != .eof) {
            const decl = self.parseDecl() catch {
                // Assume a more specific diagnostic was already added at the error site
                self.syncToStmtBoundary();
                continue;
            };
            try decls.append(decl);
        }
        return .{ .decls = decls, .package = pkg_decl };
    }

    fn parsePackageDecl(self: *Parser) !cst.PackageDecl {
        const loc = self.currentLoc();
        try self.expect(.keyword_package);
        const name = try self.expectIdent();
        try self.expect(.eos);
        return .{ .name = name.bytes, .loc = loc };
    }

    fn parseDecl(self: *Parser) anyerror!cst.Decl {
        const loc = self.currentLoc();
        const lhs = try self.parseExpr(0, .expr);
        var is_const = false;
        var ty: ?*cst.Expr = null;
        var is_assign = false;

        switch (self.current().tag) {
            .coloncolon => {
                self.advance();
                is_const = true;
            },
            .coloneq => {
                self.advance();
            },
            .colon => {
                // Special case: labeled loop like "label: for/while ... { ... }"
                const next = self.peek().tag;
                if (lhs.* == .Ident and (next == .keyword_for or next == .keyword_while)) {
                    const label_name = lhs.Ident.name;
                    self.advance(); // consume ':'
                    const loop_expr = try self.parseLabeledLoop(label_name);
                    if (self.current().tag != .rcurly and self.current().tag != .eof) {
                        try self.expect(.eos);
                    }
                    return .{ .lhs = null, .rhs = loop_expr, .ty = null, .loc = loc, .is_const = false, .is_assign = false };
                } else {
                    self.advance();
                    ty = try self.parseExpr(0, .type);
                    switch (self.current().tag) {
                        .eq => self.advance(),
                        .colon => {
                            self.advance();
                            is_const = true;
                        },
                        else => {
                            const unexpected_tok = self.current();
                            self.errorNote(self.currentLoc(), "expected '=' or '::' after type in declaration, found {s}", .{Token.Tag.symbol(unexpected_tok.tag)}, unexpected_tok.loc, "did you mean '=' before the initializer?", .{});
                            return error.UnexpectedToken;
                        },
                    }
                }
            },
            .eq => {
                self.advance();
                is_assign = true;
            },
            .eos => {
                self.advance();
                return .{ .lhs = null, .rhs = lhs, .ty = null, .loc = loc, .is_const = false, .is_assign = false };
            },
            .rcurly => {
                return .{ .lhs = null, .rhs = lhs, .ty = null, .loc = loc, .is_const = false, .is_assign = false };
            },
            else => {
                const got = self.current();
                self.errorNote(self.currentLoc(), "expected '::' or '=' after lhs in declaration, found {s}", .{Token.Tag.symbol(got.tag)}, got.loc, "use '::' for constants, '=' to assign or initialize variables", .{});
                return error.UnexpectedToken;
            },
        }

        const rhs = try self.parseExpr(0, .expr);
        if (self.current().tag != .rcurly and self.current().tag != .eof) {
            try self.expect(.eos);
        }
        return .{ .lhs = lhs, .rhs = rhs, .ty = ty, .loc = loc, .is_const = is_const, .is_assign = is_assign };
    }

    fn nud(self: *Parser, tag: Token.Tag, comptime mode: ParseMode) anyerror!*cst.Expr {
        // prefix
        switch (tag) {
            .plus, .minus, .b_and, .bang, .dotdot, .dotdoteq => {
                // Capture operator info up-front to avoid mutation by recursive parse
                const op_loc = self.currentLoc();
                const op_kind = toPrefixOp(tag);
                self.advance();
                const rhs = try self.parseExpr(prefixBp(tag), mode);
                const unary = cst.Prefix{ .op = op_kind, .right = rhs, .loc = op_loc };
                return try self.alloc(cst.Expr, .{ .Prefix = unary });
            },
            .b_or => return try self.parseClosure(),
            .keyword_comptime => return try self.parseComptime(),
            .keyword_code => return try self.parseCodeBlock(),
            .keyword_mlir => return try self.parseMlir(),
            .keyword_insert => return try self.parseInsert(),
            else => {},
        }

        // literal
        if (isLiteralTag(tag)) {
            const literal = cst.Literal{ .value = self.slice(self.current()), .loc = self.currentLoc(), .kind = tag };
            self.advance();
            return try self.alloc(cst.Expr, .{ .Literal = literal });
        }

        // others
        return switch (tag) {
            .star => try self.parsePointerType(),
            .question => try self.parseOptionalType(),
            .at => blk: {
                // Attributes preceding a construct
                const attrs = try self.parseAttributesList();
                // Allow optional EOS/newlines between attrs and the annotated construct
                while (self.current().tag == .eos) self.advance();
                // Parse the next expression and attach attributes where applicable
                const annotated = try self.parseExpr(0, mode);
                switch (annotated.*) {
                    .Function => |*fnn| fnn.attrs = attrs,
                    .BuiltinType => |*bt| switch (bt.*) {
                        .Struct => |*st| st.attrs = attrs,
                        .Union => |*un| un.attrs = attrs,
                        .Enum => |*en| en.attrs = attrs,
                        else => {},
                    },
                    else => {},
                }
                break :blk annotated;
            },
            .identifier => blk: {
                const ident = cst.Ident{ .name = self.slice(self.current()), .loc = self.currentLoc() };
                self.advance();
                break :blk try self.alloc(cst.Expr, .{ .Ident = ident });
            },
            .lsquare => try self.parseArrayLike(),
            .lparen => try self.parseParenExpr(),
            .lcurly => try self.parseBlockExpr(),
            .keyword_proc, .keyword_fn => try self.parseFunctionLike(self.current().tag, false, false),
            .keyword_extern => try self.parseExternDecl(),
            .keyword_any => blk: {
                const any_type = cst.AnyType{ .loc = self.currentLoc() };
                self.advance();
                break :blk try self.alloc(cst.Expr, .{ .BuiltinType = .{ .Any = any_type } });
            },
            .keyword_type => blk: {
                const type_type = cst.TypeType{ .loc = self.currentLoc() };
                self.advance();
                break :blk try self.alloc(cst.Expr, .{ .BuiltinType = .{ .Type = type_type } });
            },
            .keyword_noreturn => blk: {
                const noreturn_type = cst.NoreturnType{ .loc = self.currentLoc() };
                self.advance();
                break :blk try self.alloc(cst.Expr, .{ .BuiltinType = .{ .Noreturn = noreturn_type } });
            },
            .keyword_complex => try self.parseComplexType(),
            .keyword_simd => try self.parseSimdType(),
            .keyword_tensor => try self.parseTensorType(),
            .keyword_struct => try self.parseStructLikeType(.keyword_struct, false),
            .keyword_union => try self.parseStructLikeType(.keyword_union, false),
            .keyword_enum => try self.parseEnumType(false),
            .keyword_variant => try self.parseVariantType(),
            .keyword_error => try self.parseErrorType(),
            .keyword_return => try self.parseReturn(),
            .keyword_import => blk: {
                const loc = self.currentLoc();
                self.advance(); // "import"
                const expr = try self.parseExpr(0, .expr);
                break :blk try self.alloc(cst.Expr, .{ .Import = .{ .expr = expr, .loc = loc } });
            },
            .keyword_typeof => blk: {
                const start = try self.beginKeywordParen(.keyword_typeof);
                const expr = try self.parseExpr(0, .expr);
                try self.endParen();
                break :blk try self.alloc(cst.Expr, .{ .TypeOf = .{ .expr = expr, .loc = start } });
            },
            .keyword_async => blk: {
                const loc = self.currentLoc();
                self.advance(); // "async"
                switch (self.current().tag) {
                    .keyword_proc, .keyword_fn => break :blk try self.parseFunctionLike(self.current().tag, false, true),
                    else => {
                        const body = try self.parseBlockExpr();
                        break :blk try self.alloc(cst.Expr, .{ .Async = .{ .body = body, .loc = loc } });
                    },
                }
            },
            .keyword_if => try self.parseIfExpr(),
            .keyword_while => try self.parseWhileExpr(),
            .keyword_match => try self.parseMatchExpr(),
            .keyword_for => try self.parseForExpr(),
            .keyword_break => blk: {
                const break_token = self.current();
                self.advance();
                var label: ?[]const u8 = null;
                var value: ?*cst.Expr = null;
                if (self.current().tag == .colon) {
                    self.advance();
                    const name = try self.expectIdent();
                    label = name.bytes;
                }
                if (!self.isStmtTerminator()) {
                    value = try self.parseExpr(0, .expr);
                }
                const break_expr = cst.Break{ .loc = break_token.loc, .label = label, .value = value };
                break :blk try self.alloc(cst.Expr, .{ .Break = break_expr });
            },
            .keyword_continue => blk: {
                const continue_token = self.current();
                self.advance();
                const continue_expr = cst.Continue{ .loc = continue_token.loc };
                break :blk try self.alloc(cst.Expr, .{ .Continue = continue_expr });
            },
            .keyword_unreachable => blk: {
                const unreachable_token = self.current();
                self.advance();
                const unreachable_expr = cst.Unreachable{ .loc = unreachable_token.loc };
                break :blk try self.alloc(cst.Expr, .{ .Unreachable = unreachable_expr });
            },
            .keyword_null => blk: {
                const null_token = self.current();
                self.advance();
                const null_expr = cst.Null{ .loc = null_token.loc };
                break :blk try self.alloc(cst.Expr, .{ .Null = null_expr });
            },
            .keyword_defer => blk: {
                const defer_token = self.current();
                self.advance();
                const deferred = try self.parseExpr(0, .expr);
                const defer_expr = cst.Defer{ .expr = deferred, .loc = defer_token.loc };
                break :blk try self.alloc(cst.Expr, .{ .Defer = defer_expr });
            },
            .keyword_errdefer => blk: {
                const errdefer_token = self.current();
                self.advance();
                const deferred = try self.parseExpr(0, .expr);
                const errdefer_expr = cst.ErrDefer{ .expr = deferred, .loc = errdefer_token.loc };
                break :blk try self.alloc(cst.Expr, .{ .ErrDefer = errdefer_expr });
            },
            else => {
                const got = self.current();
                self.errorNote(self.currentLoc(), "unexpected token in expression: {s}", .{Token.Tag.symbol(tag)}, got.loc, "this token cannot start or continue an expression here", .{});
                return error.UnexpectedToken;
            },
        };
    }

    inline fn toInfixOp(tag: Token.Tag) cst.InfixOp {
        return switch (tag) {
            .plus => .add,
            .minus => .sub,
            .star => .mul,
            .slash => .div,
            .percent => .mod,
            .shl => .shl,
            .shr => .shr,
            .star_pipe => .mul_sat,
            .plus_pipe => .add_sat,
            .minus_pipe => .sub_sat,
            .shl_pipe => .shl_sat,
            .star_percent => .mul_wrap,
            .plus_percent => .add_wrap,
            .minus_percent => .sub_wrap,
            .lt => .lt,
            .le => .lte,
            .gt => .gt,
            .ge => .gte,
            .eqeq => .eq,
            .ne => .neq,
            .b_and => .b_and,
            .caret => .b_xor,
            .b_or => .b_or,
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

    fn parseExpr(self: *Parser, min_bp: u8, comptime mode: ParseMode) !*cst.Expr {
        var left = try self.nud(self.current().tag, mode);

        while (true) {
            const tag = self.current().tag;

            // ---------- Postfix ----------
            if (postfixBp(tag)) |l_bp| {
                // never treat '!' as postfix in type context
                if (tag == .bang and mode == .type) {
                    // skip; might be infix type operator
                } else if (l_bp >= min_bp) {
                    // block struct-literal when not allowed
                    if (tag == .lcurly and (mode == .type or mode == .expr_no_struct)) break;
                    if (tag == .lcurly and !self.looksLikeCtorHead(left)) break;

                    // SPECIAL-CASE: for '!' in expr modes, always take postfix unwrap.
                    if (tag == .bang and mode != .type) {
                        const loc = self.currentLoc();
                        self.advance();
                        left = try self.alloc(cst.Expr, .{ .ErrUnwrap = .{ .expr = left, .loc = loc } });
                        continue;
                    }

                    // Range postfix still defers to infix when it’s actually x..y or x..=y
                    const prefer_postfix_for_range = (tag == .dotdot or tag == .dotdoteq);
                    const should_let_infix_win = prefer_postfix_for_range and !self.nextIsTerminator();

                    if (!should_let_infix_win) {
                        self.advance();
                        left = switch (tag) {
                            .lparen => try self.parseCall(left),
                            .lsquare => try self.parseIndex(left),
                            .dot => try self.parsePostfixAfterDot(left),
                            .dot_lparen => try self.parseCastParen(left),
                            .lcurly => try self.parseStructLiteral(),
                            .dotstar => try self.parseDeref(left),
                            .question => try self.parseOptionalUnwrap(left),
                            .keyword_catch => try self.parseCatchExpr(left),
                            else => {
                                const got = self.current();
                                self.errorNote(self.currentLoc(), "unexpected postfix operator: {s}", .{Token.Tag.symbol(tag)}, got.loc, "this operator cannot be used here", .{});
                                return error.UnexpectedToken;
                            },
                        };
                        continue;
                    }
                }
            }

            // ---------- Infix ----------
            if (infixBp(tag)) |bp| {
                // Only allow infix '!' in *type* mode (error-union like `T ! E`)
                if (tag == .bang and mode != .type) break;

                const l_bp, const r_bp = bp;
                if (l_bp < min_bp) break;

                const loc = self.currentLoc();
                self.advance();
                const right = try self.parseExpr(r_bp, mode);
                left = try self.alloc(cst.Expr, .{ .Infix = .{ .op = toInfixOp(tag), .left = left, .right = right, .loc = loc } });
                continue;
            }

            break;
        }
        // Debug log removed for cleaner output
        return left;
    }

    //=================================================================
    // Common element parsers
    //=================================================================

    fn parseStructLiteral(self: *Parser) anyerror!*cst.Expr {
        const struct_start = self.currentLoc();
        var entries = self.list(cst.StructFieldValue);
        while (self.current().tag != .rcurly and self.current().tag != .eof) {
            const field_tok = self.current();
            var field_name: ?[]const u8 = null;
            if (self.current().tag == .identifier) {
                field_name = self.slice(field_tok);
                self.advance();
                try self.expect(.colon);
            }
            const value = try self.parseExpr(0, .expr);
            try entries.append(.{ .name = field_name, .value = value, .loc = field_tok.loc });
            if (!self.consumeIf(.comma)) break;
        }
        try self.expect(.rcurly);
        const struct_lit = cst.StructLiteral{ .fields = entries, .loc = struct_start };
        return self.alloc(cst.Expr, .{ .Struct = struct_lit });
    }

    fn parseIndex(self: *Parser, collection: *cst.Expr) anyerror!*cst.Expr {
        const index_start = self.currentLoc();
        const index = try self.parseExpr(0, .expr);
        try self.expect(.rsquare);
        const index_expr = cst.Index{ .collection = collection, .index = index, .loc = index_start };
        return self.alloc(cst.Expr, .{ .Index = index_expr });
    }

    fn parseField(self: *Parser, parent: *cst.Expr) anyerror!*cst.Expr {
        const field_token = self.current();
        var is_tuple = false;
        switch (self.current().tag) {
            .identifier => self.advance(),
            .integer_literal => {
                is_tuple = true;
                self.advance();
            },
            else => {
                const got = self.current();
                self.errorNote(self.currentLoc(), "expected identifier or integer after '.', found {s}", .{Token.Tag.symbol(got.tag)}, got.loc, "use a field name like .foo or a tuple index like .0", .{});
                return error.UnexpectedToken;
            },
        }
        const field = cst.Field{ .parent = parent, .field = self.slice(field_token), .is_tuple = is_tuple, .loc = field_token.loc };
        return self.alloc(cst.Expr, .{ .Field = field });
    }

    fn parseCommaExprListUntil(self: *Parser, comptime end_tag: Token.Tag) !std.array_list.Managed(*cst.Expr) {
        var items = self.list(*cst.Expr);
        if (self.current().tag != end_tag) {
            while (true) {
                const arg = try self.parseExpr(0, .expr);
                try items.append(arg);
                if (!self.consumeIf(.comma)) break;
            }
        }
        try self.expect(end_tag);
        return items;
    }

    fn parseCall(self: *Parser, callee: *cst.Expr) anyerror!*cst.Expr {
        const args = try self.parseCommaExprListUntil(.rparen);
        const call = cst.Call{ .callee = callee, .args = args, .loc = self.currentLoc() };
        return self.alloc(cst.Expr, .{ .Call = call });
    }

    fn finishParsingExprList(self: *Parser, comptime end_tag: Token.Tag, first_element: *cst.Expr) !std.array_list.Managed(*cst.Expr) {
        var elements = self.list(*cst.Expr);
        try elements.append(first_element);
        while (self.current().tag != end_tag and self.current().tag != .eof) {
            const elem = try self.parseExpr(0, .expr);
            try elements.append(elem);
            if (!self.consumeIf(.comma)) break;
        }
        try self.expect(end_tag);
        return elements;
    }

    //=================================================================
    // Statements / blocks
    //=================================================================

    inline fn parseDeref(self: *Parser, expr: *cst.Expr) !*cst.Expr {
        const loc = self.currentLoc();
        // Current token was .dotstar, already consumed by caller.
        return self.alloc(cst.Expr, .{ .Deref = .{ .expr = expr, .loc = loc } });
    }

    inline fn parseOptionalUnwrap(self: *Parser, expr: *cst.Expr) !*cst.Expr {
        const loc = self.currentLoc();
        // Current token was '?', already consumed by caller.
        return self.alloc(cst.Expr, .{ .OptionalUnwrap = .{ .expr = expr, .loc = loc } });
    }

    inline fn parsePostfixAfterDot(self: *Parser, left: *cst.Expr) anyerror!*cst.Expr {
        return switch (self.current().tag) {
            .keyword_await => try self.parseAwait(left),
            .caret, .b_or, .percent, .question => try self.parseCastSigil(left),
            else => try self.parseField(left),
        };
    }

    fn parseCastParen(self: *Parser, expr: *cst.Expr) anyerror!*cst.Expr {
        const loc = self.currentLoc();
        // Current token was .dot_lparen, already consumed by caller.
        // Parse a type until ')'
        const ty = try self.parseExpr(0, .type);
        try self.expect(.rparen);
        return self.alloc(cst.Expr, .{ .Cast = .{ .expr = expr, .ty = ty, .kind = .normal, .loc = loc } });
    }

    fn parseCastSigil(self: *Parser, expr: *cst.Expr) anyerror!*cst.Expr {
        const loc = self.currentLoc();
        const op_tag = self.current().tag;
        const kind: cst.CastKind = switch (op_tag) {
            .caret => .bitcast,
            .b_or => .saturate,
            .percent => .wrap,
            .question => .checked,
            else => unreachable,
        };
        self.advance();
        const ty = try self.parseExpr(0, .type);
        return self.alloc(cst.Expr, .{ .Cast = .{ .expr = expr, .ty = ty, .kind = kind, .loc = loc } });
    }

    inline fn parseAwait(self: *Parser, expr: *cst.Expr) !*cst.Expr {
        const loc = self.currentLoc();
        try self.expect(.keyword_await);
        return self.alloc(cst.Expr, .{ .Await = .{ .expr = expr, .loc = loc } });
    }

    inline fn parseReturn(self: *Parser) !*cst.Expr {
        const return_token = self.current();
        self.advance();
        var value: ?*cst.Expr = null;
        if (!self.isStmtTerminator()) {
            value = try self.parseExpr(0, .expr);
        }
        if (!self.isStmtTerminator()) {
            try self.expect(.eos);
        }
        const return_expr = cst.Return{ .value = value, .loc = return_token.loc };
        return self.alloc(cst.Expr, .{ .Return = return_expr });
    }

    fn parseBlock(self: *Parser) !cst.Block {
        var items = self.list(cst.Decl);
        const loc = try self.beginBrace();
        while (self.current().tag != .rcurly and self.current().tag != .eof) {
            const stmt = self.parseDecl() catch {
                // Assume a more specific diagnostic was already added at the error site
                self.syncToStmtBoundary();
                continue;
            };
            try items.append(stmt);
        }
        try self.endBrace();
        return .{ .items = items, .loc = loc };
    }

    fn parseBlockExpr(self: *Parser) !*cst.Expr {
        const block = try self.parseBlock();
        return self.alloc(cst.Expr, .{ .Block = block });
    }

    inline fn parseExprOrBlock(self: *Parser) anyerror!*cst.Expr {
        if (self.current().tag == .lcurly) {
            return try self.parseBlockExpr();
        } else {
            return try self.parseExpr(0, .expr);
        }
    }

    fn parseClosure(self: *Parser) !*cst.Expr {
        const closure_start = self.currentLoc();
        try self.expect(.b_or);
        var params = self.list(cst.Param);
        if (self.current().tag != .b_or) {
            const p = infixBp(.b_or).?; // {.l_bp, .r_bp}
            const r_bp = p[1];
            const barrier: u8 = r_bp + 1; // stop before consuming '|'
            while (true) {
                const param_start = self.currentLoc();
                // Parse parameter pattern; do not consume '|' as bitwise-or.
                const pat_expr = try self.parseExpr(barrier, .expr_no_struct);
                var ty: ?*cst.Expr = null;
                var value: ?*cst.Expr = null;
                if (self.current().tag == .colon) {
                    self.advance();
                    // Parse type but prevent consuming the closing '|' as bitwise-or.
                    ty = try self.parseExpr(barrier, .type);
                }
                if (self.current().tag == .eq) {
                    self.advance();
                    value = try self.parseExpr(0, .expr);
                }
                try params.append(.{ .pat = pat_expr, .ty = ty, .value = value, .loc = param_start });
                if (self.consumeIf(.comma)) {
                    continue;
                } else if (self.current().tag == .b_or) {
                    break;
                } else {
                    const got = self.current();
                    self.errorNote(self.currentLoc(), "expected ',' or '|' after closure parameter, found {s}", .{Token.Tag.symbol(got.tag)}, got.loc, "separate parameters with ',' and end the list with '|'", .{});
                    return error.UnexpectedToken;
                }
            }
        }
        try self.expect(.b_or);

        var return_type: ?*cst.Expr = null;
        var body: *cst.Expr = undefined;
        if (self.current().tag == .lcurly) {
            body = try self.parseBlockExpr();
        } else {
            // Parse a potential return type first; if it is immediately followed by '{',
            // treat it as the explicit result type and parse a block body.
            // Otherwise, the parsed node is the expression body (no explicit result type).
            const ty_or_body = try self.parseExpr(0, .type);
            if (self.current().tag == .lcurly) {
                return_type = ty_or_body;
                body = try self.parseBlockExpr();
            } else {
                body = ty_or_body; // expression-bodied closure
            }
        }

        const closure = cst.Closure{ .params = params, .result_ty = return_type, .body = body, .loc = closure_start };
        return self.alloc(cst.Expr, .{ .Closure = closure });
    }

    fn parseCatchExpr(self: *Parser, expr: *cst.Expr) anyerror!*cst.Expr {
        const catch_loc = self.currentLoc();
        var binding: ?cst.Ident = null;
        if (self.current().tag == .b_or) {
            self.advance();
            const name = try self.expectIdent();
            binding = cst.Ident{ .name = name.bytes, .loc = name.loc };
            try self.expect(.b_or);
        }
        const handler: *cst.Expr = try self.parseExprOrBlock();
        const catch_expr = cst.Catch{ .expr = expr, .binding = binding, .handler = handler, .loc = catch_loc };
        return self.alloc(cst.Expr, .{ .Catch = catch_expr });
    }

    fn parseIfExpr(self: *Parser) !*cst.Expr {
        const if_start = self.currentLoc();
        self.advance(); // "if"
        const condition = try self.parseExpr(0, .expr_no_struct);
        const then_block = try self.parseBlock();
        var else_block: ?*cst.Expr = null;
        if (self.current().tag == .keyword_else) {
            self.advance();
            else_block = try self.parseExprOrBlock();
        }
        const if_expr = cst.If{
            .cond = condition,
            .then_block = then_block,
            .else_block = else_block,
            .loc = if_start,
        };
        return try self.alloc(cst.Expr, .{ .If = if_expr });
    }

    fn parseWhileExpr(self: *Parser) !*cst.Expr {
        const while_start = self.currentLoc();
        self.advance(); // "while"
        var condition: ?*cst.Expr = null;
        var pattern: ?*cst.Pattern = null;
        switch (self.current().tag) {
            .keyword_is => {
                self.advance();
                pattern = try self.parsePattern();
                try self.expect(.coloneq);
                condition = try self.parseExpr(0, .expr_no_struct);
            },
            .lcurly => {}, // forever loop
            else => {
                condition = try self.parseExpr(0, .expr_no_struct);
            },
        }
        const body = try self.parseBlock();
        const while_expr = cst.While{
            .cond = condition,
            .pattern = pattern,
            .body = body,
            .loc = while_start,
            .is_pattern = false,
            .label = null,
        };
        return try self.alloc(cst.Expr, .{ .While = while_expr });
    }

    fn parseLabeledLoop(self: *Parser, label_name: []const u8) anyerror!*cst.Expr {
        return switch (self.current().tag) {
            .keyword_for => blk: {
                var loop = try self.parseForExpr();
                if (loop.* == .For) loop.For.label = label_name;
                break :blk loop;
            },
            .keyword_while => blk: {
                var loop = try self.parseWhileExpr();
                if (loop.* == .While) loop.While.label = label_name;
                break :blk loop;
            },
            else => {
                const got = self.current();
                self.errorNote(
                    self.currentLoc(),
                    "expected 'for' or 'while' after label, found {s}",
                    .{Token.Tag.symbol(got.tag)},
                    got.loc,
                    "labeled loops: label: for ... {{ ... }} or label: while ... {{ ... }}",
                    .{},
                );
                return error.UnexpectedToken;
            },
        };
    }

    fn parseForExpr(self: *Parser) !*cst.Expr {
        const for_start = self.currentLoc();
        self.advance(); // "for"
        const pattern = try self.parsePattern();
        try self.expect(.keyword_in);
        const iterable = try self.parseExpr(0, .expr_no_struct);
        const body = try self.parseBlock();
        const for_expr = cst.For{
            .pattern = pattern,
            .iterable = iterable,
            .body = body,
            .loc = for_start,
        };
        return try self.alloc(cst.Expr, .{ .For = for_expr });
    }

    fn parseMatchExpr(self: *Parser) !*cst.Expr {
        const start = self.currentLoc();
        self.advance(); // "match"

        const scrutinee = try self.parseExpr(0, .expr_no_struct);

        try self.expect(.lcurly);
        var arms = self.list(cst.MatchArm);
        while (self.current().tag != .rcurly and self.current().tag != .eof) {
            const pat_expr = try self.parsePattern();

            var guard: ?*cst.Expr = null;
            if (self.current().tag == .keyword_if) {
                self.advance();
                guard = try self.parseExpr(0, .expr_no_struct);
            }

            try self.expect(.fatarrow);

            const body: *cst.Expr = try self.parseExprOrBlock();

            _ = self.consumeIf(.comma);

            try arms.append(.{ .pattern = pat_expr, .guard = guard, .body = body, .loc = self.currentLoc() });
        }
        try self.expect(.rcurly);

        return try self.alloc(cst.Expr, .{ .Match = .{ .expr = scrutinee, .arms = arms, .loc = start } });
    }

    //=================================================================
    // Patterns
    // =================================================================

    fn parsePattern(self: *Parser) !*cst.Pattern {
        return try self.parsePatOr();
    }

    fn parsePatOr(self: *Parser) !*cst.Pattern {
        const current_loc = self.currentLoc();
        const first = try self.parsePatRange();
        if (self.current().tag != .b_or) return first; // '|' token; you already use .b_or for '|'

        var alts = self.list(*cst.Pattern);
        try alts.append(first);
        while (self.current().tag == .b_or) {
            self.advance();
            try alts.append(try self.parsePatRange());
        }
        const or_pat = cst.OrPattern{ .loc = current_loc, .alts = alts };
        return try self.alloc(cst.Pattern, .{ .Or = or_pat });
    }

    fn parsePatRange(self: *Parser) !*cst.Pattern {
        // Handle prefix/open ranges first:  ..X  or  ..=X
        if (self.current().tag == .dotdot or self.current().tag == .dotdoteq) {
            const start_loc = self.currentLoc();
            const incl = (self.current().tag == .dotdoteq);
            self.advance();
            const end = try self.parseConstExprForRangeEnd();
            return try self.alloc(cst.Pattern, .{ .Range = .{
                .loc = start_loc,
                .start = null,
                .end = end,
                .inclusive_right = incl,
            } });
        }

        // Otherwise parse a primary/atomic pattern as the potential left side
        const left = try self.parsePatAt();

        // If followed by  .. or ..=  then we have an infix range: LEFT .. RIGHT
        if (self.current().tag == .dotdot or self.current().tag == .dotdoteq) {
            const incl = (self.current().tag == .dotdoteq);
            const loc = self.currentLoc();
            self.advance();

            const rhs = try self.parseConstExprForRangeEnd();
            const lhs_expr = try self.patternToConstExpr(left); // convert left pattern to a const expr
            return try self.alloc(cst.Pattern, .{ .Range = .{
                .loc = loc,
                .start = lhs_expr,
                .end = rhs,
                .inclusive_right = incl,
            } });
        }

        return left;
    }

    fn patternToConstExpr(self: *Parser, pat: *cst.Pattern) !*cst.Expr {
        return switch (pat.*) {
            .Literal => |lit_expr_ptr| lit_expr_ptr, // you already store the literal as an *ast.Expr
            .Path => |p| try self.pathToConstExpr(p.segments),
            .Binding => |b| blk: {
                // Turn binding name into an expr; the checker can complain if it's not const.
                const ident = cst.Ident{ .name = b.name, .loc = b.loc };
                break :blk try self.alloc(cst.Expr, .{ .Ident = ident });
            },
            .Wildcard => {
                self.errorNote(self.currentLoc(), "'_' is not valid as a constant in a range pattern", .{}, null, "use a literal, constant path, or a binding name", .{});
                return error.UnexpectedToken;
            },
            // Disallow complex patterns on the LHS of a range.
            else => {
                self.errorNote(self.currentLoc(), "left side of a range pattern must be a const-like literal/path/binding", .{}, null, "use a literal, constant path, or a simple binding", .{});
                return error.UnexpectedToken;
            },
        };
    }

    fn patternToBindingName(self: *Parser, pat: *cst.Pattern) ![]const u8 {
        return switch (pat.*) {
            .Binding => pat.Binding.name,
            .Path => blk: {
                if (pat.Path.segments.items.len == 1) {
                    break :blk pat.Path.segments.items[0].name;
                } else {
                    self.errorNote(
                        self.currentLoc(),
                        "only simple identifier paths can be used as binding names in '@' patterns",
                        .{},
                        null,
                        "use a single identifier without dots",
                        .{},
                    );
                    return error.InvalidPatternForBinding;
                }
            },
            else => {
                self.errorNote(
                    self.currentLoc(),
                    "only simple identifier paths can be used as binding names in '@' patterns",
                    .{},
                    null,
                    "use a single identifier without dots",
                    .{},
                );
                return error.InvalidPatternForBinding;
            },
        };
    }

    fn parsePatAt(self: *Parser) !*cst.Pattern {
        // binding '@' pattern: IDENT '@' subpattern
        // But IDENT alone might be a Path/Binding; we need a lookahead.
        const p = try self.parsePatPrimary();

        if (self.current().tag == .at) { // '@'
            const current_loc = self.currentLoc();
            // Left must be a binding name (IDENT) to be valid; let checker enforce that
            self.advance();
            const sub = try self.parsePatAt(); // right-assoc
            // Extract binder name if `p` is a simple Path/Binding; otherwise checker will error
            const name = try self.patternToBindingName(p);
            const at = cst.AtPattern{ .loc = current_loc, .binder = name, .pattern = sub };
            return try self.alloc(cst.Pattern, .{ .At = at });
        }
        return p;
    }

    fn parsePatPrimary(self: *Parser) !*cst.Pattern {
        switch (self.current().tag) {
            // .underscore_like => { /* see note below */ },
            .char_literal, .string_literal, .raw_string_literal, .byte_literal, .byte_char_literal, .byte_string_literal, .raw_byte_string_literal, .integer_literal, .float_literal, .keyword_true, .keyword_false => {
                const lit = try self.nud(self.current().tag, .expr_no_struct); // reuse literal expr nud
                return try self.alloc(cst.Pattern, .{ .Literal = lit });
            },
            // .star => { // *pat
            //     self.advance();
            //     const sub = try self.parsePatPrimary();
            //     return try self.alloc(ast.Pattern, .{ .Deref = sub });
            // },
            .lparen => return try self.parseTuplePattern(),
            .lsquare => return try self.parseSlicePattern(),
            .dotdot, .dotdoteq => { // .. / ..= open ranges
                const start_loc = self.currentLoc();
                const incl = (self.current().tag == .dotdoteq);
                self.advance();
                const end = try self.parseConstExprForRangeEnd();
                const range = cst.RangePattern{
                    .loc = start_loc,
                    .start = null,
                    .end = end,
                    .inclusive_right = incl,
                };
                return try self.alloc(cst.Pattern, .{ .Range = range });
            },
            .identifier => return try self.parsePathishPattern(),
            else => {
                self.errorNote(
                    self.currentLoc(),
                    "unexpected token in pattern: {s}",
                    .{Token.Tag.symbol(self.current().tag)},
                    null,
                    "this token cannot start a pattern",
                    .{},
                );
                return error.UnexpectedToken;
            },
        }
    }

    fn parseTuplePattern(self: *Parser) anyerror!*cst.Pattern {
        const loc = self.currentLoc();
        try self.expect(.lparen);
        var elems = self.list(*cst.Pattern);
        if (self.current().tag != .rparen) {
            while (true) {
                try elems.append(try self.parsePattern());
                if (!self.consumeIf(.comma)) break;
            }
        }
        try self.expect(.rparen);
        const tuple_pat = cst.TuplePattern{ .loc = loc, .elems = elems };
        return try self.alloc(cst.Pattern, .{ .Tuple = tuple_pat });
    }

    fn parsePathishPattern(self: *Parser) anyerror!*cst.Pattern {
        // Collect a dotted path: Foo.Bar.Baz
        var segs = self.list(cst.Ident);
        while (true) {
            const tok = self.current();
            try self.expect(.identifier);
            try segs.append(.{ .name = self.slice(tok), .loc = tok.loc });
            if (self.current().tag != .dot) break;
            self.advance();
            if (self.current().tag != .identifier) break; // allow weirdness; checker will flag
        }
        const path = segs;

        switch (self.current().tag) {
            .lparen => { // tuple/variant data
                const loc = self.currentLoc();
                self.advance();
                var elems = self.list(*cst.Pattern);
                if (self.current().tag != .rparen) {
                    while (true) {
                        try elems.append(try self.parsePattern());
                        if (!self.consumeIf(.comma)) break;
                    }
                }
                try self.expect(.rparen);
                if (path.items.len == 1) {
                    // Could be tuple pattern without a variant; but in Rust, plain tuple pattern has no head.
                    // In practice, treat as VariantTuple and let checker resolve head=path
                }
                const tuple_pat = cst.VariantTuplePattern{ .loc = loc, .path = path, .elems = elems };
                return try self.alloc(cst.Pattern, .{ .VariantTuple = tuple_pat });
            },
            .lcurly => { // struct/variant struct data; supports {..., ..}
                self.advance();
                var fields = self.list(cst.StructPatternField);
                var has_rest = false;
                const pat_loc = self.currentLoc();
                while (self.current().tag != .rcurly and self.current().tag != .eof) {
                    if (self.current().tag == .dotdot) { // '..'
                        has_rest = true;
                        self.advance();
                        if (self.current().tag == .comma) self.advance();
                        break;
                    }
                    const name_tok = self.current();
                    try self.expect(.identifier);
                    const name = self.slice(name_tok);
                    const loc = name_tok.loc;

                    var pat: *cst.Pattern = undefined;
                    if (self.current().tag == .colon) {
                        self.advance();
                        pat = try self.parsePattern();
                    } else {
                        // field shorthand: `name` == bind name
                        pat = try self.alloc(
                            cst.Pattern,
                            .{ .Binding = .{ .loc = loc, .name = name } },
                        );
                    }
                    try fields.append(.{ .name = name, .pattern = pat, .loc = loc });

                    if (!self.consumeIf(.comma)) break;
                }
                try self.expect(.rcurly);
                // disambiguation left to checker: path may be a struct type or enum variant
                return try self.alloc(
                    cst.Pattern,
                    .{ .VariantStruct = .{ .loc = pat_loc, .path = path, .fields = fields, .has_rest = has_rest } },
                );
            },
            .dotdot, .dotdoteq => { // range like: Foo .. Bar  (typically literals/consts; allow path here)
                const incl = (self.current().tag == .dotdoteq);
                const loc = self.currentLoc();
                self.advance();
                const rhs = try self.parseConstExprForRangeEnd();
                const start_expr = try self.pathToConstExpr(path);
                return try self.alloc(cst.Pattern, .{ .Range = .{
                    .loc = loc,
                    .start = start_expr,
                    .end = rhs,
                    .inclusive_right = incl,
                } });
            },
            else => {
                // bare identifier/path: binding or const-path pattern; let checker decide
                if (path.items.len == 1 and std.mem.eql(u8, path.items[0].name, "_")) {
                    return try self.alloc(cst.Pattern, .{ .Wildcard = .{ .loc = path.items[0].loc } });
                }
                // default to Binding; checker can upgrade to const-path pattern if name resolves to a const
                if (path.items.len == 1) {
                    return try self.alloc(cst.Pattern, .{
                        .Binding = .{ .name = path.items[0].name, .loc = path.items[0].loc },
                    });
                }
                return try self.alloc(cst.Pattern, .{
                    .Path = .{ .segments = path, .loc = path.items[0].loc },
                });
            },
        }
    }

    fn parseSlicePattern(self: *Parser) anyerror!*cst.Pattern {
        try self.expect(.lsquare);
        var elems = self.list(*cst.Pattern);
        var has_rest = false;
        var rest_index: usize = 0;
        var rest_binding: ?*cst.Pattern = null;
        const loc = self.currentLoc();

        if (self.current().tag != .rsquare) {
            var i: usize = 0;
            while (true) : (i += 1) {
                if (self.current().tag == .dotdot) {
                    has_rest = true;
                    rest_index = i;
                    self.advance();

                    // OPTIONAL: allow a binding name after `..` (e.g. `.. rest`)
                    if (self.current().tag == .identifier) {
                        const name_tok = self.current();
                        const name = self.slice(name_tok);
                        self.advance();
                        if (!std.mem.eql(u8, name, "_")) {
                            rest_binding = try self.alloc(
                                cst.Pattern,
                                .{ .Binding = .{ .name = name, .loc = name_tok.loc } },
                            );
                        }
                    }

                    _ = self.consumeIf(.comma);
                    break; // rest consumes the remainder
                }
                try elems.append(try self.parsePattern());
                if (!self.consumeIf(.comma)) break;
            }
        }

        try self.expect(.rsquare);
        return try self.alloc(cst.Pattern, .{
            .Slice = .{
                .loc = loc,
                .elems = elems,
                .has_rest = has_rest,
                .rest_index = rest_index,
                .rest_binding = rest_binding, // NEW
            },
        });
    }

    fn parseConstExprForRangeEnd(self: *Parser) !*cst.Expr {
        // use normal expr, semantic checker will ensure "const evaluable" and no side effects
        return self.parseExpr(0, .expr_no_struct);
    }

    fn pathToConstExpr(self: *Parser, path: std.array_list.Managed(cst.Ident)) !*cst.Expr {
        // Build an ast.Expr Ident/Field chain from the path for the checker to resolve.
        var expr: *cst.Expr = try self.alloc(cst.Expr, .{ .Ident = path.items[0] });
        var i: usize = 1;
        while (i < path.items.len) : (i += 1) {
            expr = try self.alloc(cst.Expr, .{ .Field = .{
                .parent = expr,
                .field = path.items[i].name,
                .is_tuple = false,
                .loc = self.currentLoc(),
            } });
        }
        return expr;
    }

    //=================================================================
    // Types (building blocks)
    //=================================================================

    fn parseStructField(self: *Parser) !cst.StructField {
        const start = self.currentLoc();
        // Optional visibility modifier (currently ignored in AST)
        if (self.current().tag == .keyword_pub) {
            self.advance();
        }
        const field_attrs = try self.parseOptionalAttributes();
        const name = try self.expectIdent();
        try self.expect(.colon);
        const ty = try self.parseExpr(0, .type);
        const value = try self.parseOptionalInitializer(.expr);
        return .{ .name = name.bytes, .ty = ty, .value = value, .loc = start, .attrs = field_attrs };
    }

    fn parseStructFieldList(self: *Parser, end_tag: Token.Tag) !std.array_list.Managed(cst.StructField) {
        var fields = self.list(cst.StructField);
        while (self.current().tag != end_tag and self.current().tag != .eof) {
            try fields.append(try self.parseStructField());
            if (!self.consumeIf(.comma)) break;
        }
        try self.expect(end_tag);
        return fields;
    }

    inline fn parseStructLikeType(
        self: *Parser,
        comptime tag: Token.Tag,
        comptime is_extern: bool,
    ) !*cst.Expr {
        const struct_start = self.currentLoc();
        self.advance(); // "struct" / "union"
        try self.expect(.lcurly);
        const fields = try self.parseStructFieldList(.rcurly);
        const struct_type = cst.StructLikeType{ .is_extern = is_extern, .fields = fields, .loc = struct_start };
        if (tag == .keyword_struct) {
            return self.alloc(cst.Expr, .{ .BuiltinType = .{ .Struct = struct_type } });
        }
        return self.alloc(cst.Expr, .{ .BuiltinType = .{ .Union = struct_type } });
    }

    inline fn parsePointerType(self: *Parser) !*cst.Expr {
        const start_token = self.current();
        self.advance(); // "*"
        var is_const = false;
        if (self.current().tag == .keyword_const) {
            is_const = true;
            self.advance();
        }
        const elem_type = try self.parseExpr(0, .type);
        const ptr_type = cst.PointerType{ .elem = elem_type, .is_const = is_const, .loc = start_token.loc };
        return try self.alloc(cst.Expr, .{ .BuiltinType = .{ .Pointer = ptr_type } });
    }

    inline fn parseOptionalType(self: *Parser) !*cst.Expr {
        const start_token = self.current();
        self.advance(); // "?"
        const elem_type = try self.parseExpr(0, .type);
        const opt_type = cst.UnaryType{ .elem = elem_type, .loc = start_token.loc };
        return try self.alloc(cst.Expr, .{ .BuiltinType = .{ .Optional = opt_type } });
    }

    inline fn parseComplexType(self: *Parser) !*cst.Expr {
        const start = try self.beginKeywordParen(.keyword_complex);
        const elem_type = try self.parseExpr(0, .type);
        try self.endParen();
        const complex_type = cst.ComplexType{ .elem = elem_type, .loc = start };
        return try self.alloc(cst.Expr, .{ .BuiltinType = .{ .Complex = complex_type } });
    }

    inline fn parseSimdType(self: *Parser) !*cst.Expr {
        const start = try self.beginKeywordParen(.keyword_simd);
        const elem_type = try self.parseExpr(0, .type);
        try self.expect(.comma);
        const size_expr = try self.parseExpr(0, .expr);
        try self.endParen();
        const simd_type = cst.SimdType{ .elem = elem_type, .lanes = size_expr, .loc = start };
        return try self.alloc(cst.Expr, .{ .BuiltinType = .{ .Simd = simd_type } });
    }

    inline fn parseTensorType(self: *Parser) !*cst.Expr {
        const start = try self.beginKeywordParen(.keyword_tensor);
        const first = try self.parseExpr(0, .expr);
        try self.expect(.comma);
        var shape = try self.finishParsingExprList(.rparen, first);
        const elem_type = shape.pop().?;
        const tensor_type = cst.TensorType{ .elem = elem_type, .shape = shape, .loc = start };
        return try self.alloc(cst.Expr, .{ .BuiltinType = .{ .Tensor = tensor_type } });
    }

    //=================================================================
    // Array-like / Map (type or literal)
    //=================================================================

    fn parseMapTypeOrLiteral(self: *Parser, key_expr: *cst.Expr, start_loc: Loc) !*cst.Expr {
        // caller consumed ":" already
        const value_type = try self.parseExpr(0, .type);
        return switch (self.current().tag) {
            .rsquare => blk: {
                try self.expect(.rsquare);
                const map_type = cst.MapType{ .key = key_expr, .value = value_type, .loc = start_loc };
                break :blk try self.alloc(cst.Expr, .{ .BuiltinType = .{ .MapType = map_type } });
            },
            .comma => blk: {
                // literal form: [key: value, ...]
                self.advance();
                var entries = self.list(cst.KeyValue);
                try entries.append(.{ .key = key_expr, .value = value_type, .loc = start_loc });
                while (self.current().tag != .rsquare and self.current().tag != .eof) {
                    const k = try self.parseExpr(0, .expr);
                    try self.expect(.colon);
                    const v = try self.parseExpr(0, .expr);
                    try entries.append(.{ .key = k, .value = v, .loc = self.currentLoc() });
                    if (!self.consumeIf(.comma)) break;
                }
                try self.expect(.rsquare);
                const map = cst.Map{ .entries = entries, .loc = start_loc };
                break :blk try self.alloc(cst.Expr, .{ .Map = map });
            },
            else => {
                self.errorNote(
                    self.currentLoc(),
                    "expected ']' or ',' in map type/literal, found {s}",
                    .{Token.Tag.symbol(self.current().tag)},
                    null,
                    "use ']' to end a map type or ',' to separate key-value pairs in a map literal",
                    .{},
                );
                return error.UnexpectedToken;
            },
        };
    }

    fn parseArrayLike(self: *Parser) !*cst.Expr {
        const start_token = self.current();
        self.advance(); // "["

        return switch (self.current().tag) {
            // "[]T" slice type OR "[]" empty array literal
            .rsquare => blk: {
                self.advance(); // "]"
                switch (self.current().tag) {
                    .eos, .rcurly, .rparen, .rsquare, .comma, .colon => {
                        const array = cst.Array{ .elems = self.list(*cst.Expr), .loc = start_token.loc };
                        break :blk try self.alloc(cst.Expr, .{ .Array = array });
                    },
                    else => {
                        const elem_type = try self.parseExpr(0, .type);
                        const slice_type = cst.UnaryType{ .elem = elem_type, .loc = start_token.loc };
                        break :blk try self.alloc(cst.Expr, .{ .BuiltinType = .{ .Slice = slice_type } });
                    },
                }
            },

            // "[dyn]T" dynamic array type
            .keyword_dyn => blk: {
                self.advance();
                try self.expect(.rsquare);
                const elem_type = try self.parseExpr(0, .type);
                const dyn_array_type = cst.UnaryType{ .elem = elem_type, .loc = start_token.loc };
                break :blk try self.alloc(cst.Expr, .{ .BuiltinType = .{ .DynArray = dyn_array_type } });
            },

            // starts with expression -> could be sized array type "[N]T", map "[K:V]" / map literal, or array literal "[a, b, ...]"
            else => blk: {
                const first_expr = try self.parseExpr(0, .expr);
                switch (self.current().tag) {
                    .rsquare => {
                        // "[N]T" (array type)
                        self.advance();
                        const elem_type = try self.parseExpr(0, .type);
                        const array_type = cst.ArrayType{ .elem = elem_type, .size = first_expr, .loc = start_token.loc };
                        break :blk try self.alloc(cst.Expr, .{ .BuiltinType = .{ .Array = array_type } });
                    },
                    .colon => {
                        // map type or literal "[K:V]" or "[k:v, ...]"
                        self.advance(); // consume ":"
                        break :blk try self.parseMapTypeOrLiteral(first_expr, start_token.loc);
                    },
                    .comma => {
                        // array literal "[a, b, ...]"
                        self.advance();
                        const elements = try self.finishParsingExprList(.rsquare, first_expr);
                        const array = cst.Array{ .elems = elements, .loc = start_token.loc };
                        break :blk try self.alloc(cst.Expr, .{ .Array = array });
                    },
                    else => {
                        self.errorNote(
                            self.currentLoc(),
                            "expected ']', ':', or ',' in array-like, found {s}",
                            .{Token.Tag.symbol(self.current().tag)},
                            null,
                            "use ']' to end an array type or literal, ':' for a map type/literal, or ',' to separate elements in an array literal",
                            .{},
                        );
                        return error.UnexpectedToken;
                    },
                }
            },
        };
    }

    fn parseParenExpr(self: *Parser) !*cst.Expr {
        const start_token = self.current();
        self.advance(); // "("
        return switch (self.current().tag) {
            .rparen => blk: {
                // empty tuple "()"
                self.advance();
                const tuple = cst.Tuple{ .elems = self.list(*cst.Expr), .loc = start_token.loc };
                break :blk try self.alloc(cst.Expr, .{ .Tuple = tuple });
            },
            else => blk: {
                const expr = try self.parseExpr(0, .expr);
                if (self.current().tag == .comma) {
                    self.advance();
                    const elements = try self.finishParsingExprList(.rparen, expr);
                    const tuple = cst.Tuple{ .elems = elements, .loc = start_token.loc };
                    break :blk try self.alloc(cst.Expr, .{ .Tuple = tuple });
                } else {
                    try self.expect(.rparen);
                    break :blk expr;
                }
            },
        };
    }

    //=================================================================
    // Functions
    //=================================================================

    inline fn parseOptionalReturnType(self: *Parser) !?*cst.Expr {
        return switch (self.current().tag) {
            .lcurly, .eos => null,
            else => try self.parseExpr(0, .type),
        };
    }

    fn parseExternDecl(self: *Parser) !*cst.Expr {
        self.advance(); // "extern"
        switch (self.current().tag) {
            .keyword_async => {
                self.advance();
                switch (self.current().tag) {
                    .keyword_proc, .keyword_fn => return try self.parseFunctionLike(self.current().tag, true, true),
                    else => {
                        self.errorNote(
                            self.currentLoc(),
                            "expected 'proc' or 'fn' after 'extern async', found {s}",
                            .{Token.Tag.symbol(self.current().tag)},
                            null,
                            "use 'extern async proc' or 'extern async fn'",
                            .{},
                        );
                        return error.UnexpectedToken;
                    },
                }
            },
            .keyword_proc, .keyword_fn => return try self.parseFunctionLike(self.current().tag, true, false),
            .keyword_struct => return try self.parseStructLikeType(.keyword_struct, true),
            .keyword_enum => return try self.parseEnumType(true),
            .keyword_union => return try self.parseStructLikeType(.keyword_union, true),
            else => {
                self.errorNote(
                    self.currentLoc(),
                    "expected 'proc', 'fn', or a type after 'extern', found {s}",
                    .{Token.Tag.symbol(self.current().tag)},
                    null,
                    "use 'extern proc', 'extern fn', or 'extern struct/enum/union'",
                    .{},
                );
                return error.UnexpectedToken;
            },
        }
    }

    fn parseFunctionLike(self: *Parser, tag: Token.Tag, comptime is_extern: bool, is_async: bool) !*cst.Expr {
        const start_token = self.current();
        self.advance(); // "proc" or "fn"
        try self.expect(.lparen);

        var params = self.list(cst.Param);
        while (self.current().tag != .rparen and self.current().tag != .eof) {
            const param_start = self.currentLoc();
            const param_attrs = try self.parseOptionalAttributes();
            var pat: ?*cst.Expr = try self.parseExpr(0, .expr);
            var ty: *cst.Expr = undefined;
            var value: ?*cst.Expr = null;

            if (self.current().tag == .colon) {
                self.advance();
                ty = try self.parseExpr(0, .type);
                if (self.current().tag == .eq) {
                    self.advance();
                    value = try self.parseExpr(0, .expr);
                }
            } else if (self.current().tag == .comma or self.current().tag == .rparen) {
                ty = pat.?;
                pat = null;
            } else {
                self.errorNote(
                    self.currentLoc(),
                    "expected ':', ',', or ')' after parameter, found {s}",
                    .{Token.Tag.symbol(self.current().tag)},
                    null,
                    "use ':' to specify a type, or ',' / ')' to end the parameter",
                    .{},
                );
                return error.UnexpectedToken;
            }

            try params.append(.{ .pat = pat, .ty = ty, .value = value, .loc = param_start, .attrs = param_attrs });
            if (self.current().tag != .comma) break;
            self.advance();
        }
        try self.expect(.rparen);

        const return_type: ?*cst.Expr = try self.parseOptionalReturnType();

        var body: ?cst.Block = null;
        var raw_asm: ?[]const u8 = null;
        if (self.current().tag == .lcurly) {
            body = try self.parseBlock();
        } else if (self.current().tag == .raw_asm_block) {
            // Capture the raw asm text as-is from the source
            const tok = self.current();
            raw_asm = self.slice(tok);
            self.advance();
        }
        // if last type is keyword_any, then function is variadic (C-style ...)
        var is_variadic = false;
        if (params.items.len > 0) {
            const last_param = params.items[params.items.len - 1];
            if (last_param.ty.?.* == .BuiltinType) {
                if (last_param.ty.?.BuiltinType == .Any) {
                    is_variadic = true;
                }
            }
        }
        const func = cst.Function{
            .is_proc = (tag == .keyword_proc),
            .params = params,
            .result_ty = return_type,
            .body = body,
            .loc = start_token.loc,
            .is_async = is_async,
            .is_variadic = is_variadic,
            .is_extern = is_extern,
            .raw_asm = raw_asm,
        };
        return try self.alloc(cst.Expr, .{ .Function = func });
    }

    //=================================================================
    // Metaprogramming: comptime, code, insert, mlir
    //=================================================================

    fn parseComptime(self: *Parser) !*cst.Expr {
        self.advance(); // "comptime"
        if (self.current().tag == .lcurly) {
            const blk = try self.parseBlock();
            return try self.alloc(cst.Expr, .{ .Comptime = .{ .Block = blk } });
        } else {
            const expr = try self.parseExpr(0, .expr);
            return try self.alloc(cst.Expr, .{ .Comptime = .{ .Expr = expr } });
        }
    }

    fn parseCodeBlock(self: *Parser) !*cst.Expr {
        const start = self.currentLoc();
        self.advance(); // "code"
        const blk = try self.parseBlock();
        return try self.alloc(cst.Expr, .{ .Code = .{ .block = blk, .loc = start } });
    }

    fn parseInsert(self: *Parser) !*cst.Expr {
        const start = self.currentLoc();
        self.advance(); // "insert"
        const expr = try self.parseExpr(0, .expr);
        return try self.alloc(cst.Expr, .{ .Insert = .{ .expr = expr, .loc = start } });
    }

    fn parseMlir(self: *Parser) !*cst.Expr {
        const start = self.currentLoc();
        self.advance(); // "mlir"
        var kind: cst.MlirKind = .Module;
        switch (self.current().tag) {
            .identifier => {
                const kw = self.slice(self.current());
                if (std.mem.eql(u8, kw, "attribute")) {
                    kind = .Attribute;
                    self.advance();
                } else if (std.mem.eql(u8, kw, "op") or std.mem.eql(u8, kw, "operation")) {
                    kind = .Operation;
                    self.advance();
                }
            },
            .keyword_type => {
                kind = .Type;
                self.advance();
            },
            else => {},
        }
        const tok = self.current();
        const raw = self.slice(tok);
        try self.expect(.mlir_content);
        return try self.alloc(cst.Expr, .{ .Mlir = .{ .kind = kind, .text = raw, .loc = start } });
    }

    //=================================================================
    // Enums / Variants
    //=================================================================

    inline fn parseEnumType(self: *Parser, comptime is_extern: bool) !*cst.Expr {
        const enum_start = self.currentLoc();
        self.advance(); // "enum"

        var backing_type: ?*cst.Expr = null;
        if (self.current().tag == .lparen) {
            self.advance();
            backing_type = try self.parseExpr(0, .type);
            try self.expect(.rparen);
        }

        try self.expect(.lcurly);

        var fields = self.list(cst.EnumField);
        while (self.current().tag != .rcurly and self.current().tag != .eof) {
            const field_start = self.currentLoc();
            const field_attrs = try self.parseOptionalAttributes();
            const name = try self.expectIdent();
            const value = try self.parseOptionalInitializer(.expr);
            try fields.append(.{ .name = name.bytes, .value = value, .loc = field_start, .attrs = field_attrs });
            if (!self.consumeIf(.comma)) break;
        }

        try self.expect(.rcurly);
        const enum_type = cst.EnumType{ .is_extern = is_extern, .fields = fields, .discriminant = backing_type, .loc = enum_start, .attrs = null };
        return self.alloc(cst.Expr, .{ .BuiltinType = .{ .Enum = enum_type } });
    }

    inline fn parseErrorType(self: *Parser) !*cst.Expr {
        return self.parseVariantLikeType(true);
    }

    inline fn parseVariantType(self: *Parser) !*cst.Expr {
        return self.parseVariantLikeType(false);
    }

    fn parseVariantLikeType(self: *Parser, comptime is_error: bool) !*cst.Expr {
        // Rust-like enum with payloads
        const variant_start = self.currentLoc();
        self.advance(); // "variant"
        try self.expect(.lcurly);

        var fields = self.list(cst.VariantField);

        while (self.current().tag != .rcurly and self.current().tag != .eof) {
            const case_start = self.currentLoc();
            const case_attrs = try self.parseOptionalAttributes();
            while (self.current().tag == .eos) self.advance();
            const case_name = try self.expectIdent();

            switch (self.current().tag) {
                .lparen => {
                    // Tuple-like payload
                    self.advance();
                    var types = self.list(*cst.Expr);
                    if (self.current().tag != .rparen) {
                        while (true) {
                            try types.append(try self.parseExpr(0, .type));
                            if (!self.consumeIf(.comma)) break;
                        }
                    }
                    try self.expect(.rparen);
                    const value = try self.parseOptionalInitializer(.expr);
                    try fields.append(.{ .name = case_name.bytes, .ty = .{ .Tuple = types }, .value = value, .loc = case_start, .attrs = case_attrs });
                    if (self.current().tag != .comma) break;
                    self.advance();
                },
                .lcurly => {
                    // Struct-like payload
                    self.advance();
                    const struct_fields = try self.parseStructFieldList(.rcurly);
                    const value = try self.parseOptionalInitializer(.expr);
                    try fields.append(.{ .name = case_name.bytes, .ty = .{ .Struct = struct_fields }, .value = value, .loc = case_start, .attrs = case_attrs });
                    if (!self.consumeIf(.comma)) break;
                },
                else => {
                    // No payload
                    const value = try self.parseOptionalInitializer(.expr);
                    try fields.append(.{ .name = case_name.bytes, .ty = null, .value = value, .loc = case_start, .attrs = case_attrs });
                    if (!self.consumeIf(.comma)) break;
                },
            }
        }

        try self.expect(.rcurly);
        const variant_type = cst.VariantLikeType{ .fields = fields, .loc = variant_start };
        if (is_error)
            return self.alloc(cst.Expr, .{ .BuiltinType = .{ .Error = variant_type } });
        return self.alloc(cst.Expr, .{ .BuiltinType = .{ .Variant = variant_type } });
    }
};
