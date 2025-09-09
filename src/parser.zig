const std = @import("std");
const Lexer = @import("lexer.zig").Tokenizer;
const Token = @import("lexer.zig").Token;
const Loc = Token.Loc;
const ast = @import("ast.zig");

pub const Parser = struct {
    allocator: std.mem.Allocator,
    source: []const u8,
    lexer: Lexer,
    current_token: Token,
    next_token: Token,

    const ParseMode = enum { expr, type, expr_no_struct };

    pub fn init(allocator: std.mem.Allocator, source: [:0]const u8) Parser {
        var lexer = Lexer.init(source);
        const current_token = lexer.next();
        const next_token = lexer.next();
        return .{ .allocator = allocator, .source = source, .lexer = lexer, .current_token = current_token, .next_token = next_token };
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
            std.debug.print("Expected token: {}, but got: {}\n", .{
                tag,
                self.current_token.tag,
            });
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

    inline fn parseOptionalInitializer(self: *Parser, comptime mode: ParseMode) !?*ast.Expr {
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

    fn parseAttributesList(self: *Parser) !std.array_list.Managed(ast.Attribute) {
        var attrs = self.list(ast.Attribute);
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
                std.debug.print("Expected attribute name, got: {}\n", .{tok.tag});
                return error.UnexpectedToken;
            }
            var val: ?*ast.Expr = null;
            if (self.current().tag == .eq) {
                self.advance();
                // Only literals or identifiers are allowed
                const t = self.current().tag;
                if (isLiteralTag(t) or t == .identifier) {
                    val = try self.parseExpr(0, .expr);
                } else {
                    std.debug.print("Expected literal or identifier after '=' in attribute, got: {}\n", .{t});
                    return error.UnexpectedToken;
                }
            }
            try attrs.append(.{ .name = name_bytes, .value = val, .loc = attr_loc });
            if (!self.consumeIf(.comma)) break;
        }
        try self.expect(.rsquare);
        return attrs;
    }

    fn parseOptionalAttributes(self: *Parser) !?std.array_list.Managed(ast.Attribute) {
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

    inline fn toPrefixOp(tag: Token.Tag) ast.PrefixOp {
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

    fn looksLikeCtorHead(self: *Parser, expr: *ast.Expr) bool {
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

    pub fn parse(self: *Parser) !ast.Program {
        var decls = self.list(ast.Decl);
        var pkg_decl: ?ast.PackageDecl = null;
        if (self.current_token.tag == .keyword_package) {
            pkg_decl = try self.parsePackageDecl();
        }
        while (self.current_token.tag != .eof) {
            const decl = try self.parseDecl();
            try decls.append(decl);
        }
        return .{ .decls = decls, .package = pkg_decl };
    }

    fn parsePackageDecl(self: *Parser) !ast.PackageDecl {
        const loc = self.currentLoc();
        try self.expect(.keyword_package);
        const name = try self.expectIdent();
        try self.expect(.eos);
        return .{ .name = name.bytes, .loc = loc };
    }

    fn parseDecl(self: *Parser) anyerror!ast.Decl {
        const loc = self.currentLoc();
        const lhs = try self.parseExpr(0, .expr);
        var is_const = false;
        var ty: ?*ast.Expr = null;
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
                            std.debug.print("Expected '=' or '::' after type in declaration, but got: {}\n", .{self.current().tag});
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
                std.debug.print("Expected '::' or '=' after lhs in declaration, but got: {}\n", .{self.current().tag});
                return error.UnexpectedToken;
            },
        }

        const rhs = try self.parseExpr(0, .expr);
        if (self.current().tag != .rcurly and self.current().tag != .eof) {
            // DEBUG
            std.debug.print("[debug] expecting .eos, current={any}\n", .{self.current().tag});
            try self.expect(.eos);
        }
        return .{ .lhs = lhs, .rhs = rhs, .ty = ty, .loc = loc, .is_const = is_const, .is_assign = is_assign };
    }

    fn nud(self: *Parser, tag: Token.Tag, comptime mode: ParseMode) anyerror!*ast.Expr {
        // prefix
        switch (tag) {
            .plus, .minus, .b_and, .bang, .dotdot, .dotdoteq => {
                // Capture operator info up-front to avoid mutation by recursive parse
                const op_loc = self.currentLoc();
                const op_kind = toPrefixOp(tag);
                self.advance();
                const rhs = try self.parseExpr(prefixBp(tag), mode);
                const unary = ast.Prefix{ .op = op_kind, .right = rhs, .loc = op_loc };
                return try self.alloc(ast.Expr, .{ .Prefix = unary });
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
            const literal = ast.Literal{ .value = self.slice(self.current()), .loc = self.currentLoc(), .kind = tag };
            self.advance();
            return try self.alloc(ast.Expr, .{ .Literal = literal });
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
                const ident = ast.Ident{ .name = self.slice(self.current()), .loc = self.currentLoc() };
                self.advance();
                break :blk try self.alloc(ast.Expr, .{ .Ident = ident });
            },
            .lsquare => try self.parseArrayLike(),
            .lparen => try self.parseParenExpr(),
            .lcurly => try self.parseBlockExpr(),
            .keyword_proc, .keyword_fn => try self.parseFunctionLike(self.current().tag, false, false),
            .keyword_extern => try self.parseExternDecl(),
            .keyword_any => blk: {
                const any_type = ast.AnyType{ .loc = self.currentLoc() };
                self.advance();
                break :blk try self.alloc(ast.Expr, .{ .BuiltinType = .{ .Any = any_type } });
            },
            .keyword_type => blk: {
                const type_type = ast.TypeType{ .loc = self.currentLoc() };
                self.advance();
                break :blk try self.alloc(ast.Expr, .{ .BuiltinType = .{ .Type = type_type } });
            },
            .keyword_noreturn => blk: {
                const noreturn_type = ast.NoreturnType{ .loc = self.currentLoc() };
                self.advance();
                break :blk try self.alloc(ast.Expr, .{ .BuiltinType = .{ .Noreturn = noreturn_type } });
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
                break :blk try self.alloc(ast.Expr, .{ .Import = .{ .expr = expr, .loc = loc } });
            },
            .keyword_typeof => blk: {
                const start = try self.beginKeywordParen(.keyword_typeof);
                const expr = try self.parseExpr(0, .expr);
                try self.endParen();
                break :blk try self.alloc(ast.Expr, .{ .TypeOf = .{ .expr = expr, .loc = start } });
            },
            .keyword_async => blk: {
                const loc = self.currentLoc();
                self.advance(); // "async"
                switch (self.current().tag) {
                    .keyword_proc, .keyword_fn => break :blk try self.parseFunctionLike(self.current().tag, false, true),
                    else => {
                        const body = try self.parseBlockExpr();
                        break :blk try self.alloc(ast.Expr, .{ .Async = .{ .body = body, .loc = loc } });
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
                var value: ?*ast.Expr = null;
                if (self.current().tag == .colon) {
                    self.advance();
                    const name = try self.expectIdent();
                    label = name.bytes;
                }
                if (!self.isStmtTerminator()) {
                    value = try self.parseExpr(0, .expr);
                }
                const break_expr = ast.Break{ .loc = break_token.loc, .label = label, .value = value };
                break :blk try self.alloc(ast.Expr, .{ .Break = break_expr });
            },
            .keyword_continue => blk: {
                const continue_token = self.current();
                self.advance();
                const continue_expr = ast.Continue{ .loc = continue_token.loc };
                break :blk try self.alloc(ast.Expr, .{ .Continue = continue_expr });
            },
            .keyword_unreachable => blk: {
                const unreachable_token = self.current();
                self.advance();
                const unreachable_expr = ast.Unreachable{ .loc = unreachable_token.loc };
                break :blk try self.alloc(ast.Expr, .{ .Unreachable = unreachable_expr });
            },
            .keyword_null => blk: {
                const null_token = self.current();
                self.advance();
                const null_expr = ast.Null{ .loc = null_token.loc };
                break :blk try self.alloc(ast.Expr, .{ .Null = null_expr });
            },
            .keyword_defer => blk: {
                const defer_token = self.current();
                self.advance();
                const deferred = try self.parseExpr(0, .expr);
                const defer_expr = ast.Defer{ .expr = deferred, .loc = defer_token.loc };
                break :blk try self.alloc(ast.Expr, .{ .Defer = defer_expr });
            },
            .keyword_errdefer => blk: {
                const errdefer_token = self.current();
                self.advance();
                const deferred = try self.parseExpr(0, .expr);
                const errdefer_expr = ast.ErrDefer{ .expr = deferred, .loc = errdefer_token.loc };
                break :blk try self.alloc(ast.Expr, .{ .ErrDefer = errdefer_expr });
            },
            else => {
                std.debug.print("Unexpected token in expression: {}\n", .{tag});
                return error.UnexpectedToken;
            },
        };
    }

    inline fn toInfixOp(tag: Token.Tag) ast.InfixOp {
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

    fn parseExpr(self: *Parser, min_bp: u8, comptime mode: ParseMode) !*ast.Expr {
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
                        left = try self.alloc(ast.Expr, .{ .ErrUnwrap = .{ .expr = left, .loc = loc } });
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
                            .keyword_catch => try self.parseCatchExpr(left),
                            else => unreachable,
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
                left = try self.alloc(ast.Expr, .{ .Infix = .{ .op = toInfixOp(tag), .left = left, .right = right, .loc = loc } });
                continue;
            }

            break;
        }
        // DEBUG: show token at parseExpr exit
        std.debug.print("[debug] parseExpr exit: current={any}\n", .{self.current().tag});
        return left;
    }

    //=================================================================
    // Common element parsers
    //=================================================================

    fn parseStructLiteral(self: *Parser) anyerror!*ast.Expr {
        const struct_start = self.currentLoc();
        var entries = self.list(ast.StructFieldValue);
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
        const struct_lit = ast.StructLiteral{ .fields = entries, .loc = struct_start };
        return self.alloc(ast.Expr, .{ .Struct = struct_lit });
    }

    fn parseIndex(self: *Parser, collection: *ast.Expr) anyerror!*ast.Expr {
        const index_start = self.currentLoc();
        const index = try self.parseExpr(0, .expr);
        try self.expect(.rsquare);
        const index_expr = ast.Index{ .collection = collection, .index = index, .loc = index_start };
        return self.alloc(ast.Expr, .{ .Index = index_expr });
    }

    fn parseField(self: *Parser, parent: *ast.Expr) anyerror!*ast.Expr {
        const field_token = self.current();
        var is_tuple = false;
        switch (self.current().tag) {
            .identifier => self.advance(),
            .integer_literal => {
                is_tuple = true;
                self.advance();
            },
            else => {
                std.debug.print("Expected identifier or integer after '.', but got: {}\n", .{self.current().tag});
                return error.UnexpectedToken;
            },
        }
        const field = ast.Field{ .parent = parent, .field = self.slice(field_token), .is_tuple = is_tuple, .loc = field_token.loc };
        return self.alloc(ast.Expr, .{ .Field = field });
    }

    fn parseCommaExprListUntil(self: *Parser, comptime end_tag: Token.Tag) !std.array_list.Managed(*ast.Expr) {
        var items = self.list(*ast.Expr);
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

    fn parseCall(self: *Parser, callee: *ast.Expr) anyerror!*ast.Expr {
        const args = try self.parseCommaExprListUntil(.rparen);
        const call = ast.Call{ .callee = callee, .args = args, .loc = self.currentLoc() };
        return self.alloc(ast.Expr, .{ .Call = call });
    }

    fn finishParsingExprList(self: *Parser, comptime end_tag: Token.Tag, first_element: *ast.Expr) !std.array_list.Managed(*ast.Expr) {
        var elements = self.list(*ast.Expr);
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

    inline fn parseDeref(self: *Parser, expr: *ast.Expr) !*ast.Expr {
        const loc = self.currentLoc();
        // Current token was .dotstar, already consumed by caller.
        return self.alloc(ast.Expr, .{ .Deref = .{ .expr = expr, .loc = loc } });
    }

    inline fn parsePostfixAfterDot(self: *Parser, left: *ast.Expr) anyerror!*ast.Expr {
        return switch (self.current().tag) {
            .keyword_await => try self.parseAwait(left),
            .caret, .b_or, .percent, .question => try self.parseCastSigil(left),
            else => try self.parseField(left),
        };
    }

    fn parseCastParen(self: *Parser, expr: *ast.Expr) anyerror!*ast.Expr {
        const loc = self.currentLoc();
        // Current token was .dot_lparen, already consumed by caller.
        // Parse a type until ')'
        const ty = try self.parseExpr(0, .type);
        try self.expect(.rparen);
        return self.alloc(ast.Expr, .{ .Cast = .{ .expr = expr, .ty = ty, .kind = .normal, .loc = loc } });
    }

    fn parseCastSigil(self: *Parser, expr: *ast.Expr) anyerror!*ast.Expr {
        const loc = self.currentLoc();
        const op_tag = self.current().tag;
        const kind: ast.CastKind = switch (op_tag) {
            .caret => .bitcast,
            .b_or => .saturate,
            .percent => .wrap,
            .question => .checked,
            else => unreachable,
        };
        self.advance();
        const ty = try self.parseExpr(0, .type);
        return self.alloc(ast.Expr, .{ .Cast = .{ .expr = expr, .ty = ty, .kind = kind, .loc = loc } });
    }

    inline fn parseAwait(self: *Parser, expr: *ast.Expr) !*ast.Expr {
        const loc = self.currentLoc();
        try self.expect(.keyword_await);
        return self.alloc(ast.Expr, .{ .Await = .{ .expr = expr, .loc = loc } });
    }

    inline fn parseReturn(self: *Parser) !*ast.Expr {
        const return_token = self.current();
        self.advance();
        var value: ?*ast.Expr = null;
        if (!self.isStmtTerminator()) {
            value = try self.parseExpr(0, .expr);
        }
        if (!self.isStmtTerminator()) {
            try self.expect(.eos);
        }
        const return_expr = ast.Return{ .value = value, .loc = return_token.loc };
        return self.alloc(ast.Expr, .{ .Return = return_expr });
    }

    fn parseBlock(self: *Parser) !ast.Block {
        var items = self.list(ast.Decl);
        const loc = try self.beginBrace();
        while (self.current().tag != .rcurly and self.current().tag != .eof) {
            const stmt = try self.parseDecl();
            try items.append(stmt);
        }
        try self.endBrace();
        return .{ .items = items, .loc = loc };
    }

    fn parseBlockExpr(self: *Parser) !*ast.Expr {
        const block = try self.parseBlock();
        return self.alloc(ast.Expr, .{ .Block = block });
    }

    inline fn parseExprOrBlock(self: *Parser) anyerror!*ast.Expr {
        if (self.current().tag == .lcurly) {
            return try self.parseBlockExpr();
        } else {
            return try self.parseExpr(0, .expr);
        }
    }

    fn parseClosure(self: *Parser) !*ast.Expr {
        const closure_start = self.currentLoc();
        try self.expect(.b_or);
        var params = self.list(ast.Param);
        if (self.current().tag != .b_or) {
            const p = infixBp(.b_or).?; // {.l_bp, .r_bp}
            const r_bp = p[1];
            const barrier: u8 = r_bp + 1; // stop before consuming '|'
            while (true) {
                const param_start = self.currentLoc();
                // Parse parameter pattern; do not consume '|' as bitwise-or.
                const pat_expr = try self.parseExpr(barrier, .expr_no_struct);
                var ty: ?*ast.Expr = null;
                var value: ?*ast.Expr = null;
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
                    std.debug.print("Expected ',' or '|' after closure parameter, but got: {}\n", .{self.current().tag});
                    return error.UnexpectedToken;
                }
            }
        }
        try self.expect(.b_or);

        var return_type: ?*ast.Expr = null;
        var body: *ast.Expr = undefined;
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

        const closure = ast.Closure{ .params = params, .result_ty = return_type, .body = body, .loc = closure_start };
        return self.alloc(ast.Expr, .{ .Closure = closure });
    }

    fn parseCatchExpr(self: *Parser, expr: *ast.Expr) anyerror!*ast.Expr {
        const catch_loc = self.currentLoc();
        var binding: ?ast.Ident = null;
        if (self.current().tag == .b_or) {
            self.advance();
            const name = try self.expectIdent();
            binding = ast.Ident{ .name = name.bytes, .loc = name.loc };
            try self.expect(.b_or);
        }
        const handler: *ast.Expr = try self.parseExprOrBlock();
        const catch_expr = ast.Catch{ .expr = expr, .binding = binding, .handler = handler, .loc = catch_loc };
        return self.alloc(ast.Expr, .{ .Catch = catch_expr });
    }

    fn parseIfExpr(self: *Parser) !*ast.Expr {
        const if_start = self.currentLoc();
        self.advance(); // "if"
        const condition = try self.parseExpr(0, .expr_no_struct);
        const then_block = try self.parseBlock();
        var else_block: ?*ast.Expr = null;
        if (self.current().tag == .keyword_else) {
            self.advance();
            else_block = try self.parseExprOrBlock();
        }
        const if_expr = ast.If{
            .cond = condition,
            .then_block = then_block,
            .else_block = else_block,
            .loc = if_start,
        };
        return try self.alloc(ast.Expr, .{ .If = if_expr });
    }

    fn parseWhileExpr(self: *Parser) !*ast.Expr {
        const while_start = self.currentLoc();
        self.advance(); // "while"
        var condition: ?*ast.Expr = null;
        var pattern: ?*ast.Pattern = null;
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
        const while_expr = ast.While{
            .cond = condition,
            .pattern = pattern,
            .body = body,
            .loc = while_start,
            .is_pattern = false,
            .label = null,
        };
        return try self.alloc(ast.Expr, .{ .While = while_expr });
    }

    fn parseLabeledLoop(self: *Parser, label_name: []const u8) anyerror!*ast.Expr {
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
                std.debug.print("Expected 'for' or 'while' after label, got: {}\n", .{self.current().tag});
                return error.UnexpectedToken;
            },
        };
    }

    fn parseForExpr(self: *Parser) !*ast.Expr {
        const for_start = self.currentLoc();
        self.advance(); // "for"
        const pattern = try self.parsePattern();
        try self.expect(.keyword_in);
        const iterable = try self.parseExpr(0, .expr_no_struct);
        const body = try self.parseBlock();
        const for_expr = ast.For{
            .pattern = pattern,
            .iterable = iterable,
            .body = body,
            .loc = for_start,
        };
        return try self.alloc(ast.Expr, .{ .For = for_expr });
    }

    fn parseMatchExpr(self: *Parser) !*ast.Expr {
        const start = self.currentLoc();
        self.advance(); // "match"

        const scrutinee = try self.parseExpr(0, .expr_no_struct);

        try self.expect(.lcurly);
        var arms = self.list(ast.MatchArm);
        while (self.current().tag != .rcurly and self.current().tag != .eof) {
            const pat_expr = try self.parsePattern();

            var guard: ?*ast.Expr = null;
            if (self.current().tag == .keyword_if) {
                self.advance();
                guard = try self.parseExpr(0, .expr_no_struct);
            }

            try self.expect(.fatarrow);

            const body: *ast.Expr = try self.parseExprOrBlock();

            _ = self.consumeIf(.comma);

            try arms.append(.{ .pattern = pat_expr, .guard = guard, .body = body, .loc = self.currentLoc() });
        }
        try self.expect(.rcurly);

        return try self.alloc(ast.Expr, .{ .Match = .{ .expr = scrutinee, .arms = arms, .loc = start } });
    }

    //=================================================================
    // Patterns
    // =================================================================

    fn parsePattern(self: *Parser) !*ast.Pattern {
        return try self.parsePatOr();
    }

    fn parsePatOr(self: *Parser) !*ast.Pattern {
        const current_loc = self.currentLoc();
        const first = try self.parsePatRange();
        if (self.current().tag != .b_or) return first; // '|' token; you already use .b_or for '|'

        var alts = self.list(*ast.Pattern);
        try alts.append(first);
        while (self.current().tag == .b_or) {
            self.advance();
            try alts.append(try self.parsePatRange());
        }
        const or_pat = ast.OrPattern{ .loc = current_loc, .alts = alts };
        return try self.alloc(ast.Pattern, .{ .Or = or_pat });
    }

    fn parsePatRange(self: *Parser) !*ast.Pattern {
        // Handle prefix/open ranges first:  ..X  or  ..=X
        if (self.current().tag == .dotdot or self.current().tag == .dotdoteq) {
            const start_loc = self.currentLoc();
            const incl = (self.current().tag == .dotdoteq);
            self.advance();
            const end = try self.parseConstExprForRangeEnd();
            return try self.alloc(ast.Pattern, .{ .Range = .{
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
            return try self.alloc(ast.Pattern, .{ .Range = .{
                .loc = loc,
                .start = lhs_expr,
                .end = rhs,
                .inclusive_right = incl,
            } });
        }

        return left;
    }

    fn patternToConstExpr(self: *Parser, pat: *ast.Pattern) !*ast.Expr {
        return switch (pat.*) {
            .Literal => |lit_expr_ptr| lit_expr_ptr, // you already store the literal as an *ast.Expr
            .Path => |p| try self.pathToConstExpr(p.segments),
            .Binding => |b| blk: {
                // Turn binding name into an expr; the checker can complain if it's not const.
                const ident = ast.Ident{ .name = b.name, .loc = b.loc };
                break :blk try self.alloc(ast.Expr, .{ .Ident = ident });
            },
            .Wildcard => {
                std.debug.print("Wildcard '_' is not valid as a constant in a range pattern\n", .{});
                return error.UnexpectedToken;
            },
            // Disallow complex patterns on the LHS of a range.
            else => {
                std.debug.print("Left side of a range pattern must be a const-like literal/path/binding, got pattern tag\n", .{});
                return error.UnexpectedToken;
            },
        };
    }

    fn patternToBindingName(pat: *ast.Pattern) ![]const u8 {
        return switch (pat.*) {
            .Binding => pat.Binding.name,
            .Path => blk: {
                if (pat.Path.segments.items.len == 1) {
                    break :blk pat.Path.segments.items[0].name;
                } else {
                    std.debug.print("Expected simple identifier for binding name, got path: {}\n", .{pat.Path});
                    return error.InvalidPatternForBinding;
                }
            },
            else => {
                std.debug.print("Expected simple identifier for binding name, got pattern: {}\n", .{pat});
                return error.InvalidPatternForBinding;
            },
        };
    }

    fn parsePatAt(self: *Parser) !*ast.Pattern {
        // binding '@' pattern: IDENT '@' subpattern
        // But IDENT alone might be a Path/Binding; we need a lookahead.
        const p = try self.parsePatPrimary();

        if (self.current().tag == .at) { // '@'
            const current_loc = self.currentLoc();
            // Left must be a binding name (IDENT) to be valid; let checker enforce that
            self.advance();
            const sub = try self.parsePatAt(); // right-assoc
            // Extract binder name if `p` is a simple Path/Binding; otherwise checker will error
            const name = try patternToBindingName(p);
            const at = ast.AtPattern{ .loc = current_loc, .binder = name, .pattern = sub };
            return try self.alloc(ast.Pattern, .{ .At = at });
        }
        return p;
    }

    fn parsePatPrimary(self: *Parser) !*ast.Pattern {
        switch (self.current().tag) {
            // .underscore_like => { /* see note below */ },
            .char_literal, .string_literal, .raw_string_literal, .byte_literal, .byte_char_literal, .byte_string_literal, .raw_byte_string_literal, .integer_literal, .float_literal, .keyword_true, .keyword_false => {
                const lit = try self.nud(self.current().tag, .expr_no_struct); // reuse literal expr nud
                return try self.alloc(ast.Pattern, .{ .Literal = lit });
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
                const range = ast.RangePattern{
                    .loc = start_loc,
                    .start = null,
                    .end = end,
                    .inclusive_right = incl,
                };
                return try self.alloc(ast.Pattern, .{ .Range = range });
            },
            .identifier => return try self.parsePathishPattern(),
            else => {
                std.debug.print("Unexpected token in pattern: {}\n", .{self.current().tag});
                return error.UnexpectedToken;
            },
        }
    }

    fn parseTuplePattern(self: *Parser) anyerror!*ast.Pattern {
        const loc = self.currentLoc();
        try self.expect(.lparen);
        var elems = self.list(*ast.Pattern);
        if (self.current().tag != .rparen) {
            while (true) {
                try elems.append(try self.parsePattern());
                if (!self.consumeIf(.comma)) break;
            }
        }
        try self.expect(.rparen);
        const tuple_pat = ast.TuplePattern{ .loc = loc, .elems = elems };
        return try self.alloc(ast.Pattern, .{ .Tuple = tuple_pat });
    }

    fn parsePathishPattern(self: *Parser) anyerror!*ast.Pattern {
        // Collect a dotted path: Foo.Bar.Baz
        var segs = self.list(ast.Ident);
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
                var elems = self.list(*ast.Pattern);
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
                const tuple_pat = ast.VariantTuplePattern{ .loc = loc, .path = path, .elems = elems };
                return try self.alloc(ast.Pattern, .{ .VariantTuple = tuple_pat });
            },
            .lcurly => { // struct/variant struct data; supports {..., ..}
                self.advance();
                var fields = self.list(ast.StructPatternField);
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

                    var pat: *ast.Pattern = undefined;
                    if (self.current().tag == .colon) {
                        self.advance();
                        pat = try self.parsePattern();
                    } else {
                        // field shorthand: `name` == bind name
                        pat = try self.alloc(
                            ast.Pattern,
                            .{ .Binding = .{ .loc = loc, .name = name } },
                        );
                    }
                    try fields.append(.{ .name = name, .pattern = pat, .loc = loc });

                    if (!self.consumeIf(.comma)) break;
                }
                try self.expect(.rcurly);
                // disambiguation left to checker: path may be a struct type or enum variant
                return try self.alloc(
                    ast.Pattern,
                    .{ .VariantStruct = .{ .loc = pat_loc, .path = path, .fields = fields, .has_rest = has_rest } },
                );
            },
            .dotdot, .dotdoteq => { // range like: Foo .. Bar  (typically literals/consts; allow path here)
                const incl = (self.current().tag == .dotdoteq);
                const loc = self.currentLoc();
                self.advance();
                const rhs = try self.parseConstExprForRangeEnd();
                const start_expr = try self.pathToConstExpr(path);
                return try self.alloc(ast.Pattern, .{ .Range = .{
                    .loc = loc,
                    .start = start_expr,
                    .end = rhs,
                    .inclusive_right = incl,
                } });
            },
            else => {
                // bare identifier/path: binding or const-path pattern; let checker decide
                if (path.items.len == 1 and std.mem.eql(u8, path.items[0].name, "_")) {
                    return try self.alloc(ast.Pattern, .{ .Wildcard = .{ .loc = path.items[0].loc } });
                }
                // default to Binding; checker can upgrade to const-path pattern if name resolves to a const
                if (path.items.len == 1) {
                    return try self.alloc(ast.Pattern, .{
                        .Binding = .{ .name = path.items[0].name, .loc = path.items[0].loc },
                    });
                }
                return try self.alloc(ast.Pattern, .{
                    .Path = .{ .segments = path, .loc = path.items[0].loc },
                });
            },
        }
    }

    fn parseSlicePattern(self: *Parser) anyerror!*ast.Pattern {
        try self.expect(.lsquare);
        var elems = self.list(*ast.Pattern);
        var has_rest = false;
        var rest_index: usize = 0;
        var rest_binding: ?*ast.Pattern = null;
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
                                ast.Pattern,
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
        return try self.alloc(ast.Pattern, .{
            .Slice = .{
                .loc = loc,
                .elems = elems,
                .has_rest = has_rest,
                .rest_index = rest_index,
                .rest_binding = rest_binding, // NEW
            },
        });
    }

    fn parseConstExprForRangeEnd(self: *Parser) !*ast.Expr {
        // use normal expr, semantic checker will ensure "const evaluable" and no side effects
        return self.parseExpr(0, .expr_no_struct);
    }

    fn pathToConstExpr(self: *Parser, path: std.array_list.Managed(ast.Ident)) !*ast.Expr {
        // Build an ast.Expr Ident/Field chain from the path for the checker to resolve.
        var expr: *ast.Expr = try self.alloc(ast.Expr, .{ .Ident = path.items[0] });
        var i: usize = 1;
        while (i < path.items.len) : (i += 1) {
            expr = try self.alloc(ast.Expr, .{ .Field = .{
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

    fn parseStructField(self: *Parser) !ast.StructField {
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

    fn parseStructFieldList(self: *Parser, end_tag: Token.Tag) !std.array_list.Managed(ast.StructField) {
        var fields = self.list(ast.StructField);
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
    ) !*ast.Expr {
        const struct_start = self.currentLoc();
        self.advance(); // "struct" / "union"
        try self.expect(.lcurly);
        const fields = try self.parseStructFieldList(.rcurly);
        const struct_type = ast.StructLikeType{ .is_extern = is_extern, .fields = fields, .loc = struct_start };
        if (tag == .keyword_struct) {
            return self.alloc(ast.Expr, .{ .BuiltinType = .{ .Struct = struct_type } });
        }
        return self.alloc(ast.Expr, .{ .BuiltinType = .{ .Union = struct_type } });
    }

    inline fn parsePointerType(self: *Parser) !*ast.Expr {
        const start_token = self.current();
        self.advance(); // "*"
        var is_const = false;
        if (self.current().tag == .keyword_const) {
            is_const = true;
            self.advance();
        }
        const elem_type = try self.parseExpr(0, .type);
        const ptr_type = ast.PointerType{ .elem = elem_type, .is_const = is_const, .loc = start_token.loc };
        return try self.alloc(ast.Expr, .{ .BuiltinType = .{ .Pointer = ptr_type } });
    }

    inline fn parseOptionalType(self: *Parser) !*ast.Expr {
        const start_token = self.current();
        self.advance(); // "?"
        const elem_type = try self.parseExpr(0, .type);
        const opt_type = ast.UnaryType{ .elem = elem_type, .loc = start_token.loc };
        return try self.alloc(ast.Expr, .{ .BuiltinType = .{ .Optional = opt_type } });
    }

    inline fn parseComplexType(self: *Parser) !*ast.Expr {
        const start = try self.beginKeywordParen(.keyword_complex);
        const elem_type = try self.parseExpr(0, .type);
        try self.endParen();
        const complex_type = ast.ComplexType{ .elem = elem_type, .loc = start };
        return try self.alloc(ast.Expr, .{ .BuiltinType = .{ .Complex = complex_type } });
    }

    inline fn parseSimdType(self: *Parser) !*ast.Expr {
        const start = try self.beginKeywordParen(.keyword_simd);
        const elem_type = try self.parseExpr(0, .type);
        try self.expect(.comma);
        const size_expr = try self.parseExpr(0, .expr);
        try self.endParen();
        const simd_type = ast.SimdType{ .elem = elem_type, .lanes = size_expr, .loc = start };
        return try self.alloc(ast.Expr, .{ .BuiltinType = .{ .Simd = simd_type } });
    }

    inline fn parseTensorType(self: *Parser) !*ast.Expr {
        const start = try self.beginKeywordParen(.keyword_tensor);
        const first = try self.parseExpr(0, .expr);
        try self.expect(.comma);
        var shape = try self.finishParsingExprList(.rparen, first);
        const elem_type = shape.pop().?;
        const tensor_type = ast.TensorType{ .elem = elem_type, .shape = shape, .loc = start };
        return try self.alloc(ast.Expr, .{ .BuiltinType = .{ .Tensor = tensor_type } });
    }

    //=================================================================
    // Array-like / Map (type or literal)
    //=================================================================

    fn parseMapTypeOrLiteral(self: *Parser, key_expr: *ast.Expr, start_loc: Loc) !*ast.Expr {
        // caller consumed ":" already
        const value_type = try self.parseExpr(0, .type);
        return switch (self.current().tag) {
            .rsquare => blk: {
                try self.expect(.rsquare);
                const map_type = ast.MapType{ .key = key_expr, .value = value_type, .loc = start_loc };
                break :blk try self.alloc(ast.Expr, .{ .BuiltinType = .{ .MapType = map_type } });
            },
            .comma => blk: {
                // literal form: [key: value, ...]
                self.advance();
                var entries = self.list(ast.KeyValue);
                try entries.append(.{ .key = key_expr, .value = value_type, .loc = start_loc });
                while (self.current().tag != .rsquare and self.current().tag != .eof) {
                    const k = try self.parseExpr(0, .expr);
                    try self.expect(.colon);
                    const v = try self.parseExpr(0, .expr);
                    try entries.append(.{ .key = k, .value = v, .loc = self.currentLoc() });
                    if (!self.consumeIf(.comma)) break;
                }
                try self.expect(.rsquare);
                const map = ast.Map{ .entries = entries, .loc = start_loc };
                break :blk try self.alloc(ast.Expr, .{ .Map = map });
            },
            else => {
                std.debug.print("Expected ']' or ',' in map type/literal, but got: {}\n", .{self.current().tag});
                return error.UnexpectedToken;
            },
        };
    }

    fn parseArrayLike(self: *Parser) !*ast.Expr {
        const start_token = self.current();
        self.advance(); // "["

        return switch (self.current().tag) {
            // "[]T" slice type OR "[]" empty array literal
            .rsquare => blk: {
                self.advance(); // "]"
                switch (self.current().tag) {
                    .eos, .rcurly, .rparen, .rsquare, .comma, .colon => {
                        const array = ast.Array{ .elems = self.list(*ast.Expr), .loc = start_token.loc };
                        break :blk try self.alloc(ast.Expr, .{ .Array = array });
                    },
                    else => {
                        const elem_type = try self.parseExpr(0, .type);
                        const slice_type = ast.UnaryType{ .elem = elem_type, .loc = start_token.loc };
                        break :blk try self.alloc(ast.Expr, .{ .BuiltinType = .{ .Slice = slice_type } });
                    },
                }
            },

            // "[dyn]T" dynamic array type
            .keyword_dyn => blk: {
                self.advance();
                try self.expect(.rsquare);
                const elem_type = try self.parseExpr(0, .type);
                const dyn_array_type = ast.UnaryType{ .elem = elem_type, .loc = start_token.loc };
                break :blk try self.alloc(ast.Expr, .{ .BuiltinType = .{ .DynArray = dyn_array_type } });
            },

            // starts with expression -> could be sized array type "[N]T", map "[K:V]" / map literal, or array literal "[a, b, ...]"
            else => blk: {
                const first_expr = try self.parseExpr(0, .expr);
                switch (self.current().tag) {
                    .rsquare => {
                        // "[N]T" (array type)
                        self.advance();
                        const elem_type = try self.parseExpr(0, .type);
                        const array_type = ast.ArrayType{ .elem = elem_type, .size = first_expr, .loc = start_token.loc };
                        break :blk try self.alloc(ast.Expr, .{ .BuiltinType = .{ .Array = array_type } });
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
                        const array = ast.Array{ .elems = elements, .loc = start_token.loc };
                        break :blk try self.alloc(ast.Expr, .{ .Array = array });
                    },
                    else => {
                        std.debug.print("Expected ']', ':', or ',' in array-like, but got: {}\n", .{self.current().tag});
                        return error.UnexpectedToken;
                    },
                }
            },
        };
    }

    fn parseParenExpr(self: *Parser) !*ast.Expr {
        const start_token = self.current();
        self.advance(); // "("
        return switch (self.current().tag) {
            .rparen => blk: {
                // empty tuple "()"
                self.advance();
                const tuple = ast.Tuple{ .elems = self.list(*ast.Expr), .loc = start_token.loc };
                break :blk try self.alloc(ast.Expr, .{ .Tuple = tuple });
            },
            else => blk: {
                const expr = try self.parseExpr(0, .expr);
                if (self.current().tag == .comma) {
                    self.advance();
                    const elements = try self.finishParsingExprList(.rparen, expr);
                    const tuple = ast.Tuple{ .elems = elements, .loc = start_token.loc };
                    break :blk try self.alloc(ast.Expr, .{ .Tuple = tuple });
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

    inline fn parseOptionalReturnType(self: *Parser) !?*ast.Expr {
        return switch (self.current().tag) {
            .lcurly, .eos => null,
            else => try self.parseExpr(0, .type),
        };
    }

    fn parseExternDecl(self: *Parser) !*ast.Expr {
        self.advance(); // "extern"
        switch (self.current().tag) {
            .keyword_async => {
                self.advance();
                switch (self.current().tag) {
                    .keyword_proc, .keyword_fn => return try self.parseFunctionLike(self.current().tag, true, true),
                    else => {
                        std.debug.print("Expected 'proc' or 'fn' after 'extern async', but got: {}\n", .{self.current().tag});
                        return error.UnexpectedToken;
                    },
                }
            },
            .keyword_proc, .keyword_fn => return try self.parseFunctionLike(self.current().tag, true, false),
            .keyword_struct => return try self.parseStructLikeType(.keyword_struct, true),
            .keyword_enum => return try self.parseEnumType(true),
            .keyword_union => return try self.parseStructLikeType(.keyword_union, true),
            else => {
                std.debug.print("Expected 'proc', 'fn', or string literal after 'extern', but got: {}\n", .{self.current().tag});
                return error.UnexpectedToken;
            },
        }
    }

    fn parseFunctionLike(self: *Parser, tag: Token.Tag, comptime is_extern: bool, is_async: bool) !*ast.Expr {
        const start_token = self.current();
        self.advance(); // "proc" or "fn"
        try self.expect(.lparen);

        var params = self.list(ast.Param);
        while (self.current().tag != .rparen and self.current().tag != .eof) {
            const param_start = self.currentLoc();
            const param_attrs = try self.parseOptionalAttributes();
            var pat: ?*ast.Expr = try self.parseExpr(0, .expr);
            var ty: *ast.Expr = undefined;
            var value: ?*ast.Expr = null;

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
                std.debug.print("Expected ':', ',', or ')' after parameter, but got: {}\n", .{self.current().tag});
                return error.UnexpectedToken;
            }

            try params.append(.{ .pat = pat, .ty = ty, .value = value, .loc = param_start, .attrs = param_attrs });
            if (self.current().tag != .comma) break;
            self.advance();
        }
        try self.expect(.rparen);

        const return_type: ?*ast.Expr = try self.parseOptionalReturnType();

        var body: ?ast.Block = null;
        var raw_asm: ?[]const u8 = null;
        if (self.current().tag == .lcurly) {
            body = try self.parseBlock();
        } else if (self.current().tag == .raw_asm_block) {
            // Capture the raw asm text as-is from the source
            const tok = self.current();
            raw_asm = self.slice(tok);
            self.advance();
        }

        const func = ast.Function{
            .is_proc = (tag == .keyword_proc),
            .params = params,
            .result_ty = return_type,
            .body = body,
            .loc = start_token.loc,
            .is_async = is_async,
            .is_variadic = false, // TODO: i could just use  "any" as last param type
            .is_extern = is_extern,
            .raw_asm = raw_asm,
        };
        return try self.alloc(ast.Expr, .{ .Function = func });
    }

    //=================================================================
    // Metaprogramming: comptime, code, insert, mlir
    //=================================================================

    fn parseComptime(self: *Parser) !*ast.Expr {
        self.advance(); // "comptime"
        if (self.current().tag == .lcurly) {
            const blk = try self.parseBlock();
            return try self.alloc(ast.Expr, .{ .Comptime = .{ .Block = blk } });
        } else {
            const expr = try self.parseExpr(0, .expr);
            return try self.alloc(ast.Expr, .{ .Comptime = .{ .Expr = expr } });
        }
    }

    fn parseCodeBlock(self: *Parser) !*ast.Expr {
        const start = self.currentLoc();
        self.advance(); // "code"
        const blk = try self.parseBlock();
        return try self.alloc(ast.Expr, .{ .Code = .{ .block = blk, .loc = start } });
    }

    fn parseInsert(self: *Parser) !*ast.Expr {
        const start = self.currentLoc();
        self.advance(); // "insert"
        const expr = try self.parseExpr(0, .expr);
        return try self.alloc(ast.Expr, .{ .Insert = .{ .expr = expr, .loc = start } });
    }

    fn parseMlir(self: *Parser) !*ast.Expr {
        const start = self.currentLoc();
        self.advance(); // "mlir"
        var kind: ast.MlirKind = .Module;
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
        return try self.alloc(ast.Expr, .{ .Mlir = .{ .kind = kind, .text = raw, .loc = start } });
    }

    //=================================================================
    // Enums / Variants
    //=================================================================

    inline fn parseEnumType(self: *Parser, comptime is_extern: bool) !*ast.Expr {
        const enum_start = self.currentLoc();
        self.advance(); // "enum"

        var backing_type: ?*ast.Expr = null;
        if (self.current().tag == .lparen) {
            self.advance();
            backing_type = try self.parseExpr(0, .type);
            try self.expect(.rparen);
        }

        try self.expect(.lcurly);

        var fields = self.list(ast.EnumField);
        while (self.current().tag != .rcurly and self.current().tag != .eof) {
            const field_start = self.currentLoc();
            const field_attrs = try self.parseOptionalAttributes();
            const name = try self.expectIdent();
            const value = try self.parseOptionalInitializer(.expr);
            try fields.append(.{ .name = name.bytes, .value = value, .loc = field_start, .attrs = field_attrs });
            if (!self.consumeIf(.comma)) break;
        }

        try self.expect(.rcurly);
        const enum_type = ast.EnumType{ .is_extern = is_extern, .fields = fields, .discriminant = backing_type, .loc = enum_start, .attrs = null };
        return self.alloc(ast.Expr, .{ .BuiltinType = .{ .Enum = enum_type } });
    }

    inline fn parseErrorType(self: *Parser) !*ast.Expr {
        return self.parseVariantLikeType(true);
    }

    inline fn parseVariantType(self: *Parser) !*ast.Expr {
        return self.parseVariantLikeType(false);
    }

    fn parseVariantLikeType(self: *Parser, comptime is_error: bool) !*ast.Expr {
        // Rust-like enum with payloads
        const variant_start = self.currentLoc();
        self.advance(); // "variant"
        try self.expect(.lcurly);

        var fields = self.list(ast.VariantField);

        while (self.current().tag != .rcurly and self.current().tag != .eof) {
            const case_start = self.currentLoc();
            const case_attrs = try self.parseOptionalAttributes();
            while (self.current().tag == .eos) self.advance();
            const case_name = try self.expectIdent();

            switch (self.current().tag) {
                .lparen => {
                    // Tuple-like payload
                    self.advance();
                    var types = self.list(*ast.Expr);
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
        const variant_type = ast.VariantLikeType{ .fields = fields, .loc = variant_start };
        if (is_error)
            return self.alloc(ast.Expr, .{ .BuiltinType = .{ .Error = variant_type } });
        return self.alloc(ast.Expr, .{ .BuiltinType = .{ .Variant = variant_type } });
    }
};
