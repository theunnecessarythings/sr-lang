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

    const ParseMode = enum { expr, type };

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
            .lparen, .lsquare, .lcurly, .dot, .dotdot, .dotdoteq => 95,
            else => null,
        };
    }

    inline fn prefixBp(tag: Token.Tag) u8 {
        return switch (tag) {
            .plus, .minus, .b_and, .star, .bang, .dotdot, .dotdoteq => 90,
            else => unreachable,
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

    fn parseDecl(self: *Parser) !ast.Decl {
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
            try self.expect(.eos);
        }
        return .{ .lhs = lhs, .rhs = rhs, .ty = ty, .loc = loc, .is_const = is_const, .is_assign = is_assign };
    }

    fn nud(self: *Parser, tag: Token.Tag) anyerror!*ast.Expr {
        // prefix
        switch (tag) {
            .plus, .minus, .b_and, .bang, .dotdot, .dotdoteq => {
                const op_tok = self.current();
                self.advance();
                const rhs = try self.parseExpr(prefixBp(tag), .expr);
                const unary = ast.Prefix{ .op = toPrefixOp(op_tok.tag), .right = rhs, .loc = op_tok.loc };
                return try self.alloc(ast.Expr, .{ .Prefix = unary });
            },
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
            .identifier => blk: {
                const ident = ast.Ident{ .name = self.slice(self.current()), .loc = self.currentLoc() };
                self.advance();
                break :blk try self.alloc(ast.Expr, .{ .Ident = ident });
            },
            .lsquare => try self.parseArrayLike(),
            .lparen => try self.parseParenExpr(),
            .lcurly => try self.parseBlockExpr(),
            .keyword_proc, .keyword_fn => try self.parseFunctionLike(self.current().tag),
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
            .keyword_struct => try self.parseStructLikeType(.keyword_struct),
            .keyword_union => try self.parseStructLikeType(.keyword_union),
            .keyword_enum => try self.parseEnumType(),
            .keyword_variant => try self.parseVariantType(),
            .keyword_return => try self.parseReturn(),
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
            else => unreachable,
        };
    }

    fn parseExpr(self: *Parser, min_bp: u8, comptime mode: ParseMode) !*ast.Expr {
        var left = try self.nud(self.current().tag);

        while (true) {
            const tag = self.current().tag;

            // Postfix — but do NOT preempt infix ".." / "..="
            if (postfixBp(tag)) |l_bp| {
                if (l_bp >= min_bp) {
                    // do not start a struct literal in type context
                    if (tag == .lcurly and mode == .type) break;

                    const is_range_postfix = (tag == .dotdot or tag == .dotdoteq);
                    const should_let_infix_win = is_range_postfix and !self.nextIsTerminator();

                    if (!should_let_infix_win) {
                        self.advance();
                        left = switch (tag) {
                            .lparen => try self.parseCall(left),
                            .lsquare => try self.parseIndex(left),
                            .dot => try self.parseField(left),
                            .lcurly => try self.parseStructLiteral(),
                            // .dotdot, .dotdoteq => blk: {
                            //     // only reached when nextIsTerminator() == true → x.. / x..=
                            //     const range = ast.Range{
                            //         .start = left,
                            //         .end = null,
                            //         .inclusive_right = (tag == .dotdoteq),
                            //         .loc = self.currentLoc(),
                            //     };
                            //     break :blk try self.alloc(ast.Expr, .{ .Range = range });
                            // },
                            else => unreachable,
                        };
                        continue;
                    }
                }
            }

            // Infix (this now gets 1 .. 3)
            if (infixBp(tag)) |bp| {
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
            if (self.current().tag != .comma) break;
            self.advance();
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
                if (self.current().tag != .comma) break;
                self.advance();
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
            if (self.current().tag != .comma) break;
            self.advance();
        }
        try self.expect(end_tag);
        return elements;
    }

    //=================================================================
    // Statements / blocks
    //=================================================================

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

    //=================================================================
    // Types (building blocks)
    //=================================================================

    fn parseStructField(self: *Parser) !ast.StructField {
        const start = self.currentLoc();
        const name = try self.expectIdent();
        try self.expect(.colon);
        const ty = try self.parseExpr(0, .type);
        const value = try self.parseOptionalInitializer(.expr);
        return .{ .name = name.bytes, .ty = ty, .value = value, .loc = start };
    }

    fn parseStructFieldList(self: *Parser, end_tag: Token.Tag) !std.array_list.Managed(ast.StructField) {
        var fields = self.list(ast.StructField);
        while (self.current().tag != end_tag and self.current().tag != .eof) {
            try fields.append(try self.parseStructField());
            if (self.current().tag != .comma) break;
            self.advance();
        }
        try self.expect(end_tag);
        return fields;
    }

    inline fn parseStructLikeType(self: *Parser, comptime tag: Token.Tag) !*ast.Expr {
        const struct_start = self.currentLoc();
        self.advance(); // "struct" / "union"
        try self.expect(.lcurly);
        const fields = try self.parseStructFieldList(.rcurly);
        const struct_type = ast.StructLikeType{ .fields = fields, .loc = struct_start };
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
                    if (self.current().tag != .comma) break;
                    self.advance();
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

    fn parseFunctionLike(self: *Parser, tag: Token.Tag) !*ast.Expr {
        const start_token = self.current();
        self.advance(); // "proc" or "fn"
        try self.expect(.lparen);

        var params = self.list(ast.Param);
        while (self.current().tag != .rparen and self.current().tag != .eof) {
            const param_start = self.currentLoc();
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

            try params.append(.{ .pat = pat, .ty = ty, .value = value, .loc = param_start });
            if (self.current().tag != .comma) break;
            self.advance();
        }
        try self.expect(.rparen);

        const return_type: ?*ast.Expr = try self.parseOptionalReturnType();

        var body: ?ast.Block = null;
        if (self.current().tag == .lcurly) {
            body = try self.parseBlock();
        }

        const func = ast.Function{
            .is_proc = (tag == .keyword_proc),
            .params = params,
            .result_ty = return_type,
            .body = body,
            .loc = start_token.loc,
            .is_variadic = false, // TODO
        };
        return try self.alloc(ast.Expr, .{ .Function = func });
    }

    //=================================================================
    // Enums / Variants
    //=================================================================

    inline fn parseEnumType(self: *Parser) !*ast.Expr {
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
            const name = try self.expectIdent();
            const value = try self.parseOptionalInitializer(.expr);
            try fields.append(.{ .name = name.bytes, .value = value, .loc = field_start });
            if (self.current().tag != .comma) break;
            self.advance();
        }

        try self.expect(.rcurly);
        const enum_type = ast.EnumType{ .fields = fields, .discriminant = backing_type, .loc = enum_start };
        return self.alloc(ast.Expr, .{ .BuiltinType = .{ .Enum = enum_type } });
    }

    inline fn parseVariantType(self: *Parser) !*ast.Expr {
        // Rust-like enum with payloads
        const variant_start = self.currentLoc();
        self.advance(); // "variant"
        try self.expect(.lcurly);

        var fields = self.list(ast.VariantField);

        while (self.current().tag != .rcurly and self.current().tag != .eof) {
            const case_start = self.currentLoc();
            const case_name = try self.expectIdent();

            switch (self.current().tag) {
                .lparen => {
                    // Tuple-like payload
                    self.advance();
                    var types = self.list(*ast.Expr);
                    if (self.current().tag != .rparen) {
                        while (true) {
                            try types.append(try self.parseExpr(0, .type));
                            if (self.current().tag != .comma) break;
                            self.advance();
                        }
                    }
                    try self.expect(.rparen);
                    const value = try self.parseOptionalInitializer(.expr);
                    try fields.append(.{ .name = case_name.bytes, .ty = .{ .Tuple = types }, .value = value, .loc = case_start });
                    if (self.current().tag != .comma) break;
                    self.advance();
                },
                .lcurly => {
                    // Struct-like payload
                    self.advance();
                    const struct_fields = try self.parseStructFieldList(.rcurly);
                    const value = try self.parseOptionalInitializer(.expr);
                    try fields.append(.{ .name = case_name.bytes, .ty = .{ .Struct = struct_fields }, .value = value, .loc = case_start });
                    if (self.current().tag != .comma) break;
                    self.advance();
                },
                else => {
                    // No payload
                    const value = try self.parseOptionalInitializer(.expr);
                    try fields.append(.{ .name = case_name.bytes, .ty = null, .value = value, .loc = case_start });
                    if (self.current().tag != .comma) break;
                    self.advance();
                },
            }
        }

        try self.expect(.rcurly);
        const variant_type = ast.VariantLikeType{ .fields = fields, .loc = variant_start };
        return self.alloc(ast.Expr, .{ .BuiltinType = .{ .Variant = variant_type } });
    }
};

