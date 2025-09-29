const std = @import("std");
const cst = @import("cst.zig"); // Import cst to get FileId

pub const Token = struct {
    tag: Tag,
    loc: Loc,

    pub const Loc = struct {
        file_id: cst.FileId,
        start: usize,
        end: usize,

        pub fn init(file_id: cst.FileId, start: usize, end: usize) Loc {
            return .{ .file_id = file_id, .start = start, .end = end };
        }

        pub fn merge(self: Loc, other: Loc) Loc {
            std.debug.assert(self.file_id == other.file_id); // Spans must be from the same file to be merged.
            return .{
                .file_id = self.file_id,
                .start = @min(self.start, other.start),
                .end = @max(self.end, other.end),
            };
        }
    };

    pub const keywords = std.StaticStringMap(Tag).initComptime(.{
        .{ "align", .keyword_align },
        .{ "and", .keyword_and },
        .{ "any", .keyword_any },
        .{ "asm", .keyword_asm },
        .{ "async", .keyword_async },
        .{ "await", .keyword_await },
        .{ "break", .keyword_break },
        .{ "catch", .keyword_catch },
        .{ "comptime", .keyword_comptime },
        .{ "code", .keyword_code },
        .{ "complex", .keyword_complex },
        .{ "const", .keyword_const },
        .{ "continue", .keyword_continue },
        .{ "dyn", .keyword_dyn },
        .{ "defer", .keyword_defer },
        .{ "else", .keyword_else },
        .{ "enum", .keyword_enum },
        .{ "errdefer", .keyword_errdefer },
        .{ "error", .keyword_error },
        .{ "export", .keyword_export },
        .{ "extern", .keyword_extern },
        .{ "false", .keyword_false },
        .{ "fn", .keyword_fn },
        .{ "for", .keyword_for },
        .{ "if", .keyword_if },
        .{ "in", .keyword_in },
        .{ "is", .keyword_is },
        .{ "insert", .keyword_insert },
        .{ "import", .keyword_import },
        .{ "match", .keyword_match },
        .{ "mlir", .keyword_mlir },
        .{ "noreturn", .keyword_noreturn },
        .{ "null", .keyword_null },
        .{ "opaque", .keyword_opaque },
        .{ "or", .keyword_or },
        .{ "orelse", .keyword_orelse },
        .{ "package", .keyword_package },
        .{ "proc", .keyword_proc },
        .{ "pub", .keyword_pub },
        .{ "return", .keyword_return },
        .{ "linksection", .keyword_linksection },
        .{ "simd", .keyword_simd },
        .{ "struct", .keyword_struct },
        .{ "threadlocal", .keyword_threadlocal },
        .{ "tensor", .keyword_tensor },
        .{ "test", .keyword_test },
        .{ "true", .keyword_true },
        .{ "type", .keyword_type },
        .{ "typeof", .keyword_typeof },
        .{ "union", .keyword_union },
        .{ "undefined", .keyword_undefined },
        .{ "unreachable", .keyword_unreachable },
        .{ "variant", .keyword_variant },
        .{ "while", .keyword_while },
    });

    pub fn getKeyword(bytes: []const u8) ?Tag {
        return keywords.get(bytes);
    }

    pub const Tag = enum {
        // control
        invalid,
        eof,
        eos, // semicolon or inserted semicolon

        // identifiers
        identifier,
        raw_identifier,

        // literals
        char_literal,
        string_literal,
        raw_string_literal,
        raw_asm_block,
        mlir_content,
        integer_literal,
        float_literal,
        imaginary_literal,

        // operators & punctuation
        plus,
        minus,
        star,
        slash,
        percent,
        caret,
        bang,
        b_and,
        b_or,
        shl,
        shr,
        plus_equal,
        minus_equal,
        rarrow,
        star_equal,
        slash_equal,
        percent_equal,
        caret_equal,
        and_equal,
        or_equal,
        shl_equal,
        shr_equal,
        shl_pipe,
        shl_pipe_equal,
        plus_pipe,
        plus_pipe_equal,
        minus_pipe,
        minus_pipe_equal,
        star_pipe,
        star_pipe_equal,
        plus_percent,
        plus_percent_equal,
        minus_percent,
        minus_percent_equal,
        star_percent,
        star_percent_equal,
        eq,
        eqeq,
        ne,
        gt,
        lt,
        ge,
        le,
        at,
        dot,
        dotdot,
        dotstar,
        dotlparen,
        dotdotdot,
        dotdoteq,
        comma,
        colon,
        coloncolon,
        coloneq,
        fatarrow,
        question,
        lcurly,
        rcurly,
        lsquare,
        rsquare,
        lparen,
        rparen,

        container_doc_comment,
        doc_comment,

        // keywords
        keyword_align,
        keyword_and,
        keyword_any,
        keyword_asm,
        keyword_async,
        keyword_await,
        keyword_break,
        keyword_catch,
        keyword_comptime,
        keyword_code,
        keyword_complex,
        keyword_const,
        keyword_continue,
        keyword_dyn,
        keyword_defer,
        keyword_else,
        keyword_enum,
        keyword_errdefer,
        keyword_error,
        keyword_export,
        keyword_extern,
        keyword_false,
        keyword_fn,
        keyword_for,
        keyword_if,
        keyword_in,
        keyword_is,
        keyword_insert,
        keyword_import,
        keyword_match,
        keyword_mlir,
        keyword_noreturn,
        keyword_null,
        keyword_opaque,
        keyword_or,
        keyword_orelse,
        keyword_package,
        keyword_proc,
        keyword_pub,
        keyword_return,
        keyword_linksection,
        keyword_simd,
        keyword_struct,
        keyword_threadlocal,
        keyword_tensor,
        keyword_test,
        keyword_true,
        keyword_type,
        keyword_typeof,
        keyword_union,
        keyword_undefined,
        keyword_unreachable,
        keyword_variant,
        keyword_while,
        pub fn lexeme(tag: Tag) ?[]const u8 {
            return switch (tag) {
                .invalid,
                .identifier,
                .raw_identifier,
                .string_literal,
                .raw_string_literal,
                .char_literal,
                .eof,
                .eos,
                .integer_literal,
                .float_literal,
                .imaginary_literal,
                .doc_comment,
                .container_doc_comment,
                => null,

                .plus => "+",
                .minus => "-",
                .star => "*",
                .slash => "/",
                .percent => "%",
                .caret => "^",
                .bang => "!",
                .b_and => "&",
                .b_or => "|",
                .shl => "<<",
                .shr => ">>",
                .plus_equal => "+=",
                .minus_equal => "-=",
                .rarrow => "->",
                .star_equal => "*=",
                .slash_equal => "/=",
                .percent_equal => "%=",
                .caret_equal => "^=",
                .and_equal => "&=",
                .or_equal => "|=",
                .shl_equal => "<<=",
                .shr_equal => ">>=",
                .shl_pipe => "<<|",
                .shl_pipe_equal => "<<|=",
                .plus_pipe => "+|",
                .plus_pipe_equal => "+|=",
                .minus_pipe => "-|",
                .minus_pipe_equal => "-|=",
                .star_pipe => "*|",
                .star_pipe_equal => "*|=",
                .plus_percent => "+%",
                .plus_percent_equal => "+%=",
                .minus_percent => "-%",
                .minus_percent_equal => "-%=",
                .star_percent => "*%",
                .star_percent_equal => "*%=",
                .eq => "=",
                .eqeq => "==",
                .ne => "!=",
                .gt => ">",
                .lt => "<",
                .ge => ">=",
                .le => "<=",
                .at => "@",
                .dot => ".",
                .dotdot => "..",
                .dotstar => ".*",
                .dotlparen => ".(",
                .dotdotdot => "...",
                .dotdoteq => "..=",
                .comma => ",",
                .colon => ":",
                .coloncolon => "::",
                .coloneq => ":=",
                .fatarrow => "=>",
                .question => "?",
                .lcurly => "{",
                .rcurly => "}",
                .lsquare => "[",
                .rsquare => "]",
                .lparen => "(",
                .rparen => ")",
                .raw_asm_block => "asm { ... }",
                .mlir_content => "mlir { ... }",
                .keyword_align => "align",
                .keyword_and => "and",
                .keyword_any => "any",
                .keyword_asm => "asm",
                .keyword_async => "async",
                .keyword_await => "await",
                .keyword_break => "break",
                .keyword_catch => "catch",
                .keyword_comptime => "comptime",
                .keyword_code => "code",
                .keyword_complex => "complex",
                .keyword_const => "const",
                .keyword_continue => "continue",
                .keyword_dyn => "dyn",
                .keyword_defer => "defer",
                .keyword_else => "else",
                .keyword_enum => "enum",
                .keyword_errdefer => "errdefer",
                .keyword_error => "error",
                .keyword_export => "export",
                .keyword_extern => "extern",
                .keyword_false => "false",
                .keyword_fn => "fn",
                .keyword_for => "for",
                .keyword_if => "if",
                .keyword_in => "in",
                .keyword_is => "is",
                .keyword_insert => "insert",
                .keyword_import => "import",
                .keyword_match => "match",
                .keyword_mlir => "mlir",
                .keyword_noreturn => "noreturn",
                .keyword_null => "null",
                .keyword_opaque => "opaque",
                .keyword_or => "or",
                .keyword_orelse => "orelse",
                .keyword_package => "package",
                .keyword_proc => "proc",
                .keyword_pub => "pub",
                .keyword_return => "return",
                .keyword_linksection => "linksection",
                .keyword_simd => "simd",
                .keyword_struct => "struct",
                .keyword_threadlocal => "threadlocal",
                .keyword_tensor => "tensor",
                .keyword_test => "test",
                .keyword_true => "true",
                .keyword_type => "type",
                .keyword_typeof => "typeof",
                .keyword_union => "union",
                .keyword_undefined => "undefined",
                .keyword_unreachable => "unreachable",
                .keyword_variant => "variant",
                .keyword_while => "while",
            };
        }

        pub fn symbol(tag: Tag) []const u8 {
            return tag.lexeme() orelse switch (tag) {
                .invalid => "invalid token",
                .identifier => "an identifier",
                .string_literal => "a string literal",
                .char_literal => "a character literal",
                .eof => "EOF",
                .eos => "EOS",
                .integer_literal => "an integer literal",
                .float_literal => "a float literal",
                .imaginary_literal => "an imaginary literal",
                .doc_comment, .container_doc_comment => "a document comment",
                else => unreachable,
            };
        }
    };
};

pub const Tokenizer = struct {
    buffer: [:0]const u8,
    index: usize,
    mode: Mode = .normal,
    last_tag: Token.Tag = .invalid,
    mlir_pending: bool = false,
    asm_pending: bool = false,
    raw_string_hashes: usize = 0,
    file_id: u32 = 0,

    pub fn init(source: [:0]const u8, file_id: u32, mode: Mode) Tokenizer {
        return .{
            .buffer = source,
            .index = if (std.mem.startsWith(u8, source, "\xEF\xBB\xBF")) 3 else 0,
            .mode = mode,
            .file_id = file_id,
        };
    }

    const Mode = enum {
        normal,
        semi,
    };

    const State = enum {
        start,
        plus,
        minus,
        star,
        slash,
        caret,
        percent,
        bang,
        ampersand,
        pipe,
        langle,
        rangle,
        equal,
        dot,
        colon,

        plus_pipe,
        plus_percent,
        minus_pipe,
        minus_percent,
        star_pipe,
        star_percent,
        langle_langle,
        rangle_rangle,
        langle_langle_pipe,
        dot_dot,

        line_comment_start,
        line_comment,
        doc_comment_start,
        doc_comment,
        expect_newline,
        block_comment_start,
        block_comment,

        identifier,
        raw_identifier,
        char_literal,
        string_literal,
        string_literal_slash,
        raw_string_literal,
        char_literal_slash,

        int,
        int_exponent,
        int_period,
        float,
        float_exponent,

        mlir_block,
        asm_block,

        invalid,
    };

    inline fn curr(self: *Tokenizer) u8 {
        return self.buffer[self.index];
    }

    inline fn advance(self: *Tokenizer) void {
        self.index += 1;
    }

    inline fn shouldInsertSemi(self: *Tokenizer) bool {
        return asiEnd(self.last_tag);
    }

    inline fn asiEnd(tag: Token.Tag) bool {
        return switch (tag) {
            // identifiers
            .identifier,
            .raw_identifier,

            // literals
            .char_literal,
            .string_literal,
            .raw_string_literal,
            .integer_literal,
            .float_literal,
            .imaginary_literal,

            // closing delimiters
            .rparen,
            .rsquare,
            .rcurly,

            .dotstar,
            .question,
            .bang,

            // keywords that end statements
            .keyword_true,
            .keyword_false,
            .keyword_null,
            .keyword_undefined,
            .keyword_return,
            .keyword_noreturn,
            .keyword_break,
            .keyword_continue,
            .keyword_unreachable,
            .keyword_await,
            .keyword_type,
            .keyword_any,

            .raw_asm_block,
            .mlir_content,
            => true,

            else => false,
        };
    }

    pub fn next(self: *Tokenizer) Token {
        var result = Token{
            .tag = .invalid,
            .loc = .{ .file_id = self.file_id, .start = self.index, .end = self.index },
        };

        var block_depth: usize = 0;
        var in_string: bool = false;
        var quote: u8 = 0;

        state: switch (State.start) {
            .start => {
                switch (self.curr()) {
                    0 => {
                        if (self.index == self.buffer.len) {
                            if (self.mode == .semi and self.shouldInsertSemi()) {
                                // Emit a final inserted semicolon before EOF.
                                // Do NOT advance index; next call will see EOF and emit .eof.
                                result.tag = .eos;
                            } else {
                                return .{
                                    .tag = .eof,
                                    .loc = .{ .file_id = self.file_id, .start = self.index, .end = self.index },
                                };
                            }
                        } else continue :state .invalid;
                    },
                    '+' => continue :state .plus,
                    '-' => continue :state .minus,
                    '*' => continue :state .star,
                    '/' => continue :state .slash,
                    '^' => continue :state .caret,
                    '%' => continue :state .percent,
                    '!' => continue :state .bang,
                    '&' => continue :state .ampersand,
                    '|' => continue :state .pipe,
                    '<' => continue :state .langle,
                    '>' => continue :state .rangle,
                    '=' => continue :state .equal,
                    '.' => continue :state .dot,
                    ':' => continue :state .colon,

                    '@' => {
                        result.tag = .at;
                        self.advance();
                    },
                    ',' => {
                        result.tag = .comma;
                        self.advance();
                    },
                    ';' => {
                        result.tag = .eos;
                        self.advance();
                    },
                    '?' => {
                        result.tag = .question;
                        self.advance();
                    },
                    '{' => {
                        result.tag = .lcurly;
                        self.advance();

                        if (self.mlir_pending or self.last_tag == .keyword_mlir) {
                            self.mlir_pending = false;
                            block_depth = 1;
                            in_string = false;
                            quote = 0;
                            continue :state .mlir_block;
                        } else if (self.asm_pending or self.last_tag == .keyword_asm) {
                            self.asm_pending = false;
                            block_depth = 1;
                            in_string = false;
                            quote = 0;
                            continue :state .asm_block;
                        }
                    },
                    '}' => {
                        result.tag = .rcurly;
                        self.advance();
                    },
                    '[' => {
                        result.tag = .lsquare;
                        self.advance();
                    },
                    ']' => {
                        result.tag = .rsquare;
                        self.advance();
                    },
                    '(' => {
                        result.tag = .lparen;
                        self.advance();
                    },
                    ')' => {
                        result.tag = .rparen;
                        self.advance();
                    },

                    ' ', '\t' => {
                        self.advance();
                        result.loc.start = self.index;
                        continue :state .start;
                    },
                    '\n' => {
                        self.advance();
                        if (self.mode == .semi and self.shouldInsertSemi()) {
                            result.tag = .eos;
                        } else {
                            result.loc.start = self.index;
                            continue :state .start;
                        }
                    },
                    '\r' => {
                        self.advance();
                        if (self.curr() == '\n') {
                            self.advance();
                            if (self.mode == .semi and self.shouldInsertSemi()) {
                                result.tag = .eos;
                            } else {
                                result.loc.start = self.index;
                                continue :state .start;
                            }
                        } else if (self.index == self.buffer.len) {
                            result.tag = .invalid;
                        } else {
                            continue :state .invalid;
                        }
                    },
                    'a'...'q', 's'...'z', 'A'...'Z', '_' => continue :state .identifier,
                    '0'...'9' => {
                        result.tag = .integer_literal;
                        self.advance();
                        continue :state .int;
                    },
                    'r' => {
                        const next_char = if (self.index + 1 < self.buffer.len) self.buffer[self.index + 1] else 0;
                        if (next_char == '"') {
                            result.tag = .raw_string_literal;
                            self.advance(); // 'r'
                            self.advance(); // '"'
                            self.raw_string_hashes = 0;
                            continue :state .raw_string_literal;
                        } else if (next_char == '#') {
                            var idx = self.index + 1;
                            while (idx < self.buffer.len and self.buffer[idx] == '#') idx += 1;
                            const hash_count = idx - (self.index + 1);
                            if (hash_count > 0 and idx < self.buffer.len and self.buffer[idx] == '"') {
                                result.tag = .raw_string_literal;
                                self.advance(); // 'r'
                                var consumed: usize = 0;
                                while (consumed < hash_count) : (consumed += 1) {
                                    self.advance();
                                }
                                self.advance(); // '"'
                                self.raw_string_hashes = hash_count;
                                continue :state .raw_string_literal;
                            } else {
                                self.advance(); // 'r'
                                self.advance(); // '#'
                                continue :state .raw_identifier;
                            }
                        } else continue :state .identifier;
                    },
                    '\'' => {
                        result.tag = .char_literal;
                        continue :state .char_literal;
                    },
                    '"' => {
                        result.tag = .string_literal;
                        continue :state .string_literal;
                    },
                    else => continue :state .invalid,
                }
            },
            .plus => {
                self.advance();
                switch (self.curr()) {
                    '%' => continue :state .plus_percent,
                    '|' => continue :state .plus_pipe,
                    '=' => {
                        result.tag = .plus_equal;
                        self.advance();
                    },
                    else => result.tag = .plus,
                }
            },
            .minus => {
                self.advance();
                switch (self.curr()) {
                    '>' => {
                        result.tag = .rarrow;
                        self.advance();
                    },
                    '%' => continue :state .minus_percent,
                    '|' => continue :state .minus_pipe,
                    '=' => {
                        result.tag = .minus_equal;
                        self.advance();
                    },
                    else => result.tag = .minus,
                }
            },
            .star => {
                self.advance();
                switch (self.curr()) {
                    '%' => continue :state .star_percent,
                    '|' => continue :state .star_pipe,
                    '=' => {
                        result.tag = .star_equal;
                        self.advance();
                    },
                    else => result.tag = .star,
                }
            },
            .slash => {
                self.advance();
                switch (self.curr()) {
                    '=' => {
                        result.tag = .slash_equal;
                        self.advance();
                    },
                    '/' => continue :state .line_comment_start,
                    '*' => continue :state .block_comment_start,
                    else => result.tag = .slash,
                }
            },
            .caret => {
                self.advance();
                if (self.curr() == '=') {
                    result.tag = .caret_equal;
                    self.advance();
                } else {
                    result.tag = .caret;
                }
            },
            .percent => {
                self.advance();
                if (self.curr() == '=') {
                    result.tag = .percent_equal;
                    self.advance();
                } else {
                    result.tag = .percent;
                }
            },
            .bang => {
                self.advance();
                if (self.curr() == '=') {
                    result.tag = .ne;
                    self.advance();
                } else {
                    result.tag = .bang;
                }
            },
            .ampersand => {
                self.advance();
                if (self.curr() == '=') {
                    result.tag = .and_equal;
                    self.advance();
                } else {
                    result.tag = .b_and;
                }
            },
            .pipe => {
                self.advance();
                if (self.curr() == '=') {
                    result.tag = .or_equal;
                    self.advance();
                } else {
                    result.tag = .b_or;
                }
            },
            .langle => {
                self.advance();
                switch (self.curr()) {
                    '<' => continue :state .langle_langle,
                    '=' => {
                        result.tag = .le;
                        self.advance();
                    },
                    else => result.tag = .lt,
                }
            },
            .rangle => {
                self.advance();
                switch (self.curr()) {
                    '>' => continue :state .rangle_rangle,
                    '=' => {
                        result.tag = .ge;
                        self.advance();
                    },
                    else => result.tag = .gt,
                }
            },
            .equal => {
                self.advance();
                switch (self.curr()) {
                    '=' => {
                        result.tag = .eqeq;
                        self.advance();
                    },
                    '>' => {
                        result.tag = .fatarrow;
                        self.advance();
                    },
                    else => result.tag = .eq,
                }
            },
            .dot => {
                self.advance();
                switch (self.curr()) {
                    '.' => continue :state .dot_dot,
                    '*' => {
                        result.tag = .dotstar;
                        self.advance();
                    },
                    '(' => {
                        result.tag = .dotlparen;
                        self.advance();
                    },
                    '=' => {
                        result.tag = .dotdoteq;
                        self.advance();
                    },
                    else => result.tag = .dot,
                }
            },
            .colon => {
                self.advance();
                switch (self.curr()) {
                    ':' => {
                        result.tag = .coloncolon;
                        self.advance();
                    },
                    '=' => {
                        result.tag = .coloneq;
                        self.advance();
                    },
                    else => result.tag = .colon,
                }
            },

            .plus_pipe => {
                self.advance();
                if (self.curr() == '=') {
                    result.tag = .plus_pipe_equal;
                    self.advance();
                } else {
                    result.tag = .plus_pipe;
                }
            },
            .plus_percent => {
                self.advance();
                if (self.curr() == '=') {
                    result.tag = .plus_percent_equal;
                    self.advance();
                } else {
                    result.tag = .plus_percent;
                }
            },
            .minus_pipe => {
                self.advance();
                if (self.curr() == '=') {
                    result.tag = .minus_pipe_equal;
                    self.advance();
                } else {
                    result.tag = .minus_pipe;
                }
            },
            .minus_percent => {
                self.advance();
                if (self.curr() == '=') {
                    result.tag = .minus_percent_equal;
                    self.advance();
                } else {
                    result.tag = .minus_percent;
                }
            },
            .star_pipe => {
                self.advance();
                if (self.curr() == '=') {
                    result.tag = .star_pipe_equal;
                    self.advance();
                } else {
                    result.tag = .star_pipe;
                }
            },
            .star_percent => {
                self.advance();
                if (self.curr() == '=') {
                    result.tag = .star_percent_equal;
                    self.advance();
                } else {
                    result.tag = .star_percent;
                }
            },
            .langle_langle => {
                self.advance();
                if (self.curr() == '=') {
                    result.tag = .shl_equal;
                    self.advance();
                } else if (self.curr() == '|') {
                    continue :state .langle_langle_pipe;
                } else {
                    result.tag = .shl;
                }
            },
            .rangle_rangle => {
                self.advance();
                if (self.curr() == '=') {
                    result.tag = .shr_equal;
                    self.advance();
                } else {
                    result.tag = .shr;
                }
            },
            .langle_langle_pipe => {
                self.advance();
                if (self.curr() == '=') {
                    result.tag = .shl_pipe_equal;
                    self.advance();
                } else {
                    result.tag = .shl_pipe;
                }
            },
            .dot_dot => {
                self.advance();
                switch (self.curr()) {
                    '.' => {
                        result.tag = .dotdotdot;
                        self.advance();
                    },
                    '=' => {
                        result.tag = .dotdoteq;
                        self.advance();
                    },
                    else => result.tag = .dotdot,
                }
            },

            .line_comment_start => {
                self.advance();
                switch (self.curr()) {
                    0 => {
                        if (self.index != self.buffer.len) {
                            continue :state .invalid;
                        } else {
                            if (self.mode == .semi and self.shouldInsertSemi()) {
                                result.tag = .eos; // inserted semicolon at EOF after comment
                            } else {
                                return .{ .tag = .eof, .loc = .{ .file_id = self.file_id, .start = self.index, .end = self.index } };
                            }
                        }
                    },
                    '!' => {
                        result.tag = .container_doc_comment;
                        continue :state .doc_comment;
                    },
                    '\n' => {
                        self.advance();
                        result.loc.start = self.index;
                        continue :state .start;
                    },
                    '/' => continue :state .doc_comment_start,
                    '\r' => continue :state .expect_newline,
                    0x01...0x09, 0x0b...0x0c, 0x0e...0x1f, 0x7f => {
                        continue :state .invalid;
                    },
                    else => continue :state .line_comment,
                }
            },
            .doc_comment_start => {
                self.advance();
                switch (self.curr()) {
                    0, '\n' => result.tag = .doc_comment,
                    '\r' => {
                        if (self.buffer[self.index + 1] == '\n') {
                            result.tag = .doc_comment;
                        } else continue :state .invalid;
                    },
                    '/' => continue :state .line_comment,
                    0x01...0x09, 0x0b...0x0c, 0x0e...0x1f, 0x7f => continue :state .invalid,
                    else => {
                        result.tag = .doc_comment;
                        continue :state .doc_comment;
                    },
                }
            },
            .line_comment => {
                self.advance();
                switch (self.curr()) {
                    0 => {
                        if (self.index != self.buffer.len) {
                            continue :state .invalid;
                        } else {
                            if (self.mode == .semi and self.shouldInsertSemi()) {
                                result.tag = .eos; // inserted semicolon at EOF after comment
                            } else {
                                return .{ .tag = .eof, .loc = .{ .file_id = self.file_id, .start = self.index, .end = self.index } };
                            }
                        }
                    },
                    '\n' => {
                        self.advance();
                        if (self.mode == .semi and self.shouldInsertSemi()) {
                            result.tag = .eos;
                        } else {
                            result.loc.start = self.index;
                            continue :state .start;
                        }
                    },
                    '\r' => continue :state .expect_newline,
                    0x01...0x09, 0x0b...0x0c, 0x0e...0x1f, 0x7f => continue :state .invalid,
                    else => continue :state .line_comment,
                }
            },
            .doc_comment => {
                self.advance();
                switch (self.curr()) {
                    0, '\n' => {},
                    '\r' => if (self.buffer[self.index + 1] != '\n') {
                        continue :state .invalid;
                    },
                    0x01...0x09, 0x0b...0x0c, 0x0e...0x1f, 0x7f => continue :state .invalid,
                    else => continue :state .doc_comment,
                }
            },

            .block_comment_start => {
                self.advance(); // consume the '*'
                continue :state .block_comment;
            },
            .block_comment => {
                const c = self.curr();
                switch (c) {
                    0 => {
                        if (self.index == self.buffer.len) {
                            result.tag = .invalid;
                        } else continue :state .invalid;
                    },
                    '*' => {
                        self.advance();
                        if (self.curr() == '/') {
                            self.advance();
                            result.loc.start = self.index;
                            continue :state .start;
                        }
                        continue :state .block_comment;
                    },
                    0x01...0x09, 0x0b...0x0c, 0x0e...0x1f, 0x7f => {
                        continue :state .invalid;
                    },
                    else => {
                        self.advance();
                        continue :state .block_comment;
                    },
                }
            },
            .expect_newline => {
                self.advance();
                switch (self.curr()) {
                    0 => {
                        if (self.index == self.buffer.len) {
                            result.tag = .invalid;
                        } else continue :state .invalid;
                    },
                    '\n' => {
                        self.advance();
                        if (self.mode == .semi and self.shouldInsertSemi()) {
                            result.tag = .eos;
                        } else {
                            result.loc.start = self.index;
                            continue :state .start;
                        }
                    },

                    else => continue :state .invalid,
                }
            },

            .identifier => {
                self.advance();
                switch (self.curr()) {
                    'a'...'z', 'A'...'Z', '0'...'9', '_' => continue :state .identifier,
                    else => {
                        const ident = self.buffer[result.loc.start..self.index];
                        if (Token.getKeyword(ident)) |kw| {
                            if (kw == .keyword_mlir) self.mlir_pending = true;
                            if (kw == .keyword_asm) self.asm_pending = true;
                            result.tag = kw;
                        } else {
                            result.tag = .identifier;
                        }
                    },
                }
            },
            .raw_identifier => {
                // Token starts at 'r' and is followed by one or more '#'.
                // The identifier body begins after the last '#'.
                var body_start = result.loc.start + 1; // start after 'r'
                var hashes: usize = 0;
                while (body_start + hashes < self.buffer.len and self.buffer[body_start + hashes] == '#') : (hashes += 1) {}
                body_start += hashes;
                const body_len = if (self.index > body_start) self.index - body_start else 0;
                if (self.index == self.buffer.len) {
                    if (hashes > 0 and body_len > 0) {
                        // Accept any non-empty body after at least one '#'
                        result.tag = .raw_identifier;
                    } else {
                        result.tag = .invalid;
                    }
                } else switch (self.curr()) {
                    'a'...'z', 'A'...'Z', '0'...'9', '_', '#' => {
                        self.advance();
                        continue :state .raw_identifier;
                    },
                    else => {
                        if (hashes > 0 and body_len > 0) {
                            // Accept any non-empty body after at least one '#'
                            result.tag = .raw_identifier;
                        } else {
                            continue :state .invalid;
                        }
                    },
                }
            },
            .raw_string_literal => {
                const c = self.curr();
                switch (c) {
                    0 => {
                        if (self.index == self.buffer.len) {
                            result.tag = .invalid;
                        } else continue :state .invalid;
                    },
                    '"' => {
                        var idx = self.index + 1;
                        var remaining = self.raw_string_hashes;
                        while (remaining > 0 and idx < self.buffer.len and self.buffer[idx] == '#') : (remaining -= 1) idx += 1;
                        if (remaining == 0) {
                            self.advance();
                            var consumed: usize = 0;
                            while (consumed < self.raw_string_hashes) : (consumed += 1) {
                                if (self.curr() != '#') break;
                                self.advance();
                            }
                            self.raw_string_hashes = 0;
                            result.tag = .raw_string_literal;
                        } else {
                            self.advance();
                            continue :state .raw_string_literal;
                        }
                    },
                    else => {
                        self.advance();
                        continue :state .raw_string_literal;
                    },
                }
            },
            .string_literal => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    0 => {
                        if (self.index != self.buffer.len) {
                            continue :state .invalid;
                        } else {
                            result.tag = .invalid;
                        }
                    },
                    '\n' => result.tag = .invalid,
                    '\\' => continue :state .string_literal_slash,
                    '"' => self.index += 1,
                    0x01...0x09, 0x0b...0x1f, 0x7f => {
                        continue :state .invalid;
                    },
                    else => continue :state .string_literal,
                }
            },

            .string_literal_slash => {
                self.advance();
                switch (self.curr()) {
                    0, '\n' => result.tag = .invalid,
                    else => continue :state .string_literal,
                }
            },

            .char_literal => {
                self.advance();
                switch (self.curr()) {
                    0 => {
                        if (self.index != self.buffer.len) {
                            continue :state .invalid;
                        } else result.tag = .invalid;
                    },
                    '\n' => result.tag = .invalid,
                    '\\' => continue :state .char_literal_slash,
                    '\'' => self.advance(),
                    0x01...0x09, 0x0b...0x1f, 0x7f => continue :state .invalid,
                    else => continue :state .char_literal,
                }
            },

            .char_literal_slash => {
                self.advance();
                switch (self.curr()) {
                    0 => {
                        if (self.index != self.buffer.len) {
                            continue :state .invalid;
                        } else result.tag = .invalid;
                    },
                    '\n' => result.tag = .invalid,
                    0x01...0x09, 0x0b...0x1f, 0x7f => continue :state .invalid,
                    else => continue :state .char_literal,
                }
            },

            .int => switch (self.buffer[self.index]) {
                '.' => continue :state .int_period,
                '_', 'a'...'d', 'f'...'o', 'q'...'z', 'A'...'D', 'F'...'O', 'Q'...'Z', '0'...'9' => {
                    self.advance();
                    continue :state .int;
                },
                'e', 'E', 'p', 'P' => {
                    continue :state .int_exponent;
                },
                else => if (self.index > result.loc.start and self.buffer[self.index - 1] == 'i') {
                    result.tag = .imaginary_literal;
                },
            },
            .int_exponent => {
                self.advance();
                switch (self.curr()) {
                    '-', '+' => {
                        self.advance();
                        continue :state .float;
                    },
                    else => continue :state .int,
                }
            },
            .int_period => {
                self.advance();
                const c = self.curr();
                // If the previous token was a standalone '.', we're in a field access like '.1.0'.
                // Do not merge the following '.' into a float; keep this token as an integer literal.
                if (self.last_tag == .dot) {
                    self.index -= 1;
                } else if (c == 'i') {
                    self.index -= 1;
                } else switch (c) {
                    '_', 'a'...'d', 'f'...'o', 'q'...'z', 'A'...'D', 'F'...'O', 'Q'...'Z', '0'...'9' => {
                        self.advance();
                        result.tag = .float_literal;
                        continue :state .float;
                    },
                    'e', 'E', 'p', 'P' => {
                        result.tag = .float_literal;
                        continue :state .float_exponent;
                    },
                    else => self.index -= 1,
                }
            },
            .float => switch (self.curr()) {
                '_', 'a'...'d', 'f'...'o', 'q'...'z', 'A'...'D', 'F'...'O', 'Q'...'Z', '0'...'9' => {
                    self.advance();
                    continue :state .float;
                },
                'e', 'E', 'p', 'P' => {
                    continue :state .float_exponent;
                },
                else => if (self.index > result.loc.start and self.buffer[self.index - 1] == 'i') {
                    result.tag = .imaginary_literal;
                },
            },
            .float_exponent => {
                self.advance();
                switch (self.curr()) {
                    '-', '+' => {
                        self.advance();
                        continue :state .float;
                    },
                    else => continue :state .float,
                }
            },

            .mlir_block => {
                switch (self.curr()) {
                    0 => {
                        if (self.index == self.buffer.len) {
                            // unterminated block
                            result.tag = .invalid;
                        } else continue :state .invalid;
                    },
                    '\\' => {
                        // Inside a string, skip escaped char
                        if (in_string) {
                            self.advance();
                            if (self.curr() != 0) self.advance();
                        } else {
                            self.advance();
                        }
                        continue :state .mlir_block;
                    },
                    '"', '\'' => {
                        const c = self.curr();
                        if (!in_string) {
                            in_string = true;
                            quote = c;
                        } else if (quote == c) {
                            in_string = false;
                        }
                        self.advance();
                        continue :state .mlir_block;
                    },
                    '{' => {
                        if (!in_string) block_depth += 1;
                        self.advance();
                        continue :state .mlir_block;
                    },
                    '}' => {
                        if (!in_string) {
                            if (block_depth == 0) {
                                // should not happen, but guard anyway
                                result.tag = .invalid;
                            } else {
                                block_depth -= 1;
                                self.advance(); // consume the closing '}'
                                if (block_depth == 0) {
                                    result.tag = .mlir_content;
                                } else {
                                    continue :state .mlir_block;
                                }
                            }
                        } else {
                            self.advance();
                            continue :state .mlir_block;
                        }
                    },
                    else => {
                        self.advance();
                        continue :state .mlir_block;
                    },
                }
            },

            .asm_block => {
                // Same logic as mlir_block but yields raw_asm_block
                switch (self.curr()) {
                    0 => {
                        if (self.index == self.buffer.len) {
                            result.tag = .invalid;
                        } else continue :state .invalid;
                    },
                    '\\' => {
                        if (in_string) {
                            self.advance();
                            if (self.curr() != 0) self.advance();
                        } else {
                            self.advance();
                        }
                        continue :state .asm_block;
                    },
                    '"', '\'' => {
                        const c = self.curr();
                        if (!in_string) {
                            in_string = true;
                            quote = c;
                        } else if (quote == c) {
                            in_string = false;
                        }
                        self.advance();
                        continue :state .asm_block;
                    },
                    '{' => {
                        if (!in_string) block_depth += 1;
                        self.advance();
                        continue :state .asm_block;
                    },
                    '}' => {
                        if (!in_string) {
                            if (block_depth == 0) {
                                result.tag = .invalid;
                            } else {
                                block_depth -= 1;
                                self.advance();
                                if (block_depth == 0) {
                                    result.tag = .raw_asm_block;
                                } else {
                                    continue :state .asm_block;
                                }
                            }
                        } else {
                            self.advance();
                            continue :state .asm_block;
                        }
                    },
                    else => {
                        self.advance();
                        continue :state .asm_block;
                    },
                }
            },

            .invalid => {
                self.advance();
                switch (self.curr()) {
                    0 => if (self.index == self.buffer.len) {
                        result.tag = .invalid;
                    } else continue :state .invalid,
                    '\n' => result.tag = .invalid,
                    else => continue :state .invalid,
                }
            },
        }
        result.loc.end = self.index;
        self.last_tag = result.tag;
        return result;
    }
};
