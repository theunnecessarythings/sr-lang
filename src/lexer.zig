const std = @import("std");

pub const Token = struct {
    tag: Tag,
    loc: Loc,

    pub const Loc = struct {
        start: usize,
        end: usize,
    };

    pub const keywords = std.StaticStringMap(Tag).initComptime(.{
        .{ "align", .keyword_align },
        .{ "and", .keyword_and },
        .{ "any", .keyword_any },
        .{ "as", .keyword_as },
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
        eos, // emitted only by NLSEMI

        // identifiers
        identifier,
        raw_identifier,

        // literals
        char_literal,
        string_literal,
        raw_string_literal,
        byte_literal,
        byte_char_literal,
        byte_string_literal,
        raw_byte_string_literal,
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
        pipe_pipe,
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
        dotdotdot,
        dotdoteq,
        dot_lparen,
        dot_lsquare,
        dot_lcurly,
        comma,
        semi,
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
        pound,

        // keywords
        keyword_align,
        keyword_and,
        keyword_any,
        keyword_as,
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
                .invalid, .eof, .eos, .identifier, .raw_identifier, .char_literal, .string_literal, .raw_string_literal, .byte_literal, .byte_string_literal, .raw_byte_string_literal, .raw_asm_block, .integer_literal, .float_literal, .imaginary_literal => null,

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
                .pipe_pipe => "||",
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
                .dotdotdot => "...",
                .dotdoteq => "..=",
                .dot_lparen => ".(",
                .dot_lsquare => ".[",
                .dot_lcurly => ".{",
                .comma => ",",
                .semi => ";",
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
                .pound => "#",

                .keyword_align => "align",
                .keyword_and => "and",
                .keyword_any => "any",
                .keyword_as => "as",
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
                .eof => "EOF",
                .eos => "; (inserted)",
                .identifier, .raw_identifier => "an identifier",
                .char_literal => "a character literal",
                .string_literal, .raw_string_literal, .byte_string_literal, .raw_byte_string_literal => "a string literal",
                .byte_literal => "a byte literal",
                .raw_asm_block => "an asm block",
                .mlir_content => "an mlir block",
                .integer_literal => "an integer literal",
                .float_literal => "a floating-point literal",
                .imaginary_literal => "an imaginary literal",
                else => unreachable,
            };
        }
    };
};

pub const Tokenizer = struct {
    buffer: [:0]const u8,
    index: usize,
    nlsemi: bool, // NLSEMI mode flag (needed for EOS insertion)

    // aux for raw strings
    raw_hashes: usize = 0,

    // aux for block comment nesting
    block_depth: usize = 0,

    // aux for raw-asm lookahead
    asm_maybe: bool = false,
    // aux for mlir block capture after seeing 'mlir'
    mlir_maybe: bool = false,

    // NEW: last two emitted token kinds (to implement floatLiteralPossible)
    lt1: Token.Tag = .invalid,
    lt2: Token.Tag = .invalid,

    // NEW: latched at the start of a numeric token (matches your LexerBase guard)
    allow_float: bool = true,

    /// For debugging purposes.
    pub fn dump(self: *Tokenizer, token: *const Token) void {
        std.debug.print("{s} \"{s}\"\n", .{ @tagName(token.tag), self.buffer[token.loc.start..token.loc.end] });
    }

    pub fn init(buffer: [:0]const u8) Tokenizer {
        var idx: usize = 0;
        // Skip BOM if present.
        if (std.mem.startsWith(u8, buffer, "\xEF\xBB\xBF")) idx = 3;
        // Shebang at SOF: '#!' ... EOL
        if (idx + 1 < buffer.len and buffer[idx] == '#' and buffer[idx + 1] == '!') {
            while (idx < buffer.len and
                buffer[idx] != '\n' and buffer[idx] != '\r') idx += 1;
        }
        return .{ .buffer = buffer, .index = idx, .nlsemi = false };
    }

    const State = enum {
        start,

        // NLSEMI handling
        nlsemi,

        // identifiers
        identifier,
        raw_ident_after_rhash,

        // strings
        string_literal,
        string_escape,
        char_literal,
        char_escape,
        byte_string_literal,
        byte_char_literal,
        raw_string_prefix, // r, r#, r##..., br, br#, ...
        raw_string_body, // reading until closing "###...
        raw_string_maybe_close,
        byte_string_body,

        // asm
        maybe_raw_asm_ws,
        raw_asm_body,

        // numbers
        int,
        int_exponent,
        float_exponent,
        suffix_check,

        // operators / punctuation
        plus,
        plus_percent,
        plus_pipe,
        minus,
        minus_percent,
        minus_pipe,
        asterisk,
        asterisk_percent,
        asterisk_pipe,
        slash,
        line_comment,
        block_comment, // nested
        angle_bracket_left,
        angle_bracket_angle_bracket_left,
        angle_bracket_angle_bracket_left_pipe,
        angle_bracket_right,
        angle_bracket_angle_bracket_right,
        caret,
        percent,
        ampersand,
        pipe,
        equal,
        bang,
        period,
        period_2,

        // bracket/paren to NLSEMI
        rparen_emit,
        rsquare_emit,
        rcurly_emit,

        invalid,
    };
    /// Returns next token.
    pub fn next(self: *Tokenizer) Token {
        var result: Token = .{
            .tag = undefined,
            .loc = .{ .start = self.index, .end = undefined },
        };

        state: switch (State.start) {
            .start => {
                if (self.nlsemi) {
                    result.loc.start = self.index;
                    continue :state .nlsemi;
                }
                switch (self.buffer[self.index]) {
                    0 => {
                        if (self.index == self.buffer.len) {
                            return .{
                                .tag = .eof,
                                .loc = .{ .start = self.index, .end = self.index },
                            };
                        } else continue :state .invalid;
                    },
                    ' ', '\t', '\r', '\n', 0x0c => {
                        self.index += 1;
                        result.loc.start = self.index;
                        continue :state .start;
                    },
                    // comments & shebang mid-file are just line comments
                    '/' => continue :state .slash,

                    // literals
                    '"' => {
                        result.tag = .string_literal;
                        continue :state .string_literal;
                    },
                    '\'' => {
                        result.tag = .char_literal;
                        continue :state .char_literal;
                    },

                    // identifiers / keywords / raw-id / raw-strings / byte strings
                    'a'...'z', 'A'...'Z', '_' => {
                        // ----- RAW BYTE STRING: br"..." / br#"..."
                        if (self.buffer[self.index] == 'b' and self.buffer[self.index + 1] == 'r') {
                            var j: usize = self.index + 2; // after "br"
                            var h: usize = 0;
                            while (self.buffer[j] == '#') : (j += 1) h += 1;
                            if (self.buffer[j] == '"') {
                                result.tag = .raw_byte_string_literal;
                                self.raw_hashes = 0;
                                continue :state .raw_string_prefix;
                            }
                            // else fall through to normal identifier "br..."
                        }

                        // ----- PLAIN BYTE LITERALS: b'..' and b".."
                        if (self.buffer[self.index] == 'b') {
                            const nxt = self.buffer[self.index + 1];
                            if (nxt == '\'') {
                                result.tag = .byte_char_literal;
                                continue :state .byte_char_literal; // this one is fine as-is
                            } else if (nxt == '"') {
                                result.tag = .byte_string_literal;
                                continue :state .byte_string_literal; // we'll redirect this immediately
                            }
                        }
                        // ----- RAW STRING vs RAW IDENTIFIER: r".." / r#".."# vs r#ident
                        if (self.buffer[self.index] == 'r') {
                            const j: usize = self.index + 1; // after 'r'
                            if (self.buffer[j] == '"') {
                                result.tag = .raw_string_literal;
                                self.raw_hashes = 0;
                                continue :state .raw_string_prefix;
                            }
                            if (self.buffer[j] == '#') {
                                var k = j;
                                var h: usize = 0;
                                while (self.buffer[k] == '#') : (k += 1) h += 1;
                                if (self.buffer[k] == '"') {
                                    result.tag = .raw_string_literal;
                                    self.raw_hashes = 0;
                                    continue :state .raw_string_prefix;
                                } else {
                                    // r#ident
                                    result.tag = .raw_identifier;
                                    self.index = j + 1; // after the first '#'
                                    if (!isXIDStart(self.peek())) continue :state .invalid;
                                    self.scanIdent();
                                    // fall through to keyword/ident finalization below
                                }
                            }
                        }

                        // maybe raw asm block: 'asm' WS* '{' ...
                        if (startsWith(self.buffer, self.index, "asm") and !isXIDContinue(self.buffer[self.index + 3]))
                            self.asm_maybe = true
                        else
                            self.asm_maybe = false;

                        result.tag = .identifier;
                        continue :state .identifier;
                    },

                    // numbers
                    '0'...'9' => {
                        result.tag = .integer_literal;
                        self.allow_float = self.floatLiteralPossible();
                        self.index += 1;
                        continue :state .int;
                    },

                    // punctuation / operators
                    '+' => continue :state .plus,
                    '-' => continue :state .minus,
                    '*' => continue :state .asterisk,
                    '%' => continue :state .percent,
                    '^' => continue :state .caret,
                    '&' => continue :state .ampersand,
                    '|' => continue :state .pipe,
                    '=' => continue :state .equal,
                    '!' => continue :state .bang,
                    '<' => continue :state .angle_bracket_left,
                    '>' => continue :state .angle_bracket_right,
                    '.' => continue :state .period,
                    '@' => {
                        result.tag = .at;
                        self.index += 1;
                    },
                    ',' => {
                        result.tag = .comma;
                        self.index += 1;
                    },
                    ';' => {
                        result.tag = .semi;
                        self.index += 1;
                    },
                    ':' => {
                        self.index += 1;
                        if (self.buffer[self.index] == ':') {
                            result.tag = .coloncolon;
                            self.index += 1;
                        } else if (self.buffer[self.index] == '=') {
                            result.tag = .coloneq;
                            self.index += 1;
                        } else result.tag = .colon;
                    },
                    '?' => {
                        result.tag = .question;
                        self.index += 1;
                        self.nlsemi = true;
                    },
                    '(' => {
                        result.tag = .lparen;
                        self.index += 1;
                    },
                    ')' => {
                        result.tag = .rparen;
                        self.index += 1;
                        self.nlsemi = true;
                    },
                    '[' => {
                        result.tag = .lsquare;
                        self.index += 1;
                    },
                    ']' => {
                        result.tag = .rsquare;
                        self.index += 1;
                        self.nlsemi = true;
                    },
                    '{' => {
                        if (self.mlir_maybe) {
                            // Capture nested braces content as a single mlir_content token
                            result.tag = .mlir_content;
                            const block_start = self.index; // at '{'
                            var depth: usize = 1;
                            self.index += 1; // move past initial '{'
                            while (self.index < self.buffer.len and depth > 0) {
                                const ch = self.buffer[self.index];
                                if (ch == '{') {
                                    depth += 1;
                                    self.index += 1;
                                    continue;
                                }
                                if (ch == '}') {
                                    depth -= 1;
                                    self.index += 1; // include this '}'
                                    if (depth == 0) break;
                                    continue;
                                }
                                self.index += 1;
                            }
                            // The token slice will include the full "{...}" block
                            result.loc.start = block_start;
                            self.mlir_maybe = false;
                            self.nlsemi = true;
                        } else {
                            result.tag = .lcurly;
                            self.index += 1;
                        }
                    },
                    '}' => {
                        result.tag = .rcurly;
                        self.index += 1;
                        self.nlsemi = true;
                    },
                    '#' => {
                        result.tag = .pound;
                        self.index += 1;
                    },
                    else => continue :state .invalid,
                }
            },

            // ===== NLSEMI =====
            .nlsemi => {
                // skip spaces/tabs/FF
                while (true) : (self.index += 1) {
                    const c = self.buffer[self.index];
                    switch (c) {
                        0 => {
                            if (self.index == self.buffer.len) {
                                self.nlsemi = false;
                                return .{ .tag = .eos, .loc = .{ .start = self.index, .end = self.index } };
                            } else continue :state .invalid;
                        },
                        ' ', '\t', 0x0c => {},
                        ';' => {
                            // semicolon yields EOS, consume and return to default
                            self.index += 1;
                            self.nlsemi = false;
                            return .{ .tag = .eos, .loc = .{ .start = self.index - 1, .end = self.index } };
                        },
                        '/' => {
                            if (self.buffer[self.index + 1] == '*') {
                                // block comment: skip then EOS
                                var depth: usize = 1;
                                self.index += 2;
                                while (self.index < self.buffer.len and depth > 0) {
                                    if (self.buffer[self.index] == '/' and self.buffer[self.index + 1] == '*') {
                                        depth += 1;
                                        self.index += 2;
                                        continue;
                                    }
                                    if (self.buffer[self.index] == '*' and self.buffer[self.index + 1] == '/') {
                                        depth -= 1;
                                        self.index += 2;
                                        continue;
                                    }
                                    self.index += 1;
                                }
                                self.nlsemi = false;
                                return .{ .tag = .eos, .loc = .{ .start = self.index, .end = self.index } };
                            } else if (self.buffer[self.index + 1] == '/') {
                                // line comment: skip to EOL and let newline rule below emit EOS
                                while (self.index < self.buffer.len and self.buffer[self.index] != '\n' and self.buffer[self.index] != '\r') self.index += 1;
                                if (self.index > 0) self.index -= 1;
                                continue;
                            } else {
                                // other slash → break NLSEMI, resume default
                                self.nlsemi = false;
                                result.loc.start = self.index;
                                continue :state .start;
                            }
                        },
                        '\r', '\n' => {
                            // consume all newlines
                            if (self.buffer[self.index] == '\r' and self.buffer[self.index + 1] == '\n') self.index += 2 else self.index += 1;
                            while (self.buffer[self.index] == '\r' or self.buffer[self.index] == '\n') self.index += 1;

                            // predicate: do not emit EOS if next non-space/tab/FF (on same line) is '}'
                            var j = self.index;
                            while (self.buffer[j] == ' ' or self.buffer[j] == '\t' or self.buffer[j] == 0x0c) j += 1;
                            if (self.buffer[j] == '}') {
                                self.nlsemi = false;
                                result.loc.start = self.index;
                                continue :state .start;
                            }
                            self.nlsemi = false;
                            return .{ .tag = .eos, .loc = .{ .start = self.index, .end = self.index } };
                        },
                        else => {
                            // any other char → exit NLSEMI without EOS
                            self.nlsemi = false;
                            result.loc.start = self.index;
                            continue :state .start;
                        },
                    }
                }
            },

            // ===== identifiers / keywords =====
            .identifier => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    'a'...'z', 'A'...'Z', '_', '0'...'9' => continue :state .identifier,
                    else => {
                        // if we had 'asm' and next non-space is '{', consume raw asm block
                        if (self.asm_maybe) {
                            var j = self.index;
                            while (self.buffer[j] == ' ' or self.buffer[j] == '\t') j += 1;
                            if (self.buffer[j] == '{') {
                                result.tag = .raw_asm_block;
                                self.index = j + 1;
                                // read until matching first '}'
                                while (self.index < self.buffer.len and self.buffer[self.index] != '}') self.index += 1;
                                if (self.index < self.buffer.len and self.buffer[self.index] == '}') self.index += 1;
                                self.nlsemi = true;
                                // Do not fall through to keyword/ident finalization
                            }
                        }
                        if (result.tag == .identifier) {
                            const slice = self.buffer[result.loc.start..self.index];
                            if (Token.getKeyword(slice)) |kw| {
                                result.tag = kw;
                                // NLSEMI keywords
                                switch (kw) {
                                    .keyword_any,
                                    .keyword_await,
                                    .keyword_break,
                                    .keyword_continue,
                                    .keyword_false,
                                    .keyword_noreturn,
                                    .keyword_null,
                                    .keyword_return,
                                    .keyword_true,
                                    .keyword_type,
                                    .keyword_undefined,
                                    => self.nlsemi = true,
                                    else => {},
                                }
                                // latch mlir detection to capture following '{...}' as one token
                                if (kw == .keyword_mlir) self.mlir_maybe = true;
                            } else {
                                result.tag = .identifier;
                                self.nlsemi = true;
                            }
                        }
                    },
                }
            },

            .raw_ident_after_rhash => unreachable, // handled inline above

            // ===== strings =====
            .string_literal => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    0 => result.tag = .invalid,
                    '"' => self.index += 1,
                    '\\' => continue :state .string_escape,
                    '\n', '\r' => result.tag = .invalid,
                    else => continue :state .string_literal,
                }
                self.nlsemi = true;
            },

            .string_escape => {
                self.index += 1; // accept any escaped char (including \n)
                switch (self.buffer[self.index]) {
                    0 => result.tag = .invalid,
                    else => continue :state .string_literal,
                }
            },

            .char_literal => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    0 => result.tag = .invalid,
                    '\'' => self.index += 1, // empty char invalid but caught by parser later if needed
                    '\\' => continue :state .char_escape,
                    '\n', '\r', '\t' => result.tag = .invalid,
                    else => continue :state .char_literal,
                }
                self.nlsemi = true;
            },

            .char_escape => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    0 => result.tag = .invalid,
                    '\'' => self.index += 1,
                    else => continue :state .char_literal,
                }
            },

            .byte_string_literal => {
                // Entry at 'b' of b"...": skip b"
                self.index += 2;
                continue :state .byte_string_body;
            },

            .byte_string_body => {
                switch (self.buffer[self.index]) {
                    0 => result.tag = .invalid,
                    '"' => { // closing quote
                        self.index += 1;
                    },
                    '\\' => { // simple escape: consume the backslash + next char
                        self.index += 2;
                        continue :state .byte_string_body;
                    },
                    '\n', '\r' => result.tag = .invalid,
                    else => {
                        self.index += 1;
                        continue :state .byte_string_body;
                    },
                }
                self.nlsemi = true;
            },

            .byte_char_literal => {
                // start at b'
                self.index += 2;
                switch (self.buffer[self.index]) {
                    0 => result.tag = .invalid,
                    '\\' => {
                        self.index += 2;
                    },
                    '\n', '\r', '\t', '\'' => result.tag = .invalid,
                    else => self.index += 1,
                }
                if (result.tag != .invalid) {
                    if (self.buffer[self.index] != '\'') result.tag = .invalid else self.index += 1;
                    self.nlsemi = true;
                }
            },

            .raw_string_prefix => {
                // support r" .. ", r#".."# .. r##".."## and br".." variants.
                // detect br?  If starts with 'b' and next 'r'
                if (self.buffer[self.index] == 'b' and self.buffer[self.index + 1] == 'r') {
                    self.index += 2;
                } else if (self.buffer[self.index] == 'r') {
                    self.index += 1;
                } else {
                    // from identifier path for raw_byte_string_literal; shift to 'r'
                    self.index += 0;
                }
                self.raw_hashes = 0;
                while (self.buffer[self.index] == '#') : (self.index += 1) self.raw_hashes += 1;
                if (self.buffer[self.index] != '"') {
                    result.tag = .invalid;
                } else {
                    self.index += 1;
                    continue :state .raw_string_body;
                }
            },

            .raw_string_body => {
                switch (self.buffer[self.index]) {
                    0 => result.tag = .invalid,
                    '"' => continue :state .raw_string_maybe_close,
                    else => {
                        self.index += 1;
                        continue :state .raw_string_body;
                    },
                }
            },

            .raw_string_maybe_close => {
                var k: usize = 0;
                while (k < self.raw_hashes and self.buffer[self.index + 1 + k] == '#') : (k += 1) {}
                if (k == self.raw_hashes) {
                    self.index += 1 + k; // consume '"' and the hashes
                    self.nlsemi = true;
                } else {
                    self.index += 1; // treat the '"' as part of body
                    continue :state .raw_string_body;
                }
            },
            // ===== raw asm block after 'asm' + WS + '{' =====
            .maybe_raw_asm_ws => unreachable, // handled in identifier path

            .raw_asm_body => unreachable,

            // ===== numbers =====
            .int => switch (self.buffer[self.index]) {
                // base-prefixed integers
                'x' => { // 0x...
                    if (self.buffer[result.loc.start] == '0') {
                        self.index += 1;
                        while (isHex(self.buffer[self.index]) or self.buffer[self.index] == '_') self.index += 1;
                        if (self.buffer[self.index] == 'i' and !isXIDContinue(self.buffer[self.index + 1])) {
                            self.index += 1;
                            result.tag = .imaginary_literal;
                            self.nlsemi = true;
                        } else {
                            result.tag = .integer_literal;
                            self.nlsemi = true;
                        }
                    }
                },
                'o' => { // 0o...
                    if (self.buffer[result.loc.start] == '0') {
                        self.index += 1;
                        while (isOct(self.buffer[self.index]) or self.buffer[self.index] == '_') self.index += 1;
                        if (self.buffer[self.index] == 'i' and !isXIDContinue(self.buffer[self.index + 1])) {
                            self.index += 1;
                            result.tag = .imaginary_literal;
                            self.nlsemi = true;
                        } else {
                            result.tag = .integer_literal;
                            self.nlsemi = true;
                        }
                    }
                },
                'b' => { // 0b...
                    if (self.buffer[result.loc.start] == '0') {
                        self.index += 1;
                        while ((self.buffer[self.index] == '0' or self.buffer[self.index] == '1') or self.buffer[self.index] == '_') self.index += 1;
                        if (self.buffer[self.index] == 'i' and !isXIDContinue(self.buffer[self.index + 1])) {
                            self.index += 1;
                            result.tag = .imaginary_literal;
                            self.nlsemi = true;
                        } else {
                            result.tag = .integer_literal;
                            self.nlsemi = true;
                        }
                    }
                },

                // decimal: keep consuming digits/underscores
                '0'...'9', '_' => {
                    self.index += 1;
                    continue :state .int;
                },

                // decimal with dot: DEC_LITERAL '.' {floatDotPossible()}?
                '.' => {
                    if (!self.allow_float) {
                        // Not allowed to make a float here → leave '.' for next token
                        self.scanIntSuffix();
                        if (self.buffer[self.index] == 'i' and !isXIDContinue(self.buffer[self.index + 1])) {
                            self.index += 1;
                            result.tag = .imaginary_literal;
                        } else result.tag = .integer_literal;
                        self.nlsemi = true;
                    } else if (!self.floatDotPossible()) {
                        // Same: do not consume '.', finish as integer
                        self.scanIntSuffix();
                        if (self.buffer[self.index] == 'i' and !isXIDContinue(self.buffer[self.index + 1])) {
                            self.index += 1;
                            result.tag = .imaginary_literal;
                        } else result.tag = .integer_literal;
                        self.nlsemi = true;
                    } else {
                        // consume '.' and continue as float (fractional digits optional)
                        self.index += 1;
                        while (isDec(self.buffer[self.index]) or self.buffer[self.index] == '_') self.index += 1;
                        continue :state .float_exponent;
                    }
                },

                // exponent-only float: DEC_LITERAL FLOAT_EXPONENT
                'e', 'E', 'p', 'P' => {
                    if (!self.allow_float) {
                        // back off: finish integer, leave exponent for next token
                        self.scanIntSuffix();
                        if (self.buffer[self.index] == 'i' and !isXIDContinue(self.buffer[self.index + 1])) {
                            self.index += 1;
                            result.tag = .imaginary_literal;
                        } else result.tag = .integer_literal;
                        self.nlsemi = true;
                    } else {
                        continue :state .int_exponent;
                    }
                },

                else => {
                    // plain integer with optional integer suffix, maybe imaginary
                    self.scanIntSuffix();
                    if (self.buffer[self.index] == 'i' and !isXIDContinue(self.buffer[self.index + 1])) {
                        self.index += 1;
                        result.tag = .imaginary_literal;
                    } else result.tag = .integer_literal;
                    self.nlsemi = true;
                },
            },

            .int_exponent => {
                // consume exponent: [eEpP] [+-]? '_'* DEC_LITERAL
                self.index += 1; // the e/E/p/P
                if (self.buffer[self.index] == '+' or self.buffer[self.index] == '-') self.index += 1;
                while (self.buffer[self.index] == '_') self.index += 1;
                if (isDec(self.buffer[self.index])) {
                    self.index += 1;
                    while (isDec(self.buffer[self.index]) or self.buffer[self.index] == '_') self.index += 1;
                }
                continue :state .suffix_check;
            },

            .float_exponent => {
                // optional exponent after DEC_LITERAL '.' DEC_LITERAL?
                if (self.buffer[self.index] == 'e' or self.buffer[self.index] == 'E' or
                    self.buffer[self.index] == 'p' or self.buffer[self.index] == 'P')
                {
                    self.index += 1;
                    if (self.buffer[self.index] == '+' or self.buffer[self.index] == '-') self.index += 1;
                    while (self.buffer[self.index] == '_') self.index += 1;
                    if (isDec(self.buffer[self.index])) {
                        self.index += 1;
                        while (isDec(self.buffer[self.index]) or self.buffer[self.index] == '_') self.index += 1;
                    }
                }
                continue :state .suffix_check;
            },

            .suffix_check => {
                // FLOAT_SUFFIX?
                if (startsWith(self.buffer, self.index, "f32") or startsWith(self.buffer, self.index, "f64")) {
                    self.index += 3;
                    if (self.buffer[self.index] == 'i' and !isXIDContinue(self.buffer[self.index + 1])) {
                        self.index += 1;
                        result.tag = .imaginary_literal;
                    } else result.tag = .float_literal;
                    self.nlsemi = true;
                } else {
                    // if we got here via exponent or '.' path → it's a float; else an int
                    // (We only jump here from exponent / float paths in this implementation.)
                    if (self.buffer[self.index] == 'i' and !isXIDContinue(self.buffer[self.index + 1])) {
                        self.index += 1;
                        result.tag = .imaginary_literal;
                    } else result.tag = .float_literal;
                    self.nlsemi = true;
                }
            },

            // ===== operators / punctuation =====
            .plus => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '=' => {
                        result.tag = .plus_equal;
                        self.index += 1;
                    },
                    '%' => continue :state .plus_percent,
                    '|' => continue :state .plus_pipe,
                    else => result.tag = .plus,
                }
            },

            .plus_percent => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '=' => {
                        result.tag = .plus_percent_equal;
                        self.index += 1;
                    },
                    else => result.tag = .plus_percent,
                }
            },

            .plus_pipe => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '=' => {
                        result.tag = .plus_pipe_equal;
                        self.index += 1;
                    },
                    else => result.tag = .plus_pipe,
                }
            },

            .minus => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '>' => {
                        result.tag = .rarrow;
                        self.index += 1;
                    },
                    '=' => {
                        result.tag = .minus_equal;
                        self.index += 1;
                    },
                    '%' => continue :state .minus_percent,
                    '|' => continue :state .minus_pipe,
                    else => result.tag = .minus,
                }
            },

            .minus_percent => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '=' => {
                        result.tag = .minus_percent_equal;
                        self.index += 1;
                    },
                    else => result.tag = .minus_percent,
                }
            },

            .minus_pipe => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '=' => {
                        result.tag = .minus_pipe_equal;
                        self.index += 1;
                    },
                    else => result.tag = .minus_pipe,
                }
            },

            .asterisk => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '=' => {
                        result.tag = .star_equal;
                        self.index += 1;
                    },
                    '%' => continue :state .asterisk_percent,
                    '|' => continue :state .asterisk_pipe,
                    else => result.tag = .star,
                }
            },

            .asterisk_percent => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '=' => {
                        result.tag = .star_percent_equal;
                        self.index += 1;
                    },
                    else => result.tag = .star_percent,
                }
            },

            .asterisk_pipe => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '=' => {
                        result.tag = .star_pipe_equal;
                        self.index += 1;
                    },
                    else => result.tag = .star_pipe,
                }
            },

            .percent => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '=' => {
                        result.tag = .percent_equal;
                        self.index += 1;
                    },
                    else => result.tag = .percent,
                }
            },

            .caret => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '=' => {
                        result.tag = .caret_equal;
                        self.index += 1;
                    },
                    else => result.tag = .caret,
                }
            },

            .ampersand => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '=' => {
                        result.tag = .and_equal;
                        self.index += 1;
                    },
                    else => result.tag = .b_and,
                }
            },

            .pipe => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '=' => {
                        result.tag = .or_equal;
                        self.index += 1;
                    },
                    '|' => {
                        result.tag = .pipe_pipe;
                        self.index += 1;
                    },
                    else => result.tag = .b_or,
                }
            },

            .equal => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '=' => {
                        result.tag = .eqeq;
                        self.index += 1;
                    },
                    '>' => {
                        result.tag = .fatarrow;
                        self.index += 1;
                    },
                    else => result.tag = .eq,
                }
            },

            .bang => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '=' => {
                        result.tag = .ne;
                        self.index += 1;
                    },
                    else => {
                        result.tag = .bang;
                        self.nlsemi = true;
                    },
                }
            },

            .angle_bracket_left => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '<' => continue :state .angle_bracket_angle_bracket_left,
                    '=' => {
                        result.tag = .le;
                        self.index += 1;
                    },
                    else => result.tag = .lt,
                }
            },

            .angle_bracket_angle_bracket_left => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '=' => {
                        result.tag = .shl_equal;
                        self.index += 1;
                    },
                    '|' => continue :state .angle_bracket_angle_bracket_left_pipe,
                    else => result.tag = .shl,
                }
            },

            .angle_bracket_angle_bracket_left_pipe => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '=' => {
                        result.tag = .shl_pipe_equal;
                        self.index += 1;
                    },
                    else => result.tag = .shl_pipe,
                }
            },

            .angle_bracket_right => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '>' => continue :state .angle_bracket_angle_bracket_right,
                    '=' => {
                        result.tag = .ge;
                        self.index += 1;
                    },
                    else => result.tag = .gt,
                }
            },

            .angle_bracket_angle_bracket_right => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '=' => {
                        result.tag = .shr_equal;
                        self.index += 1;
                    },
                    else => result.tag = .shr,
                }
            },

            .period => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '.' => continue :state .period_2,
                    '*' => {
                        result.tag = .dotstar;
                        self.index += 1;
                        self.nlsemi = true;
                    },
                    '(' => {
                        result.tag = .dot_lparen;
                        self.index += 1;
                    },
                    '[' => {
                        result.tag = .dot_lsquare;
                        self.index += 1;
                    },
                    '{' => {
                        result.tag = .dot_lcurly;
                        self.index += 1;
                    },
                    else => result.tag = .dot,
                }
            },

            .period_2 => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '.' => {
                        result.tag = .dotdotdot;
                        self.index += 1;
                    },
                    '=' => {
                        result.tag = .dotdoteq;
                        self.index += 1;
                    },
                    else => result.tag = .dotdot,
                }
            },

            // ===== comments =====
            .slash => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '/' => continue :state .line_comment,
                    '*' => {
                        self.block_depth = 1;
                        self.index += 1;
                        continue :state .block_comment;
                    },
                    '=' => {
                        result.tag = .slash_equal;
                        self.index += 1;
                    },
                    else => result.tag = .slash,
                }
            },

            .line_comment => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    0 => {
                        if (self.index != self.buffer.len) continue :state .invalid else return .{ .tag = .eof, .loc = .{ .start = self.index, .end = self.index } };
                    },
                    '\n', '\r' => {
                        self.index += 1;
                        result.loc.start = self.index;
                        continue :state .start;
                    },
                    else => continue :state .line_comment,
                }
            },

            .block_comment => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    0 => result.tag = .invalid,
                    '/' => {
                        if (self.buffer[self.index + 1] == '*') {
                            self.block_depth += 1;
                            self.index += 1;
                        } else continue :state .block_comment;
                    },
                    '*' => {
                        if (self.buffer[self.index + 1] == '/') {
                            self.block_depth -= 1;
                            self.index += 1;
                            if (self.block_depth == 0) {
                                // done skipping
                                self.index += 1;
                                result.loc.start = self.index;
                                continue :state .start;
                            }
                        }
                    },
                    else => continue :state .block_comment,
                }
            },

            // ===== right delimiters that also enable NLSEMI in grammar =====
            .rparen_emit => unreachable,
            .rsquare_emit => unreachable,
            .rcurly_emit => unreachable,

            .invalid => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    0 => if (self.index == self.buffer.len) {
                        result.tag = .invalid;
                    } else {
                        continue :state .invalid;
                    },
                    '\n' => result.tag = .invalid,
                    else => continue :state .invalid,
                }
            },
        }

        result.loc.end = self.index;
        self.lt2 = self.lt1;
        self.lt1 = result.tag;
        return result;
    }

    // --- helpers ---

    fn startsWith(buf: []const u8, off: usize, s: []const u8) bool {
        return off + s.len <= buf.len and std.mem.eql(u8, buf[off .. off + s.len], s);
    }

    inline fn peek(self: *Tokenizer) u8 {
        return if (self.index < self.buffer.len) self.buffer[self.index] else 0;
    }

    fn scanIdent(self: *Tokenizer) void {
        while (isXIDContinue(self.buffer[self.index])) self.index += 1;
    }

    fn scanIntSuffix(self: *Tokenizer) void {
        const suffixes = .{
            "u8", "u16", "u32", "u64", "u128", "usize",
            "i8", "i16", "i32", "i64", "i128", "isize",
        };
        inline for (suffixes) |s| {
            if (startsWith(self.buffer, self.index, s)) {
                self.index += s.len;
                break;
            }
        }
    }

    fn floatLiteralPossible(self: *Tokenizer) bool {
        // if we don't have enough history, allow
        if (self.lt1 == .invalid or self.lt2 == .invalid) return true;
        if (self.lt1 != .dot) return true;

        // If last token was DOT, disallow starting a float when previous token was any of:
        return switch (self.lt2) {
            .char_literal, .string_literal, .raw_string_literal, .byte_literal, .byte_string_literal, .raw_byte_string_literal, .integer_literal, .gt, .rcurly, .rsquare, .rparen, .identifier, .raw_identifier => false,
            else => true,
        };
    }

    fn floatDotPossible(self: *Tokenizer) bool {
        // Called with self.index on the '.' char
        const next_char = if (self.index + 1 < self.buffer.len) self.buffer[self.index + 1] else 0;

        // block '.' or '_' immediately after the dot
        if (next_char == '.' or next_char == '_') return false;

        // allow 1.f32 / 1.f64 specifically
        if (next_char == 'f') {
            const a = if (self.index + 2 < self.buffer.len) self.buffer[self.index + 2] else 0;
            const b = if (self.index + 3 < self.buffer.len) self.buffer[self.index + 3] else 0;
            if (a == '3' and b == '2') return true;
            if (a == '6' and b == '4') return true;
            return false;
        }

        // block identifiers after the dot
        if ((next_char >= 'a' and next_char <= 'z') or (next_char >= 'A' and next_char <= 'Z')) return false;

        // otherwise OK (includes EOF / newline / digits / operators)
        return true;
    }
};

// ===== character-class helpers (ASCII-only; plug in Unicode XID as needed) =====
fn isDec(c: u8) bool {
    return c >= '0' and c <= '9';
}
fn isHex(c: u8) bool {
    return (c >= '0' and c <= '9') or (c >= 'a' and c <= 'f') or (c >= 'A' and c <= 'F');
}
fn isOct(c: u8) bool {
    return c >= '0' and c <= '7';
}
fn isXIDStart(c: u8) bool {
    return (c >= 'A' and c <= 'Z') or (c >= 'a' and c <= 'z') or c == '_';
}
fn isXIDContinue(c: u8) bool {
    return isXIDStart(c) or isDec(c);
}
