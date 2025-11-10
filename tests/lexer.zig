const std = @import("std");
const lex = @import("compiler").lexer;
const ArrayList = std.array_list.Managed;
const Tag = lex.Token.Tag;

const testing = std.testing;
fn testSingle(source: [:0]const u8, expected: []const lex.Token.Tag) !void {
    var lexer = lex.Tokenizer.init(source, 0, .normal);
    var i: usize = 0;
    while (true) {
        const tok = lexer.next();
        if (tok.tag == .eof) break;
        if (i >= expected.len) {
            try testing.expect(false);
            return error.TooManyTokens;
        }
        try testing.expectEqual(expected[i], tok.tag);
        i += 1;
    }
    try testing.expectEqual(expected.len, i);
}

test "invalid" {
    try testSingle("! @ $ ~ `", &.{ .bang, .at, .invalid });
}

test "operators and punctuations" {
    try testSingle("+ - * / % ^ ! & | << >> += -= -> *= /= %= ^= &= |= <<= >>= <<| <<|= +| +|= -| -|= *| *|=  +% +%= -% -%= *% *%= = == != > < >= <= @ . .. .* ... ..=  , ; : :: := => ? { } [ ] ( )", &.{
        .plus,                .minus,          .star,               .slash,           .percent,     .caret,            .bang,         .b_and,           .b_or,          .ltlt,               .gtgt,
        .plus_equal,          .minus_equal,    .rarrow,             .star_equal,      .slash_equal, .percent_equal,    .caret_equal,  .and_equal,       .or_equal,      .shl_equal,          .shr_equal,
        .shl_pipe,            .shl_pipe_equal, .plus_pipe,          .plus_pipe_equal, .minus_pipe,  .minus_pipe_equal, .star_pipe,    .star_pipe_equal, .plus_percent,  .plus_percent_equal, .minus_percent,
        .minus_percent_equal, .star_percent,   .star_percent_equal, .equal,           .equal_equal, .not_equal,        .greater_than, .less_than,       .greater_equal, .less_equal,         .at,
        .dot,                 .dotdot,         .dotstar,            .dotdotdot,       .dotdoteq,    .comma,            .eos,          .colon,           .coloncolon,    .coloneq,            .fatarrow,
        .question,            .lcurly,         .rcurly,             .lsquare,         .rsquare,     .lparen,           .rparen,
    });
}

test "identifiers" {
    try testSingle("foo _bar baz123 _ _1 __ __2", &.{
        .identifier,
        .identifier,
        .identifier,
        .identifier,
        .identifier,
        .identifier,
        .identifier,
    });
}

test "raw identifier" {
    try testSingle("r#", &.{.invalid});
    try testSingle("r#-", &.{.invalid});
    try testSingle("r#foo", &.{.raw_identifier});
    try testSingle("r#while r#f r#comptime r#struct r##return", &.{
        .raw_identifier,
        .raw_identifier,
        .raw_identifier,
        .raw_identifier,
        .raw_identifier,
    });
}

test "keywords" {
    try testSingle("align and any asm async await break catch comptime code complex const continue dyn defer else enum errdefer error export extern false fn for if in is insert import match mlir noreturn null opaque or orelse package proc pub return linksection simd struct threadlocal tensor test true type typeof union undefined unreachable variant while", &.{
        .keyword_align, .keyword_and, .keyword_any, .keyword_asm, .keyword_async, .keyword_await, .keyword_break, .keyword_catch, .keyword_comptime, .keyword_code, .keyword_complex, .keyword_const, .keyword_continue, .keyword_dyn, .keyword_defer, .keyword_else, .keyword_enum, .keyword_errdefer, .keyword_error, .keyword_export, .keyword_extern, .keyword_false, .keyword_fn, .keyword_for, .keyword_if, .keyword_in, .keyword_is, .keyword_insert, .keyword_import, .keyword_match, .keyword_mlir, .keyword_noreturn, .keyword_null, .keyword_opaque, .keyword_or, .keyword_orelse, .keyword_package, .keyword_proc, .keyword_pub, .keyword_return, .keyword_linksection, .keyword_simd, .keyword_struct, .keyword_threadlocal, .keyword_tensor, .keyword_test, .keyword_true, .keyword_type, .keyword_typeof, .keyword_union, .keyword_undefined, .keyword_unreachable, .keyword_variant, .keyword_while,
    });
}

test "line comment followed by top-level comptime" {
    try testSingle(
        \\// line comment
        \\comptime {}
        \\
    , &.{
        .keyword_comptime,
        .lcurly,
        .rcurly,
    });
}

test "unknown length pointer and then c pointer" {
    try testSingle(
        \\[*]u8
        \\[*c]u8
    , &.{
        .lsquare,
        .star,
        .rsquare,
        .identifier,
        .lsquare,
        .star,
        .identifier,
        .rsquare,
        .identifier,
    });
}

test "code point literal with hex escape" {
    try testSingle(
        \\'\x1b'
    , &.{.char_literal});
    try testSingle(
        \\'\x1'
    , &.{.char_literal});
}

test "newline in char literal" {
    try testSingle(
        \\'
        \\'
    , &.{ .invalid, .invalid });
}

test "newline in string literal" {
    try testSingle(
        \\"
        \\"
    , &.{ .invalid, .invalid });
}

test "raw strings" {
    try testSingle("r\"raw\"", &.{.raw_string_literal});
    try testSingle("r#\"hash\"#", &.{.raw_string_literal});
    try testSingle("r#\"oops", &.{.invalid});
}

test "code point literal with unicode escapes" {
    // Valid unicode escapes
    try testSingle(
        \\'\u{3}'
    , &.{.char_literal});
    try testSingle(
        \\'\u{01}'
    , &.{.char_literal});
    try testSingle(
        \\'\u{2a}'
    , &.{.char_literal});
    try testSingle(
        \\'\u{3f9}'
    , &.{.char_literal});
    try testSingle(
        \\'\u{6E09aBc1523}'
    , &.{.char_literal});
    try testSingle(
        \\"\u{440}"
    , &.{.string_literal});

    // Invalid unicode escapes
    try testSingle(
        \\'\u'
    , &.{.char_literal});
    try testSingle(
        \\'\u{{'
    , &.{.char_literal});
    try testSingle(
        \\'\u{}'
    , &.{.char_literal});
    try testSingle(
        \\'\u{s}'
    , &.{.char_literal});
    try testSingle(
        \\'\u{2z}'
    , &.{.char_literal});
    try testSingle(
        \\'\u{4a'
    , &.{.char_literal});

    // Test old-style unicode literals
    try testSingle(
        \\'\u0333'
    , &.{.char_literal});
    try testSingle(
        \\'\U0333'
    , &.{.char_literal});
}

test "code point literal with unicode code point" {
    try testSingle(
        \\'💩'
    , &.{.char_literal});
}

test "chars" {
    try testSingle("'c'", &.{.char_literal});
}

test "invalid token characters" {
    try testSingle("#", &.{.hash});
    try testSingle("`", &.{.invalid});
    try testSingle("'c", &.{.invalid});
    try testSingle("'", &.{.invalid});
    try testSingle("''", &.{.char_literal});
    try testSingle("'\n'", &.{ .invalid, .invalid });
}

test "invalid literal/comment characters" {
    try testSingle("\"\x00\"", &.{.invalid});
    try testSingle("`\x00`", &.{.invalid});
    try testSingle("//\x00", &.{.invalid});
    try testSingle("//\x1f", &.{.invalid});
    try testSingle("//\x7f", &.{.invalid});
}

test "utf8" {
    try testSingle("//\xc2\x80", &.{});
    try testSingle("//\xf4\x8f\xbf\xbf", &.{});
}

test "invalid utf8" {
    try testSingle("//\x80", &.{});
    try testSingle("//\xbf", &.{});
    try testSingle("//\xf8", &.{});
    try testSingle("//\xff", &.{});
    try testSingle("//\xc2\xc0", &.{});
    try testSingle("//\xe0", &.{});
    try testSingle("//\xf0", &.{});
    try testSingle("//\xf0\x90\x80\xc0", &.{});
}

test "illegal unicode codepoints" {
    // unicode newline characters.U+0085, U+2028, U+2029
    try testSingle("//\xc2\x84", &.{});
    try testSingle("//\xc2\x85", &.{});
    try testSingle("//\xc2\x86", &.{});
    try testSingle("//\xe2\x80\xa7", &.{});
    try testSingle("//\xe2\x80\xa8", &.{});
    try testSingle("//\xe2\x80\xa9", &.{});
    try testSingle("//\xe2\x80\xaa", &.{});
}

test "float literal e exponent" {
    try testSingle("a = 4.94065645841246544177e-324;\n", &.{ .identifier, .equal, .float_literal, .eos });
}

test "float literal p exponent" {
    try testSingle("a = 0x1.a827999fcef32p+1022;\n", &.{ .identifier, .equal, .float_literal, .eos });
}

test "line comment and doc comment" {
    try testSingle("//", &.{});
    try testSingle("// a / b", &.{});
    try testSingle("// /", &.{});
    try testSingle("/// a", &.{.doc_comment});
    try testSingle("///", &.{.doc_comment});
    try testSingle("////", &.{});
    try testSingle("//!", &.{.container_doc_comment});
    try testSingle("//!!", &.{.container_doc_comment});
}

test "line comment followed by identifier" {
    try testSingle(
        \\    Unexpected,
        \\    // another
        \\    Another,
    , &.{
        .identifier,
        .comma,
        .identifier,
        .comma,
    });
}

test "UTF-8 BOM is recognized and skipped" {
    try testSingle("\xEF\xBB\xBFa;\n", &.{
        .identifier,
        .eos,
    });
}

test "correctly parse pointer dereference followed by asterisk" {
    try testSingle("\"b\".* * 10", &.{
        .string_literal,
        .dotstar,
        .star,
        .integer_literal,
    });

    try testSingle("(\"b\".*)* 10", &.{
        .lparen,
        .string_literal,
        .dotstar,
        .rparen,
        .star,
        .integer_literal,
    });

    try testSingle("\"b\".** 10", &.{
        .string_literal,
        .dotstar,
        .star,
        .integer_literal,
    });
}

test "range literals" {
    try testSingle("0...9", &.{ .integer_literal, .dotdotdot, .integer_literal });
    try testSingle("'0'...'9'", &.{ .char_literal, .dotdotdot, .char_literal });
    try testSingle("0x00...0x09", &.{ .integer_literal, .dotdotdot, .integer_literal });
    try testSingle("0b00...0b11", &.{ .integer_literal, .dotdotdot, .integer_literal });
    try testSingle("0o00...0o11", &.{ .integer_literal, .dotdotdot, .integer_literal });
    try testSingle("0o00..=0o11", &.{ .integer_literal, .dotdoteq, .integer_literal });
}

test "number literals decimal" {
    try testSingle("0", &.{.integer_literal});
    try testSingle("1", &.{.integer_literal});
    try testSingle("2", &.{.integer_literal});
    try testSingle("3", &.{.integer_literal});
    try testSingle("4", &.{.integer_literal});
    try testSingle("5", &.{.integer_literal});
    try testSingle("6", &.{.integer_literal});
    try testSingle("7", &.{.integer_literal});
    try testSingle("8", &.{.integer_literal});
    try testSingle("9", &.{.integer_literal});
    try testSingle("1..", &.{ .integer_literal, .dotdot });
    try testSingle("0a", &.{.integer_literal});
    try testSingle("9b", &.{.integer_literal});
    try testSingle("1z", &.{.integer_literal});
    try testSingle("1z_1", &.{.integer_literal});
    try testSingle("9z3", &.{.integer_literal});

    try testSingle("0_0", &.{.integer_literal});
    try testSingle("0001", &.{.integer_literal});
    try testSingle("01234567890", &.{.integer_literal});
    try testSingle("012_345_6789_0", &.{.integer_literal});
    try testSingle("0_1_2_3_4_5_6_7_8_9_0", &.{.integer_literal});

    try testSingle("00_", &.{.integer_literal});
    try testSingle("0_0_", &.{.integer_literal});
    try testSingle("0__0", &.{.integer_literal});
    try testSingle("0_0f", &.{.integer_literal});
    try testSingle("0_0_f", &.{.integer_literal});
    try testSingle("0_0_f_00", &.{.integer_literal});
    try testSingle("1_,", &.{ .integer_literal, .comma });

    try testSingle("0.0", &.{.float_literal});
    try testSingle("1.0", &.{.float_literal});
    try testSingle("10.0", &.{.float_literal});
    try testSingle("0e0", &.{.integer_literal});
    try testSingle("1e0", &.{.integer_literal});
    try testSingle("1e100", &.{.integer_literal});
    try testSingle("1.0e100", &.{.float_literal});
    try testSingle("1.0e+100", &.{.float_literal});
    try testSingle("1.0e-100", &.{.float_literal});
    try testSingle("1_0_0_0.0_0_0_0_0_1e1_0_0_0", &.{.float_literal});

    try testSingle("1.", &.{ .integer_literal, .dot });
    try testSingle("1e", &.{.integer_literal});
    try testSingle("1.e100", &.{.float_literal});
    try testSingle("1.0e1f0", &.{.float_literal});
    try testSingle("1.0p100", &.{.float_literal});
    try testSingle("1.0p-100", &.{.float_literal});
    try testSingle("1.0p1f0", &.{.float_literal});
    try testSingle("1.0_,", &.{ .float_literal, .comma });
    try testSingle("1_.0", &.{.float_literal});
    try testSingle("1._", &.{.float_literal});
    try testSingle("1.a", &.{.float_literal});
    try testSingle("1.z", &.{.float_literal});
    try testSingle("1._0", &.{.float_literal});
    try testSingle("1.+", &.{ .integer_literal, .dot, .plus });
    try testSingle("1._+", &.{ .float_literal, .plus });
    try testSingle("1._e", &.{.float_literal});
    try testSingle("1.0e", &.{.float_literal});
    try testSingle("1.0e,", &.{ .float_literal, .comma });
    try testSingle("1.0e_", &.{.float_literal});
    try testSingle("1.0e+_", &.{.float_literal});
    try testSingle("1.0e-_", &.{.float_literal});
    try testSingle("1.0e0_+", &.{ .float_literal, .plus });
}

test "number literals binary" {
    try testSingle("0b0", &.{.integer_literal});
    try testSingle("0b1", &.{.integer_literal});
    try testSingle("0b2", &.{.integer_literal});
    try testSingle("0b3", &.{.integer_literal});
    try testSingle("0b4", &.{.integer_literal});
    try testSingle("0b5", &.{.integer_literal});
    try testSingle("0b6", &.{.integer_literal});
    try testSingle("0b7", &.{.integer_literal});
    try testSingle("0b8", &.{.integer_literal});
    try testSingle("0b9", &.{.integer_literal});
    try testSingle("0ba", &.{.integer_literal});
    try testSingle("0bb", &.{.integer_literal});
    try testSingle("0bc", &.{.integer_literal});
    try testSingle("0bd", &.{.integer_literal});
    try testSingle("0be", &.{.integer_literal});
    try testSingle("0bf", &.{.integer_literal});
    try testSingle("0bz", &.{.integer_literal});

    try testSingle("0b0000_0000", &.{.integer_literal});
    try testSingle("0b1111_1111", &.{.integer_literal});
    try testSingle("0b10_10_10_10", &.{.integer_literal});
    try testSingle("0b0_1_0_1_0_1_0_1", &.{.integer_literal});
    try testSingle("0b1.", &.{ .integer_literal, .dot });
    try testSingle("0b1.0", &.{.float_literal});

    try testSingle("0B0", &.{.integer_literal});
    try testSingle("0b_", &.{.integer_literal});
    try testSingle("0b_0", &.{.integer_literal});
    try testSingle("0b1_", &.{.integer_literal});
    try testSingle("0b0__1", &.{.integer_literal});
    try testSingle("0b0_1_", &.{.integer_literal});
    try testSingle("0b1e", &.{.integer_literal});
    try testSingle("0b1p", &.{.integer_literal});
    try testSingle("0b1e0", &.{.integer_literal});
    try testSingle("0b1p0", &.{.integer_literal});
    try testSingle("0b1_,", &.{ .integer_literal, .comma });
}

test "number literals octal" {
    try testSingle("0o0", &.{.integer_literal});
    try testSingle("0o1", &.{.integer_literal});
    try testSingle("0o2", &.{.integer_literal});
    try testSingle("0o3", &.{.integer_literal});
    try testSingle("0o4", &.{.integer_literal});
    try testSingle("0o5", &.{.integer_literal});
    try testSingle("0o6", &.{.integer_literal});
    try testSingle("0o7", &.{.integer_literal});
    try testSingle("0o8", &.{.integer_literal});
    try testSingle("0o9", &.{.integer_literal});
    try testSingle("0oa", &.{.integer_literal});
    try testSingle("0ob", &.{.integer_literal});
    try testSingle("0oc", &.{.integer_literal});
    try testSingle("0od", &.{.integer_literal});
    try testSingle("0oe", &.{.integer_literal});
    try testSingle("0of", &.{.integer_literal});
    try testSingle("0oz", &.{.integer_literal});

    try testSingle("0o01234567", &.{.integer_literal});
    try testSingle("0o0123_4567", &.{.integer_literal});
    try testSingle("0o01_23_45_67", &.{.integer_literal});
    try testSingle("0o0_1_2_3_4_5_6_7", &.{.integer_literal});
    try testSingle("0o7.", &.{ .integer_literal, .dot });
    try testSingle("0o7.0", &.{.float_literal});

    try testSingle("0O0", &.{.integer_literal});
    try testSingle("0o_", &.{.integer_literal});
    try testSingle("0o_0", &.{.integer_literal});
    try testSingle("0o1_", &.{.integer_literal});
    try testSingle("0o0__1", &.{.integer_literal});
    try testSingle("0o0_1_", &.{.integer_literal});
    try testSingle("0o1e", &.{.integer_literal});
    try testSingle("0o1p", &.{.integer_literal});
    try testSingle("0o1e0", &.{.integer_literal});
    try testSingle("0o1p0", &.{.integer_literal});
    try testSingle("0o_,", &.{ .integer_literal, .comma });
}

test "number literals hexadecimal" {
    try testSingle("0x0", &.{.integer_literal});
    try testSingle("0x1", &.{.integer_literal});
    try testSingle("0x2", &.{.integer_literal});
    try testSingle("0x3", &.{.integer_literal});
    try testSingle("0x4", &.{.integer_literal});
    try testSingle("0x5", &.{.integer_literal});
    try testSingle("0x6", &.{.integer_literal});
    try testSingle("0x7", &.{.integer_literal});
    try testSingle("0x8", &.{.integer_literal});
    try testSingle("0x9", &.{.integer_literal});
    try testSingle("0xa", &.{.integer_literal});
    try testSingle("0xb", &.{.integer_literal});
    try testSingle("0xc", &.{.integer_literal});
    try testSingle("0xd", &.{.integer_literal});
    try testSingle("0xe", &.{.integer_literal});
    try testSingle("0xf", &.{.integer_literal});
    try testSingle("0xA", &.{.integer_literal});
    try testSingle("0xB", &.{.integer_literal});
    try testSingle("0xC", &.{.integer_literal});
    try testSingle("0xD", &.{.integer_literal});
    try testSingle("0xE", &.{.integer_literal});
    try testSingle("0xF", &.{.integer_literal});
    try testSingle("0x0z", &.{.integer_literal});
    try testSingle("0xz", &.{.integer_literal});

    try testSingle("0x0123456789ABCDEF", &.{.integer_literal});
    try testSingle("0x0123_4567_89AB_CDEF", &.{.integer_literal});
    try testSingle("0x01_23_45_67_89AB_CDE_F", &.{.integer_literal});
    try testSingle("0x0_1_2_3_4_5_6_7_8_9_A_B_C_D_E_F", &.{.integer_literal});

    try testSingle("0X0", &.{.integer_literal});
    try testSingle("0x_", &.{.integer_literal});
    try testSingle("0x_1", &.{.integer_literal});
    try testSingle("0x1_", &.{.integer_literal});
    try testSingle("0x0__1", &.{.integer_literal});
    try testSingle("0x0_1_", &.{.integer_literal});
    try testSingle("0x_,", &.{ .integer_literal, .comma });

    try testSingle("0x1.0", &.{.float_literal});
    try testSingle("0xF.0", &.{.float_literal});
    try testSingle("0xF.F", &.{.float_literal});
    try testSingle("0xF.Fp0", &.{.float_literal});
    try testSingle("0xF.FP0", &.{.float_literal});
    try testSingle("0x1p0", &.{.integer_literal});
    try testSingle("0xfp0", &.{.integer_literal});
    try testSingle("0x1.0+0xF.0", &.{ .float_literal, .plus, .float_literal });

    try testSingle("0x1.", &.{ .integer_literal, .dot });
    try testSingle("0xF.", &.{ .integer_literal, .dot });
    try testSingle("0x1.+0xF.", &.{ .integer_literal, .dot, .plus, .integer_literal, .dot });
    try testSingle("0xff.p10", &.{.float_literal});

    try testSingle("0x0123456.789ABCDEF", &.{.float_literal});
    try testSingle("0x0_123_456.789_ABC_DEF", &.{.float_literal});
    try testSingle("0x0_1_2_3_4_5_6.7_8_9_A_B_C_D_E_F", &.{.float_literal});
    try testSingle("0x0p0", &.{.integer_literal});
    try testSingle("0x0.0p0", &.{.float_literal});
    try testSingle("0xff.ffp10", &.{.float_literal});
    try testSingle("0xff.ffP10", &.{.float_literal});
    try testSingle("0xffp10", &.{.integer_literal});
    try testSingle("0xff_ff.ff_ffp1_0_0_0", &.{.float_literal});
    try testSingle("0xf_f_f_f.f_f_f_fp+1_000", &.{.float_literal});
    try testSingle("0xf_f_f_f.f_f_f_fp-1_00_0", &.{.float_literal});

    try testSingle("0x1e", &.{.integer_literal});
    try testSingle("0x1e0", &.{.integer_literal});
    try testSingle("0x1p", &.{.integer_literal});
    try testSingle("0xfp0z1", &.{.integer_literal});
    try testSingle("0xff.ffpff", &.{.float_literal});
    try testSingle("0x0.p", &.{.float_literal});
    try testSingle("0x0.z", &.{.float_literal});
    try testSingle("0x0._", &.{.float_literal});
    try testSingle("0x0_.0", &.{.float_literal});
    try testSingle("0x0_.0.0", &.{ .float_literal, .dot, .integer_literal });
    try testSingle("0x0._0", &.{.float_literal});
    try testSingle("0x0.0_", &.{.float_literal});
    try testSingle("0x0_p0", &.{.integer_literal});
    try testSingle("0x0_.p0", &.{.float_literal});
    try testSingle("0x0._p0", &.{.float_literal});
    try testSingle("0x0.0_p0", &.{.float_literal});
    try testSingle("0x0._0p0", &.{.float_literal});
    try testSingle("0x0.0p_0", &.{.float_literal});
    try testSingle("0x0.0p+_0", &.{.float_literal});
    try testSingle("0x0.0p-_0", &.{.float_literal});
    try testSingle("0x0.0p0_", &.{.float_literal});
}

test "saturating operators" {
    try testSingle("<<", &.{.ltlt});
    try testSingle("<<|", &.{.shl_pipe});
    try testSingle("<<|=", &.{.shl_pipe_equal});

    try testSingle("*", &.{.star});
    try testSingle("*|", &.{.star_pipe});
    try testSingle("*|=", &.{.star_pipe_equal});

    try testSingle("+", &.{.plus});
    try testSingle("+|", &.{.plus_pipe});
    try testSingle("+|=", &.{.plus_pipe_equal});

    try testSingle("-", &.{.minus});
    try testSingle("-|", &.{.minus_pipe});
    try testSingle("-|=", &.{.minus_pipe_equal});
}

test "null byte before eof" {
    try testSingle("123 \x00 456", &.{ .integer_literal, .invalid });
    try testSingle("//\x00", &.{.invalid});
    try testSingle("\\\\\x00", &.{.invalid});
    try testSingle("\x00", &.{.invalid});
    try testSingle("// NUL\x00\n", &.{.invalid});
    try testSingle("///\x00\n", &.{ .doc_comment, .invalid });
    try testSingle("/// NUL\x00\n", &.{ .doc_comment, .invalid });
}

test "multi line string literal with only 1 backslash" {
    try testSingle("x \\\n;", &.{ .identifier, .invalid, .eos });
}

test "invalid token with unfinished escape right before eof" {
    try testSingle("\"\\", &.{.invalid});
    try testSingle("'\\", &.{.invalid});
    try testSingle("'\\u", &.{.invalid});
}

test "invalid tabs and carriage returns" {
    try testSingle("//\t", &.{.invalid});
    try testSingle("// \t", &.{.invalid});
    try testSingle("///\t", &.{.invalid});
    try testSingle("/// \t", &.{.invalid});
    try testSingle("//!\t", &.{.invalid});
    try testSingle("//! \t", &.{.invalid});

    try testSingle("//\r", &.{.invalid});
    try testSingle("// \r", &.{.invalid});
    try testSingle("///\r", &.{.invalid});
    try testSingle("/// \r", &.{.invalid});
    try testSingle("//\r ", &.{.invalid});
    try testSingle("// \r ", &.{.invalid});
    try testSingle("///\r ", &.{.invalid});
    try testSingle("/// \r ", &.{.invalid});
    try testSingle("//\r\n", &.{});
    try testSingle("// \r\n", &.{});
    try testSingle("///\r\n", &.{.doc_comment});
    try testSingle("/// \r\n", &.{.doc_comment});
    try testSingle("//!\r", &.{.invalid});
    try testSingle("//! \r", &.{.invalid});
    try testSingle("//!\r ", &.{.invalid});
    try testSingle("//! \r ", &.{.invalid});
    try testSingle("//!\r\n", &.{.container_doc_comment});
    try testSingle("//! \r\n", &.{.container_doc_comment});

    try testSingle("\tif\tmatch\t", &.{ .keyword_if, .keyword_match });
    try testSingle("\rif\rmatch\r", &.{.invalid});
}

fn testSemi(source: [:0]const u8, expected: []const lex.Token.Tag) !void {
    var lexer = lex.Tokenizer.init(source, 0, .semi);
    var i: usize = 0;
    while (true) {
        const tok = lexer.next();
        if (tok.tag == .eof) break;
        if (i >= expected.len) {
            std.debug.print("Got extra token: {any}\n", .{tok});
            try testing.expect(false);
            return error.TooManyTokens;
        }
        try testing.expectEqual(expected[i], tok.tag);
        i += 1;
    }
    try testing.expectEqual(expected.len, i);
}

test "ASI: identifiers across newlines" {
    try testSemi("foo\nbar\n", &.{ .identifier, .eos, .identifier, .eos });
}

test "ASI: no insert after infix operator" {
    try testSemi("foo +\nbar\n", &.{ .identifier, .plus, .identifier, .eos });
}

test "ASI: literals and EOF insertion" {
    // newline then EOF
    try testSemi("1\n2", &.{ .integer_literal, .eos, .integer_literal, .eos });
}

test "ASI: closing delimiters cause insert" {
    try testSemi("()\n1\n", &.{ .lparen, .rparen, .eos, .integer_literal, .eos });
    try testSemi("[]\n", &.{ .lsquare, .rsquare, .eos });
    // EOF after }
    try testSemi("{}", &.{ .lcurly, .rcurly, .eos });
}

test "ASI: after line comments (LF and CRLF)" {
    try testSemi("1// cmt\n2\n", &.{ .integer_literal, .eos, .integer_literal, .eos });
    try testSemi("1// cmt\r\n2\r\n", &.{ .integer_literal, .eos, .integer_literal, .eos });
}

test "ASI: control keywords" {
    // bare return then newline
    try testSemi("return\n", &.{ .keyword_return, .eos });
    // return followed by expression then newline
    try testSemi("return 1\n", &.{ .keyword_return, .integer_literal, .eos });
    // newline after return then another stmt
    try testSemi("return\n1\n", &.{ .keyword_return, .eos, .integer_literal, .eos });
}

test "ASI: booleans/null/undefined end statements" {
    try testSemi("true\nfalse\n", &.{ .keyword_true, .eos, .keyword_false, .eos });
    try testSemi("null\nundefined\n", &.{ .keyword_null, .eos, .keyword_undefined, .eos });
}

test "ASI: non-enders like 'if' do not insert" {
    try testSemi("if\nx\n", &.{ .keyword_if, .identifier, .eos });
}

test "ASI: string literal then newline inserts" {
    try testSemi("\"hi\"\nfoo\n", &.{ .string_literal, .eos, .identifier, .eos });
}

test "ASI: eof after comment" {
    try testSemi("// comment\n", &.{});
}

test "block comment" {
    try testSingle(
        \\/* block comment */
        \\fn main() void {}
    , &.{
        .keyword_fn, .identifier, .lparen, .rparen, .identifier, .lcurly, .rcurly,
    });
    try testSingle("/*\x00*/", &.{.invalid});
}

test "asm block" {
    try testSingle(
        \\asm { mov eax, 1 }
    , &.{
        .keyword_asm, .raw_asm_block,
    });
    try testSingle(
        \\asm { mov \\, eax, 1, "sada", 'a' }
    , &.{
        .keyword_asm, .raw_asm_block,
    });
}

test "mlir block" {
    try testSingle(
        \\mlir { func @main() -> i32 { return 0 : i32 } }
    , &.{
        .keyword_mlir,
        .lcurly,
        .identifier,
        .at,
        .identifier,
        .lparen,
        .rparen,
        .rarrow,
        .identifier,
        .lcurly,
        .keyword_return,
        .integer_literal,
        .colon,
        .identifier,
        .rcurly,
        .rcurly,
    });
    // skip escaped
    try testSingle(
        \\mlir { func \@main() -> i32 { return 0 : i32 } }
    , &.{
        .keyword_mlir,
        .lcurly,
        .identifier,
        .invalid,
    });
}

test "mlir attribute" {
    try testSingle(
        \\mlir attribute {foo = "bar"}
    , &.{ .keyword_mlir, .identifier, .lcurly, .identifier, .equal, .string_literal, .rcurly });
}

test "mlir attribute with nested braces" {
    try testSingle(
        \\mlir attribute {foo = {bar = "baz"}}
    , &.{
        .keyword_mlir,
        .identifier,
        .lcurly,
        .identifier,
        .equal,
        .lcurly,
        .identifier,
        .equal,
        .string_literal,
        .rcurly,
        .rcurly,
    });
}

test "mlir type" {
    try testSingle(
        \\mlir type {i32}
    , &.{ .keyword_mlir, .keyword_type, .lcurly, .identifier, .rcurly });
}

test "imaginary literals: integers & floats" {
    try testSingle("1i", &.{.imaginary_literal});
    try testSingle("123i", &.{.imaginary_literal});
    try testSingle("0b101i", &.{.imaginary_literal});
    try testSingle("0o77i", &.{.imaginary_literal});
    try testSingle("0xFFi", &.{.imaginary_literal});

    try testSingle("1.0i", &.{.imaginary_literal});
    try testSingle("0x1.fp3i", &.{.imaginary_literal});
    try testSingle("1e10i", &.{.imaginary_literal});

    // unary minus stays separate
    try testSingle("-1i", &.{ .minus, .imaginary_literal });

    // NOT imaginary: the '.' splits before 'i'
    try testSingle("1.i", &.{ .integer_literal, .dot, .identifier });
}

test "ASI with imaginaries" {
    try testSemi("1i\n2i\n", &.{ .imaginary_literal, .eos, .imaginary_literal, .eos });
}

test "printf call emits closing rparen" {
    try testSingle(
        \\printf(fmt.(*void), r);
    , &.{
        .identifier, .lparen,
        .identifier, .dotlparen, .star, .identifier, .rparen, // closes .dotlparen
        .comma, .identifier, .rparen, .eos, // closes printf(
    });
}

test "/*/*" {
    try testSingle("/*/*", &.{
        .invalid,
    });
}
