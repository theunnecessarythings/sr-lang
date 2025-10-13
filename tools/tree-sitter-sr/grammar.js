const PREC = {
  assignment: 1,
  or: 2,
  and: 3,
  bitwise_or: 4,
  bitwise_xor: 5,
  bitwise_and: 6,
  equality: 7,
  relational: 8,
  shift: 9,
  additive: 10,
  multiplicative: 11,
  unary: 12,
  call: 13,
  member: 14,
};

module.exports = grammar({
  name: 'sr',

  extras: $ => [
    $.comment,
    /\s/,
  ],

  word: $ => $.identifier,

  supertypes: $ => [
    $.declaration,
    $.statement,
    $.expression,
    $.type,
    $.pattern,
  ],

  inline: $ => [
    $.type_arguments,
    $.parameters,
    $.block,
    $.pattern_list,
  ],

  conflicts: $ => [
    [$.pattern, $.expression],
    [$.struct_literal, $.block_expression],
    [$.match_arm],
  ],

  rules: {
    source_file: $ => repeat($._item),

    _item: $ => choice(
      $.package_declaration,
      $.import_declaration,
      $.declaration,
      $.statement,
    ),

    package_declaration: $ => seq(
      field('keyword', 'package'),
      field('name', $.qualified_identifier),
      ';'
    ),

    import_declaration: $ => seq(
      field('keyword', 'import'),
      field('path', $.import_path),
      optional(seq('as', field('alias', $.identifier))),
      ';'
    ),

    import_path: $ => seq(
      field('root', $.identifier),
      repeat(seq('.', field('segment', $.identifier)))
    ),

    declaration: $ => choice(
      $.function_declaration,
      $.procedure_declaration,
      $.struct_declaration,
      $.enum_declaration,
      $.const_declaration,
      $.variable_declaration,
      $.attribute_declaration,
    ),

    attribute_declaration: $ => seq(
      field('attribute', $.attribute),
      field('target', $.declaration)
    ),

    attribute: $ => seq(
      '#',
      optional('['),
      field('name', $.identifier),
      optional(seq('(', commaSep($.expression), ')')),
      optional(']')
    ),

    function_declaration: $ => seq(
      field('attributes', repeat($.attribute)),
      'fn',
      field('name', $.identifier),
      field('type_parameters', optional($.type_parameters)),
      field('parameters', $.parameters),
      optional(seq('->', field('return_type', $.type))),
      field('body', $.block)
    ),

    procedure_declaration: $ => seq(
      field('attributes', repeat($.attribute)),
      'proc',
      field('name', $.identifier),
      field('parameters', $.parameters),
      field('body', $.block)
    ),

    parameters: $ => seq(
      '(',
      optional(commaSep(field('parameter', $.parameter))),
      ')'
    ),

    parameter: $ => seq(
      optional($.attribute),
      field('pattern', $.pattern),
      optional(seq(':', field('type', $.type)))
    ),

    type_parameters: $ => seq(
      '<',
      commaSep1(field('type_parameter', $.identifier)),
      '>'
    ),

    struct_declaration: $ => seq(
      field('attributes', repeat($.attribute)),
      'struct',
      field('name', $.identifier),
      field('type_parameters', optional($.type_parameters)),
      field('body', $.struct_body)
    ),

    struct_body: $ => seq(
      '{',
      optional(commaSep(field('field', $.struct_field))),
      optional(','),
      '}'
    ),

    struct_field: $ => seq(
      repeat($.attribute),
      field('name', $.identifier),
      ':',
      field('type', $.type)
    ),

    enum_declaration: $ => seq(
      field('attributes', repeat($.attribute)),
      'enum',
      field('name', $.identifier),
      field('type_parameters', optional($.type_parameters)),
      field('body', $.enum_body)
    ),

    enum_body: $ => seq(
      '{',
      optional(commaSep(field('variant', $.enum_variant))),
      optional(','),
      '}'
    ),

    enum_variant: $ => seq(
      repeat($.attribute),
      field('name', $.identifier),
      optional(field('payload', $.variant_payload))
    ),

    variant_payload: $ => choice(
      seq('(', commaSep1($.type), ')'),
      seq('{', optional(commaSep($.struct_field)), optional(','), '}')
    ),

    const_declaration: $ => seq(
      'const',
      field('pattern', $.pattern),
      optional(seq(':', field('type', $.type))),
      '=',
      field('value', $.expression),
      ';'
    ),

    variable_declaration: $ => seq(
      'let',
      field('pattern', $.pattern),
      optional(seq(':', field('type', $.type))),
      optional(seq(':=', field('value', $.expression))),
      ';'
    ),

    statement: $ => choice(
      $.block,
      $.assignment,
      $.expression_statement,
      $.declaration_statement,
      $.return_statement,
      $.break_statement,
      $.continue_statement,
      $.if_statement,
      $.while_statement,
      $.for_statement,
      $.match_statement,
    ),

    block: $ => seq(
      '{',
      repeat($._block_item),
      optional(field('result', $.expression)),
      '}'
    ),

    _block_item: $ => choice(
      $.statement,
      $.declaration,
    ),

    expression_statement: $ => seq(field('expression', $.expression), ';'),

    declaration_statement: $ => seq($.declaration),

    assignment: $ => seq(
      field('left', $.expression),
      choice('=', '+=', '-=', '*=', '/=', '%=', '<<=', '>>=', '&=', '|=', '^='),
      field('right', $.expression),
      ';'
    ),

    return_statement: $ => seq('return', optional($.expression), ';'),

    break_statement: $ => seq('break', optional($.identifier), ';'),

    continue_statement: $ => seq('continue', optional($.identifier), ';'),

    if_statement: $ => seq(
      'if',
      field('condition', $.expression),
      field('consequence', $.block),
      repeat(field('else_if', $.else_if_clause)),
      optional(seq('else', field('alternative', $.block)))
    ),

    else_if_clause: $ => seq('else', 'if', field('condition', $.expression), field('consequence', $.block)),

    while_statement: $ => seq('while', field('condition', $.expression), field('body', $.block)),

    for_statement: $ => seq(
      'for',
      field('pattern', $.pattern),
      'in',
      field('iterator', $.expression),
      field('body', $.block)
    ),

    match_statement: $ => seq('match', field('value', $.expression), field('body', $.match_block)),

    match_block: $ => seq('{', repeat1($.match_arm), '}'),

    match_arm: $ => seq(
      field('pattern', $.pattern),
      optional(seq('if', field('guard', $.expression))),
      '=>',
      field('body', choice($.expression, $.block)),
      optional(',')
    ),

    expression: $ => choice(
      $.literal,
      $.identifier,
      $.qualified_identifier,
      $.parenthesized_expression,
      $.unary_expression,
      $.binary_expression,
      $.call_expression,
      $.member_expression,
      $.index_expression,
      $.if_expression,
      $.match_expression,
      $.block_expression,
      $.async_block,
      $.comptime_block,
      $.struct_literal,
    ),

    parenthesized_expression: $ => seq('(', $.expression, ')'),

    block_expression: $ => $.block,

    async_block: $ => seq('async', $.block),

    comptime_block: $ => seq('comptime', $.block),

    if_expression: $ => seq('if', field('condition', $.expression), field('consequence', $.block), optional(seq('else', field('alternative', choice($.block, $.expression))))),

    match_expression: $ => seq('match', field('value', $.expression), field('body', $.match_block)),

    call_expression: $ => prec(PREC.call, seq(field('function', $.expression), field('arguments', $.arguments))),

    arguments: $ => seq('(', optional(commaSep($.argument)), ')'),

    argument: $ => seq(optional(seq(field('name', $.identifier), ':')), field('value', $.expression)),

    member_expression: $ => prec(PREC.member, seq(field('object', $.expression), '.', field('property', $.identifier))),

    index_expression: $ => prec(PREC.member, seq(field('array', $.expression), '[', field('index', $.expression), ']')),

    unary_expression: $ => prec(PREC.unary, seq(choice('+', '-', '!', '~', '*', '&'), field('argument', $.expression))),

    binary_expression: $ => choice(
      ...[
        ['||', PREC.or],
        ['&&', PREC.and],
        ['|', PREC.bitwise_or],
        ['^', PREC.bitwise_xor],
        ['&', PREC.bitwise_and],
        ['==', PREC.equality],
        ['!=', PREC.equality],
        ['<', PREC.relational],
        ['<=', PREC.relational],
        ['>', PREC.relational],
        ['>=', PREC.relational],
        ['<<', PREC.shift],
        ['>>', PREC.shift],
        ['+', PREC.additive],
        ['-', PREC.additive],
        ['*', PREC.multiplicative],
        ['/', PREC.multiplicative],
        ['%', PREC.multiplicative],
      ].map(([operator, precedence]) => prec.left(precedence, seq(field('left', $.expression), operator, field('right', $.expression))))
    ),

    struct_literal: $ => seq(
      field('type', $.identifier),
      '{',
      optional(commaSep($.struct_literal_field)),
      optional(','),
      '}'
    ),

    struct_literal_field: $ => seq(field('name', $.identifier), ':', field('value', $.expression)),

    literal: $ => choice(
      $.integer_literal,
      $.float_literal,
      $.string_literal,
      $.raw_string_literal,
      $.char_literal,
      $.boolean_literal,
      $.null_literal,
      $.undefined_literal,
    ),

    integer_literal: $ => token(choice(
      /0[bB][01][_01]*/,
      /0[oO][0-7][_0-7]*/,
      /0[xX][0-9a-fA-F][_0-9a-fA-F]*/,
      /[0-9][0-9_]*/
    )),

    float_literal: $ => token(/
      (?:[0-9][0-9_]*\.[0-9_]+|\.[0-9_]+)(?:[eE][+-]?[0-9][0-9_]*)?|
      [0-9][0-9_]*(?:[eE][+-]?[0-9][0-9_]*)
    /),

    string_literal: $ => token(seq('"', repeat(choice(/[^\\"]+/, /\\./)), '"')),

    raw_string_literal: $ => token(seq('r"', repeat(/[^"]+/), '"')),

    char_literal: $ => token(seq('\'', choice(/[^\\\']/, /\\./), '\'')),

    boolean_literal: $ => choice('true', 'false'),

    null_literal: $ => 'null',

    undefined_literal: $ => 'undefined',

    qualified_identifier: $ => seq($.identifier, repeat1(seq('::', $.identifier))),

    identifier: $ => token(prec(-1, /[_A-Za-z][_A-Za-z0-9]*/)),

    comment: $ => token(choice(
      seq('//', /[^\n]*/),
      /\/\*[^*]*\*+([^/*][^*]*\*+)*\//
    )),

    pattern: $ => choice(
      '_',
      $.literal,
      $.identifier,
      $.tuple_pattern,
      $.struct_pattern,
      $.variant_pattern,
    ),

    tuple_pattern: $ => seq('(', optional($.pattern_list), ')'),

    pattern_list: $ => commaSep1($.pattern),

    struct_pattern: $ => seq(
      field('type', $.identifier),
      '{',
      optional(commaSep($.struct_pattern_field)),
      optional(','),
      '}'
    ),

    struct_pattern_field: $ => seq(field('name', $.identifier), optional(seq(':', field('pattern', $.pattern)))),

    variant_pattern: $ => seq(
      field('type', $.identifier),
      '::',
      field('variant', $.identifier),
      optional(choice(
        seq('(', optional($.pattern_list), ')'),
        seq('{', optional(commaSep($.struct_pattern_field)), optional(','), '}')
      ))
    ),

    type: $ => choice(
      $.basic_type,
      $.pointer_type,
      $.array_type,
      $.slice_type,
      $.tuple_type,
      $.qualified_identifier,
      $.identifier,
    ),

    basic_type: $ => choice(
      'i8', 'i16', 'i32', 'i64', 'i128',
      'u8', 'u16', 'u32', 'u64', 'u128',
      'f32', 'f64', 'f128',
      'bool', 'char', 'str', 'void'
    ),

    pointer_type: $ => seq('*', optional(field('qualifier', $.pointer_qualifier)), field('type', $.type)),

    pointer_qualifier: $ => choice('const', 'mut'),

    array_type: $ => seq('[', field('length', $.expression), ';', field('element', $.type), ']'),

    slice_type: $ => seq('[', field('element', $.type), ']'),

    tuple_type: $ => seq('(', commaSep1($.type), ')'),

  }
});

function commaSep(rule) {
  return seq(rule, repeat(seq(',', rule)));
}

function commaSep1(rule) {
  return seq(rule, repeat(seq(',', rule)));
}
