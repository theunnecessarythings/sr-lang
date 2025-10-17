const PREC = {
  assignment: 1,
  or: 2,
  and: 3,
  orelse: 4,
  catch: 5,
  bitwise_or: 6,
  bitwise_xor: 7,
  bitwise_and: 8,
  equality: 9,
  relational: 10,
  range: 11,
  shift: 12,
  additive: 13,
  multiplicative: 14,
  unary: 15,
  call: 16,
  member: 17,
  postfix: 18,
};

const DECIMAL_DIGITS = /[0-9](?:_?[0-9])*/;
const BINARY_DIGITS = /0[bB](?:_?[01])+/;
const OCTAL_DIGITS = /0[oO](?:_?[0-7])+/;
const HEX_DIGITS = /0[xX](?:_?[0-9a-fA-F])+/;
const FLOAT_DECIMAL = /[0-9](?:_?[0-9])*\.[0-9](?:_?[0-9])*(?:[eE][+-]?[0-9](?:_?[0-9])*)?(?:i|f[0-9]{1,3})?/;
const FLOAT_DECIMAL_EXP = /[0-9](?:_?[0-9])*\.(?:[eE][+-]?[0-9](?:_?[0-9])*)(?:i|f[0-9]{1,3})?/;
const FLOAT_DECIMAL_SUFFIX = /[0-9](?:_?[0-9])*\.(?:i|f[0-9]{1,3})/;
const FLOAT_LEADING_DOT = /\.[0-9](?:_?[0-9])*(?:[eE][+-]?[0-9](?:_?[0-9])*)?(?:i|f[0-9]{1,3})?/;
const FLOAT_EXPONENT = /[0-9](?:_?[0-9])*(?:[eE][+-]?[0-9](?:_?[0-9])*)(?:i|f[0-9]{1,3})?/;

module.exports = grammar({
  name: 'sr',

  conflicts: $ => [
    [$.primary_expression, $.type_identifier],
    [$.primary_expression, $.closure_expression],
    [$.primary_expression, $.struct_pattern],
    [$.primary_expression, $.variant_pattern],
    [$.primary_expression, $.struct_pattern, $.variant_pattern],
    [$.struct_pattern, $.variant_pattern, $.type_path],
    [$.primary_expression, $._pattern_without_or],
    [$.primary_expression, $.pattern_range_bound],
    [$.primary_expression, $._pattern_without_or, $.type_identifier],
    [$.primary_expression, $.literal_pattern],
    [$.pattern, $.or_pattern],
    [$.array_expression, $.array_pattern],
    [$.array_expression, $.slice_type],
    [$.array_expression, $.array_type],
    [$.array_expression, $.map_type],
    [$.tuple_expression, $.tuple_pattern],
    [$.struct_pattern_body, $.variant_pattern_fields],
    [$.literal, $.literal_pattern],
    [$.block, $.struct_literal_body],
    [$.struct_literal_body, $.match_expression],
    [$.fn_expression, $.error_union_type],
    [$.proc_expression, $.error_union_type],
    [$.optional_type, $.error_union_type],
    [$.pointer_type, $.error_union_type],
    [$.fn_expression, $.function_type],
    [$.proc_expression, $.procedure_type],
    [$.type, $._pattern_without_or],
    [$.type_identifier, $._pattern_without_or],
    [$.slice_type, $.error_union_type],
    [$.parameter_list, $.type_parameter_list],
    [$._pattern_without_or, $.type_parameter],
    [$.parameter, $.type_parameter],
    [$.type_argument, $.type_identifier],
    [$.dynamic_array_type, $.error_union_type],
    [$.array_type, $.error_union_type],
  ],

  extras: $ => [
    $.comment,
    /[\s\uFEFF\u2060\u200B]/,
  ],

  externals: $ => [
    $.block_comment,
  ],

  word: $ => $.identifier,

  supertypes: $ => [
    $.declaration,
    $.statement,
    $.expression,
    $.type,
    $.pattern,
  ],

  rules: {
    source_file: $ => seq(
      optional($.package_declaration),
      repeat($._item)
    ),

    _item: $ => choice(
      $.declaration,
      $.statement,
    ),

    package_declaration: $ => seq(
      'package',
      field('name', $.path)
    ),

    path: $ => seq(
      field('root', $.identifier),
      repeat(seq('.', field('segment', $.identifier)))
    ),

    declaration: $ => choice(
      $.const_declaration,
      $.var_declaration,
    ),

    declaration_modifier: $ => 'pub',

    attribute: $ => seq(
      '@[',
      optional(commaSep1($.attribute_argument)),
      ']'
    ),

    attribute_argument: $ => seq(
      field('name', $.identifier),
      optional(seq('=', field('value', $.attribute_value)))
    ),

    attribute_value: $ => choice(
      $.identifier,
      $.literal
    ),

    const_declaration: $ => prec.left(1, seq(
      repeat(field('attribute', $.attribute)),
      repeat(field('modifier', $.declaration_modifier)),
      field('pattern', $.pattern),
      choice(
        seq(
          ':',
          field('type', $.type),
          ':',
          field('value', $.expression)
        ),
        seq(
          '::',
          repeat(field('value_attribute', $.attribute)),
          field('value', choice($.type, $.expression))
        )
      )
    )),

    var_declaration: $ => prec.left(1, seq(
      repeat(field('attribute', $.attribute)),
      repeat(field('modifier', $.declaration_modifier)),
      field('pattern', $.pattern),
      choice(
        seq(
          ':',
          field('type', $.type),
          '=',
          field('value', $.expression)
        ),
        seq(
          ':=',
          field('value', $.expression)
        )
      )
    )),

    pattern: $ => choice(
      $.or_pattern,
      $._pattern_without_or
    ),

    _pattern_without_or: $ => choice(
      $.binding_pattern,
      $.range_pattern,
      $.variant_pattern,
      $.struct_pattern,
      $.tuple_pattern,
      $.array_pattern,
      $.literal_pattern,
      $.identifier,
      $.wildcard_pattern
    ),

    wildcard_pattern: $ => '_',

    literal_pattern: $ => choice(
      alias($.integer_literal, $.literal_pattern),
      alias($.float_literal, $.literal_pattern),
      alias($.string_literal, $.literal_pattern),
      alias($.char_literal, $.literal_pattern),
      alias($.boolean_literal, $.literal_pattern)
    ),

    binding_pattern: $ => seq(
      field('name', $.identifier),
      '@',
      field('pattern', $.pattern)
    ),

    or_pattern: $ => prec.left(seq(
      $._pattern_without_or,
      '|',
      $._pattern_without_or,
      repeat(seq('|', $._pattern_without_or))
    )),

    range_pattern: $ => seq(
      field('start', $.pattern_range_bound),
      field('operator', choice('..', '..=')),
      field('end', $.pattern_range_bound)
    ),

    pattern_range_bound: $ => choice(
      $.literal_pattern,
      $.identifier
    ),

    tuple_pattern: $ => seq(
      '(',
      optional(commaSep1($.pattern)),
      ')'
    ),

    array_pattern: $ => seq(
      '[',
      optional(commaSep1($.array_pattern_element)),
      ']'
    ),

    array_pattern_element: $ => choice(
      $.pattern,
      $.rest_pattern
    ),

    rest_pattern: $ => seq('..', optional(field('name', $.identifier))),

    struct_pattern: $ => seq(
      field('type', $.identifier),
      repeat(seq('.', field('name', $.identifier))),
      field('body', $.struct_pattern_body)
    ),

    struct_pattern_body: $ => seq(
      '{',
      optional(commaSep1(choice($.struct_pattern_field, $.rest_pattern))),
      '}'
    ),

    struct_pattern_field: $ => choice(
      seq(
        field('name', $.identifier),
        ':',
        field('value', $.pattern)
      ),
      field('shorthand', $.identifier)
    ),

    variant_pattern: $ => seq(
      field('constructor', $.identifier),
      repeat1(seq('.', field('name', $.identifier))),
      optional(choice(
        field('arguments', $.variant_pattern_arguments),
        field('fields', $.variant_pattern_fields)
      ))
    ),

    variant_pattern_arguments: $ => seq(
      '(',
      optional(commaSep1($.pattern)),
      ')'
    ),

    variant_pattern_fields: $ => seq(
      '{',
      optional(commaSep1(choice($.struct_pattern_field, $.rest_pattern))),
      '}'
    ),


    statement: $ => choice(
      $.assignment_statement,
      $.return_statement,
      $.break_statement,
      $.continue_statement,
      $.defer_statement,
      $.errdefer_statement,
      $.insert_statement,
      $.expression_statement,
    ),

    loop_label: $ => prec(1, seq(field('label', $.identifier), ':')),

    mlir_expression: $ => seq(
      'mlir',
      optional(field('kind', $.identifier)),
      field('body', $.mlir_body)
    ),

    asm_block: $ => seq(
      'asm',
      field('body', $.block)
    ),

    mlir_body: $ => seq(
      '{',
      repeat(choice(
        $.mlir_body,
        $.mlir_text
      )),
      '}'
    ),

    mlir_text: $ => token(/[^{}]+/),

    assignment_statement: $ => seq(
      field('left', $.expression),
      field('operator', choice(
        '=', '+=', '-=', '*=', '/=', '%=', '<<=', '>>=', '&=', '|=', '^='
      )),
      field('right', $.expression)
    ),

    return_statement: $ => prec.right(seq('return', optional($.expression))),

    break_statement: $ => choice(
      prec.left(1, seq('break', ':', field('label', $.identifier), field('value', $._break_value))),
      seq('break', ':', field('label', $.identifier)),
      prec.left(-1, seq('break', field('value', $._break_value))),
      'break'
    ),

    _break_value: $ => choice(
      $.literal,
      alias($._identifier_no_mlir, $.identifier)
    ),

    continue_statement: $ => seq(
      'continue',
      optional(seq(':', field('label', $.identifier)))
    ),

    defer_statement: $ => prec(1, seq('defer', field('handler', choice($.block, $.expression)))),

    errdefer_statement: $ => prec(1, seq('errdefer', field('handler', choice($.block, $.expression)))),

    insert_statement: $ => seq('insert', field('value', $.expression)),

    expression_statement: $ => $.expression,

    expression: $ => choice(
      $.binary_expression,
      $.unary_expression,
      $.call_expression,
      $.member_expression,
      $.index_expression,
      $.cast_expression,
      $.error_propagation_expression,
      $.optional_unwrap_expression,
      $.pointer_dereference_expression,
      $.struct_literal,
      $.import_expression,
      $.if_expression,
      $.while_expression,
      $.for_expression,
      $.match_expression,
      $.comptime_expression,
      $.code_expression,
      $.mlir_expression,
      $.primary_expression
    ),

    primary_expression: $ => choice(
      $.literal,
      $.identifier,
      $.fn_expression,
      $.proc_expression,
      $.closure_expression,
      $.async_expression,
      $.tuple_expression,
      $.array_expression,
      $.parenthesized_expression,
      $.block
    ),

    tuple_expression: $ => seq(
      '(',
      field('first', $.expression),
      ',',
      optional(commaSep($.expression)),
      optional(','),
      ')'
    ),

    parenthesized_expression: $ => seq('(', $.expression, ')'),

    block: $ => seq(
      '{',
      repeat($._block_item),
      '}'
    ),

    _block_item: $ => choice(
      $.declaration,
      $.statement
    ),

    fn_expression: $ => choice(
      prec(1, seq(
        repeat(field('modifier', choice('extern', 'async'))),
        'fn',
        field('parameters', $.parameter_list),
        optional(field('return_type', $.type)),
        field('body', choice($.block, $.asm_block))
      )),
      seq(
        repeat(field('modifier', choice('extern', 'async'))),
        'fn',
        field('parameters', $.parameter_list),
        optional(field('return_type', $.type))
      )
    ),

    proc_expression: $ => choice(
      prec(1, seq(
        repeat(field('modifier', choice('extern', 'async'))),
        'proc',
        field('parameters', $.parameter_list),
        optional(field('return_type', $.type)),
        field('body', choice($.block, $.asm_block))
      )),
      seq(
        repeat(field('modifier', choice('extern', 'async'))),
        'proc',
        field('parameters', $.parameter_list),
        optional(field('return_type', $.type))
      )
    ),

    parameter_list: $ => seq(
      '(',
      optional(commaSep1($.parameter)),
      ')'
    ),

    parameter_modifier: $ => 'comptime',

    parameter: $ => choice(
      seq(
        repeat(field('attribute', $.attribute)),
        repeat(field('modifier', $.parameter_modifier)),
        field('pattern', $.pattern),
        ':',
        field('type', $.type),
        optional(seq('=', field('default_value', $.expression)))
      ),
      seq(
        repeat(field('attribute', $.attribute)),
        repeat(field('modifier', $.parameter_modifier)),
        field('type', $.type),
        optional(seq('=', field('default_value', $.expression)))
      )
    ),

    closure_expression: $ => seq(
      field('parameters', $.closure_parameters),
      choice(
        seq(
          optional(field('return_type', $.type)),
          field('body', $.block)
        ),
        field('body', $.expression)
      )
    ),

    closure_parameters: $ => seq(
      '|',
      optional(commaSep1($.closure_parameter)),
      '|'
    ),

    closure_parameter: $ => seq(
      field('pattern', $.pattern),
      optional(seq(':', field('type', $.type)))
    ),

    async_expression: $ => seq('async', field('body', $.block)),

    import_expression: $ => prec(PREC.postfix, seq(
      'import',
      field('path', choice($.string_literal, $.identifier))
    )),

    call_expression: $ => prec(PREC.call, seq(
      field('function', $.expression),
      field('arguments', $.argument_list)
    )),

    argument_list: $ => seq(
      '(',
      optional(commaSep($.expression)),
      ')'
    ),

    member_expression: $ => prec(PREC.member, seq(
      field('object', $.expression),
      '.',
      field('property', choice($.identifier, $.integer_literal))
    )),

    index_expression: $ => prec(PREC.postfix, seq(
      field('array', $.expression),
      '[',
      optional(commaSep($.expression)),
      ']'
    )),

    cast_expression: $ => prec(PREC.postfix, seq(
      field('value', $.expression),
      '.',
      choice(
        seq('(', field('type', $.type), ')'),
        seq('^', field('type', $.type)),
        seq('|', field('type', $.type)),
        seq('%', field('type', $.type)),
        seq('?', field('type', $.type))
      )
    )),

    pointer_dereference_expression: $ => prec(PREC.postfix, seq(
      field('value', $.expression),
      '.',
      '*'
    )),

    error_propagation_expression: $ => prec(PREC.postfix, seq(
      field('value', $.expression),
      '!'
    )),

    optional_unwrap_expression: $ => prec(PREC.postfix, seq(
      field('value', $.expression),
      '?'
    )),

    struct_literal: $ => prec(PREC.postfix, seq(
      field('type', $.expression),
      field('body', $.struct_literal_body)
    )),

    struct_literal_body: $ => seq(
      '{',
      optional(commaSep1(choice($.struct_literal_field, $.struct_literal_spread))),
      '}'
    ),

    struct_literal_field: $ => seq(
      field('name', $.identifier),
      ':',
      field('value', $.expression)
    ),

    struct_literal_spread: $ => seq('..', field('value', $.expression)),

    if_expression: $ => prec.right(seq(
      'if',
      field('condition', $.expression),
      field('consequence', $.block),
      optional(seq('else', field('alternative', choice($.block, $.if_expression))))
    )),

    while_expression: $ => prec.right(seq(
      optional($.loop_label),
      'while',
      field('condition', choice(
        $.expression,
        seq(
          'is',
          field('pattern', $.pattern),
          ':=',
          field('value', $.expression)
        )
      )),
      field('body', $.block)
    )),

    for_expression: $ => prec.right(seq(
      optional($.loop_label),
      'for',
      field('pattern', $.pattern),
      'in',
      field('iterable', $.expression),
      field('body', $.block)
    )),

    match_expression: $ => seq(
      'match',
      field('value', $.expression),
      '{',
      optional(commaSep1($.match_arm)),
      '}'
    ),

    match_arm: $ => prec.right(1, seq(
      field('pattern', $.pattern),
      '=>',
      field('body', choice($.block, $.expression))
    )),

    comptime_expression: $ => prec.right(1, seq(
      'comptime',
      field('body', choice($.block, $.expression))
    )),

    code_expression: $ => prec(1, seq('code', field('body', $.block))),

    unary_expression: $ => prec(PREC.unary, seq(
      field('operator', choice('+', '-', '!', '&', '*')),
      field('argument', $.expression)
    )),

    binary_expression: $ => choice(
      ...binaryExpression($, ['or'], PREC.or),
      ...binaryExpression($, ['and'], PREC.and),
      ...binaryExpression($, ['orelse'], PREC.orelse),
      ...binaryExpression($, ['catch'], PREC.catch),
      ...binaryExpression($, ['|'], PREC.bitwise_or),
      ...binaryExpression($, ['^'], PREC.bitwise_xor),
      ...binaryExpression($, ['&'], PREC.bitwise_and),
      ...binaryExpression($, ['==', '!='], PREC.equality),
      ...binaryExpression($, ['<', '<=', '>', '>='], PREC.relational),
      ...binaryExpression($, ['..', '..='], PREC.range),
      ...binaryExpression($, ['<<', '>>'], PREC.shift),
      ...binaryExpression($, ['+', '-'], PREC.additive),
      ...binaryExpression($, ['*', '/', '%'], PREC.multiplicative)
    ),

    literal: $ => choice(
      $.integer_literal,
      $.float_literal,
      $.string_literal,
      $.char_literal,
      $.boolean_literal,
    ),

    array_expression: $ => seq(
      '[',
      optional(commaSep1(choice($.expression, $.map_entry))),
      ']'
    ),

    map_entry: $ => seq(
      field('key', $.expression),
      ':',
      field('value', $.expression)
    ),

    integer_literal: $ => token(choice(
      BINARY_DIGITS,
      OCTAL_DIGITS,
      HEX_DIGITS,
      DECIMAL_DIGITS
    )),

    float_literal: $ => token(prec(1, choice(
      FLOAT_DECIMAL,
      FLOAT_DECIMAL_EXP,
      FLOAT_DECIMAL_SUFFIX,
      FLOAT_LEADING_DOT,
      FLOAT_EXPONENT
    ))),

    string_literal: $ => token(choice(
      seq('"', repeat(choice(/[^\\"\n]/, /\\./)), '"'),
      seq('b"', repeat(choice(/[^\\"\n]/, /\\./)), '"'),
      seq('r"', repeat(/[^"]/), '"'),
      seq('br"', repeat(/[^"]/), '"'),
      seq('r#"', repeat(choice(/[^"]/, seq('"', /[^#]/))), '"#'),
      seq('br#"', repeat(choice(/[^"]/, seq('"', /[^#]/))), '"#')
    )),

    char_literal: $ => token(seq(optional('b'), '\'', choice(/[^\\'\n]/, /\\./), '\'')),

    boolean_literal: $ => choice('true', 'false'),

    type: $ => choice(
      $.pointer_type,
      $.optional_type,
      $.error_union_type,
      $.map_type,
      $.slice_type,
      $.dynamic_array_type,
      $.array_type,
      $.tuple_type,
      $.function_type,
      $.procedure_type,
      $.struct_type,
      $.union_type,
      $.enum_type,
      $.variant_type,
      $.error_type,
      $.type_call,
      $.parenthesized_type,
      $.type_identifier
    ),

    struct_type: $ => seq(
      'struct',
      field('body', $.struct_body)
    ),

    struct_body: $ => seq(
      '{',
      optional(commaSep1($.struct_field)),
      '}'
    ),

    struct_field: $ => seq(
      repeat(field('attribute', $.attribute)),
      optional(field('modifier', $.declaration_modifier)),
      field('name', $.identifier),
      ':',
      field('type', $.type)
    ),

    union_type: $ => seq(
      'union',
      field('body', $.union_body)
    ),

    union_body: $ => seq(
      '{',
      optional(commaSep1($.union_field)),
      '}'
    ),

    union_field: $ => seq(
      repeat(field('attribute', $.attribute)),
      field('name', $.identifier),
      ':',
      field('type', $.type)
    ),

    enum_type: $ => seq(
      'enum',
      optional(seq('(', field('base_type', $.type), ')')),
      field('body', $.enum_body)
    ),

    enum_body: $ => seq(
      '{',
      optional(commaSep1($.enum_variant)),
      '}'
    ),

    enum_variant: $ => seq(
      repeat(field('attribute', $.attribute)),
      field('name', $.identifier),
      optional(seq('=', field('value', $.expression)))
    ),

    variant_type: $ => seq(
      'variant',
      field('body', $.variant_body)
    ),

    variant_body: $ => seq(
      '{',
      optional(commaSep1($.variant_case)),
      '}'
    ),

    variant_case: $ => seq(
      repeat(field('attribute', $.attribute)),
      field('name', $.identifier),
      optional(field('payload', $.variant_payload))
    ),

    variant_payload: $ => choice(
      seq('(', optional(commaSep1($.type)), ')'),
      seq('{', optional(commaSep1($.struct_field)), '}')
    ),

    map_type: $ => seq(
      '[',
      field('key', $.type_identifier),
      token.immediate(':'),
      field('value', $.type),
      ']'
    ),

    slice_type: $ => seq('[', ']', field('element', $.type)),

    dynamic_array_type: $ => seq('[', 'dyn', ']', field('element', $.type)),

    array_type: $ => seq(
      '[',
      field('length', $.expression),
      ']',
      field('element', $.type)
    ),

    tuple_type: $ => seq(
      '(',
      field('first', $.type),
      ',',
      optional(commaSep($.type)),
      optional(','),
      ')'
    ),

    optional_type: $ => seq('?', field('type', $.type)),

    error_union_type: $ => prec.left(seq(
      field('left', $.type),
      '!',
      field('right', $.type)
    )),

    pointer_type: $ => seq(
      '*',
      repeat(field('qualifier', $.pointer_qualifier)),
      field('type', $.type)
    ),

    pointer_qualifier: $ => 'const',

    function_type: $ => prec.right(seq(
      'fn',
      field('parameters', $.type_parameter_list),
      optional(field('return_type', $.type))
    )),

    procedure_type: $ => prec.right(seq(
      'proc',
      field('parameters', $.type_parameter_list),
      optional(field('return_type', $.type))
    )),

    type_parameter_list: $ => seq(
      '(',
      optional(commaSep1($.type_parameter)),
      ')'
    ),

    type_parameter: $ => choice(
      seq(field('name', $.identifier), ':', field('type', $.type)),
      field('type', $.type)
    ),

    error_type: $ => seq(
      'error',
      '{',
      optional(commaSep1(field('name', $.identifier))),
      '}'
    ),

    type_call: $ => prec(PREC.call, seq(
      field('function', $.type_identifier),
      '(',
      optional(commaSep1($.type_argument)),
      ')'
    )),

    type_argument: $ => choice(
      $.type,
      $.literal,
      $.identifier
    ),

    parenthesized_type: $ => seq('(', $.type, ')'),

    type_identifier: $ => choice(
      $.type_path,
      $.identifier
    ),

    type_path: $ => prec(1, seq(
      field('root', $.identifier),
      repeat1(seq('.', field('segment', $.identifier)))
    )),

    _identifier_no_mlir: $ => token(prec(-1, /(?:(?:[A-LN-Z]|[a-ln-z]|_)[A-Za-z0-9_]*|m|m(?:[A-KM-Z]|[a-km-z]|[0-9_])[A-Za-z0-9_]*|ml|ml(?:[A-Z]|[a-hj-z]|[0-9_])[A-Za-z0-9_]*|mli|mli(?:[A-Z]|[a-qst-z]|[0-9_])[A-Za-z0-9_]*|mlir[A-Za-z0-9_]+)/)),

    identifier: $ => token(prec(-1, /[_A-Za-z][_A-Za-z0-9]*/)),

    comment: $ => choice(
      $.line_comment,
      $.block_comment
    ),

    line_comment: $ => token(seq('//', /[^\n]*/)),
  }
});

function binaryExpression($, operators, precedence) {
  return operators.map(operator =>
    prec.left(precedence, seq(field('left', $.expression), operator, field('right', $.expression)))
  );
}

function commaSep(rule) {
  return seq(rule, repeat(seq(',', rule)));
}

function commaSep1(rule) {
  return seq(rule, repeat(seq(',', rule)), optional(','));
}
