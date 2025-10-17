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
  shift: 11,
  additive: 12,
  multiplicative: 13,
  unary: 14,
  call: 15,
  member: 16,
  postfix: 17,
};

module.exports = grammar({
  name: 'sr',

  extras: $ => [
    $.comment,
    /[\s\uFEFF\u2060\u200B]/,
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

    const_declaration: $ => choice(
      seq(
        field('pattern', $.pattern),
        ':',
        field('type', $.type),
        ':',
        field('value', $.expression)
      ),
      seq(
        field('pattern', $.pattern),
        '::',
        field('value', $.expression)
      )
    ),

    var_declaration: $ => choice(
      seq(
        field('pattern', $.pattern),
        ':',
        field('type', $.type),
        '=',
        field('value', $.expression)
      ),
      seq(
        field('pattern', $.pattern),
        ':=',
        field('value', $.expression)
      )
    ),

    pattern: $ => choice(
      $.identifier,
      $.wildcard_pattern,
    ),

    wildcard_pattern: $ => '_',

    statement: $ => choice(
      $.assignment_statement,
      $.return_statement,
      $.expression_statement,
    ),

    assignment_statement: $ => seq(
      field('left', $.expression),
      field('operator', choice(
        '=', '+=', '-=', '*=', '/=', '%=', '<<=', '>>=', '&=', '|=', '^='
      )),
      field('right', $.expression)
    ),

    return_statement: $ => prec.right(seq('return', optional($.expression))),

    expression_statement: $ => $.expression,

    expression: $ => choice(
      $.binary_expression,
      $.unary_expression,
      $.call_expression,
      $.member_expression,
      $.cast_expression,
      $.primary_expression
    ),

    primary_expression: $ => choice(
      $.literal,
      $.identifier,
      $.proc_expression,
      $.parenthesized_expression,
      $.block
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

    proc_expression: $ => choice(
      prec(1, seq(
        repeat(field('modifier', choice('extern', 'async'))),
        'proc',
        field('parameters', $.parameter_list),
        optional(field('return_type', $.type)),
        field('body', $.block)
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
      optional(commaSep($.parameter)),
      ')'
    ),

    parameter: $ => choice(
      seq(
        field('pattern', $.pattern),
        ':',
        field('type', $.type)
      ),
      field('type', $.type)
    ),

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

    cast_expression: $ => prec(PREC.postfix, seq(
      field('value', $.expression),
      token('.^'),
      field('type', $.type)
    )),

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

    integer_literal: $ => token(choice(
      /0[bB][01]([01_])*/,
      /0[oO][0-7]([0-7_])*/,
      /0[xX][0-9a-fA-F]([0-9a-fA-F_])*/,
      /[0-9]([0-9_])*/
    )),

    float_literal: $ => token(/(?:[0-9]([0-9_])*\.[0-9_]+|\.[0-9_]+)(?:[eE][+-]?[0-9]([0-9_])*)?|[0-9]([0-9_])*(?:[eE][+-]?[0-9]([0-9_])*)/),

    string_literal: $ => token(seq('"', repeat(choice(/[^\\"\n]/, /\\./)), '"')),

    char_literal: $ => token(seq('\'', choice(/[^\\'\n]/, /\\./), '\'')),

    boolean_literal: $ => choice('true', 'false'),

    type: $ => choice(
      $.pointer_type,
      $.type_identifier
    ),

    pointer_type: $ => seq('*', field('type', $.type)),

    type_identifier: $ => $.identifier,

    identifier: $ => token(prec(-1, /[_A-Za-z][_A-Za-z0-9]*/)),

    comment: $ => token(choice(
      seq('//', /[^\n]*/),
      /\/\*[^*]*\*+([^/*][^*]*\*+)*\//
    )),
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
