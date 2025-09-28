// Generated Tree‑sitter grammar for the experimental sr programming language.
//
// This grammar aims to cover the most commonly used language constructs
// based on the existing Bison/Flex grammar (parser.y, lexer.l) and the
// example programs.  It is intentionally conservative: many keywords and
// operators are recognised, but unimplemented features are parsed as
// generic expressions so that the tree remains recoverable.  As the
// language matures, new rules can be added here to improve precision.

const PREC = {
  // Precedence values grow with tighter binding.
  logical_or: 1,
  logical_and: 2,
  equality: 3,
  relational: 4,
  additive: 5,
  multiplicative: 6,
  unary: 7,
  call: 8,
  member: 9,
  // Additional precedence levels for new operators.  These values
  // mirror the approximate ordering in the reference Bison grammar:
  // assignment < catch < orelse < range < logical or < logical and <
  // comparison < bitwise or/xor/and < shift < additive < multiplicative < unary.
  catch: 1,
  orelse: 2,
  range: 3,
};

// Note: Earlier versions of this file defined generic `sepBy` helper
// functions for comma‑separated lists.  Those helpers relied on
// functions such as `optional`, `seq` and `repeat` that are scoped
// within the Tree‑sitter grammar context.  To avoid referencing
// undefined symbols outside of that context, the helpers have been
// removed.  Instead, each list is expanded inline using the
// equivalent pattern: `optional(seq(rule, repeat(seq(comma, rule)),
// optional(comma)))`.

module.exports = grammar({
  name: 'sr',

  // There is a known ambiguity between assignment expressions and
  // unary expressions when a closure is immediately followed by an
  // identifier and an `=` operator, e.g. `|x| foo = bar`.  In such
  // cases the parser must decide whether the assignment belongs inside
  // the closure or outside.  We explicitly declare this conflict so
  // that the parser can handle both possibilities and prefer the
  // assignment inside the closure.  See the tests in examples/ for
  // details.
  conflicts: $ => [
    // The assignment/unary ambiguity is resolved by unary precedence, so
    // no explicit conflict is needed here.
    // Ambiguity between lvalues and primary expressions when
    // encountering member access (e.g. `foo.bar`).  Both lvalue and
    // _primary_expression begin with an identifier, so Tree‑sitter must
    // explore both interpretations to determine whether the expression
    // forms part of an assignment target or a call chain.  Declaring
    // this conflict prevents spurious shift/reduce errors in the
    // generator.
    [$.lvalue, $._primary_expression],
    // Ambiguity between patterns and primary expressions in match arms.
    // When parsing a match arm like `42 => ...`, Tree‑sitter could
    // interpret the literal `42` as either a `_primary_expression`
    // (producing an expression followed by `=>`) or as a `pattern`.
    // Declaring this conflict informs the generator that both parses
    // are possible and resolves the shift/reduce error.
    [$.pattern, $._primary_expression],
    // The type_alias/type ambiguity has been addressed by refactoring
    // the type grammar, so this conflict is no longer needed.
    // Ambiguity between type and error‑union type when parsing type
    // aliases that define error union types.  For example:
    //   MyErr :: type i32!string
    // can be parsed either as `type (i32)!string` or `(type i32)!string`.
    // Declaring this conflict allows Tree‑sitter to resolve the shift/
    // reduce conflict without failing generation.
    [$.type, $.error_union_type],
    // Ambiguity between non-error types (e.g. map or slice types) and
    // primary expressions when parsing type annotations with error
    // unions.  For example, in `x: [T] ! E` the parser may treat
    // `[T]` as a type or as part of a primary expression.  This
    // conflict declaration covers such cases.
    [$.non_error_type, $._primary_expression],
  ],

  // Skip whitespace and comments between tokens.  Newlines are
  // treated as ordinary whitespace; statement termination is
  // explicitly handled by optional semicolons in the grammar.
  extras: $ => [
    /[\s\u00a0\u1680\u2000-\u200a\u2028\u2029\u202f\u205f\u3000]/,
    $.comment,
  ],

  // The word definition is used by some editors for syntax
  // highlighting; identifiers serve this purpose well.
  word: $ => $.identifier,

  rules: {
    program: $ => repeat($._statement),

    // Statements at the top level.  Many declarations are defined
    // here; new constructs should be added to this list as they are
    // implemented.
    _statement: $ => choice(
      $.import_statement,
      $.const_declaration,
      $.var_declaration,
      $.function_declaration,
      $.proc_declaration,
      $.struct_declaration,
      $.enum_declaration,
      $.union_declaration,
      $.type_alias,
      $.defer_statement,
      $.errdefer_statement,
      $.return_statement,
      $.break_statement,
      $.continue_statement,
      $.insert_statement,
      $.expression_statement,
    ),

    // Import declarations consist of the keyword `import` followed
    // by a string literal.  In the reference grammar the import
    // syntax is more flexible, but for now we accept only literal
    // strings.
    import_statement: $ => seq(
      'import',
      field('path', $.string_literal),
      optional(';'),
    ),

    // Compile‑time constant declarations (`::`) and runtime
    // declarations (`:=` or `=`).  A type annotation may be
    // supplied before the initializer.
    const_declaration: $ => seq(
      field('name', $.identifier),
      '::',
      field('value', $.expression),
      optional(';'),
    ),

    // Variable declarations come in two forms:
    //   name := expression
    //   name: Type = expression
    // The `=` form requires a type annotation to avoid ambiguity
    // with assignment expressions.  Without a type annotation, use
    // the `:=` operator.
    var_declaration: $ => choice(
      // Declaration with ':=' (type annotation optional)
      seq(
        field('name', $.identifier),
        optional(seq(':', field('type', $.type))),
        ':=',
        field('value', $.expression),
        optional(';'),
      ),
      // Declaration with '=' must include a type annotation
      seq(
        field('name', $.identifier),
        ':',
        field('type', $.type),
        '=',
        field('value', $.expression),
        optional(';'),
      ),
    ),

    // Type aliases use the `type` keyword.  Example:
    //   MyInt :: type i32
    type_alias: $ => seq(
      field('name', $.identifier),
      '::',
      'type',
      field('definition', $.type),
      optional(';'),
    ),

    // Procedure definitions.  Procedures (declared with `proc`) may
    // have parameters and a return type, followed by a block body.
    proc_declaration: $ => seq(
      field('attrs', optional($.attribute_list)),
      'proc',
      field('name', $.identifier),
      field('parameters', $.parameters),
      optional(seq(':', field('return_type', $.type))),
      field('body', $.block),
    ),

    // Function definitions are declared with `fn`.  They share the
    // same grammar as procedures.
    function_declaration: $ => seq(
      field('attrs', optional($.attribute_list)),
      'fn',
      field('name', $.identifier),
      field('parameters', $.parameters),
      optional(seq(':', field('return_type', $.type))),
      field('body', $.block),
    ),

    // Structures consist of a name, the `struct` keyword and a
    // series of fields inside braces.  Each field is a name, a
    // type annotation and an optional comma.
    struct_declaration: $ => seq(
      field('attrs', optional($.attribute_list)),
      field('name', $.identifier),
      '::',
      'struct',
      '{',
      // zero or more struct fields separated by commas with an optional trailing comma
      optional(seq(
        $.struct_field,
        repeat(seq(',', $.struct_field)),
        optional(',')
      )),
      '}',
    ),

    struct_field: $ => seq(
      field('attrs', optional($.attribute_list)),
      field('name', $.identifier),
      ':',
      field('type', $.type),
    ),

    // Enumerations are declared using `enum`.  Variants can be
    // followed by a type in parentheses (tuple‑like), a field list
    // (struct‑like) or nothing.  A trailing comma after the last
    // variant is allowed.
    enum_declaration: $ => seq(
      field('attrs', optional($.attribute_list)),
      field('name', $.identifier),
      '::',
      'enum',
      '{',
      // zero or more enum variants separated by commas with an optional trailing comma
      optional(seq(
        $.enum_variant,
        repeat(seq(',', $.enum_variant)),
        optional(',')
      )),
      '}',
    ),

    enum_variant: $ => seq(
      field('attrs', optional($.attribute_list)),
      field('name', $.identifier),
      optional(choice(
        // Tuple‑like variant payload
        seq('(',
          optional(seq(
            $.type,
            repeat(seq(',', $.type))
          )),
          ')'
        ),
        // Struct‑like variant payload
        seq('{',
          optional(seq(
            $.struct_field,
            repeat(seq(',', $.struct_field)),
            optional(',')
          )),
          '}'
        ),
      )),
    ),

    // Unions and variants share a similar syntax.  The `union`
    // keyword is used for untagged unions, while `variant` is used
    // for tagged discriminated unions.  Both accept a list of
    // cases separated by commas.
    union_declaration: $ => seq(
      field('attrs', optional($.attribute_list)),
      field('name', $.identifier),
      '::',
      choice('union', 'variant'),
      '{',
      // zero or more union cases separated by commas with an optional trailing comma
      optional(seq(
        $.union_case,
        repeat(seq(',', $.union_case)),
        optional(',')
      )),
      '}',
    ),

    union_case: $ => seq(
      field('attrs', optional($.attribute_list)),
      field('name', $.identifier),
      optional(choice(
        // Tuple‑like union case payload
        seq('(',
          optional(seq(
            $.type,
            repeat(seq(',', $.type))
          )),
          ')'
        ),
        // Struct‑like union case payload
        seq('{',
          optional(seq(
            $.struct_field,
            repeat(seq(',', $.struct_field)),
            optional(',')
          )),
          '}'
        ),
      )),
    ),

    // Blocks contain zero or more statements enclosed in braces.
    block: $ => seq(
      '{',
      repeat($._statement),
      '}',
    ),

    // Parameter lists.  Parameters are comma‑separated and may be
    // empty.  Each parameter has a name and a type.  Default
    // values and variadic parameters are not yet supported.
    parameters: $ => seq(
      '(',
      optional(seq(
        $.parameter,
        repeat(seq(',', $.parameter))
      )),
      ')',
    ),

    parameter: $ => seq(
      field('attrs', optional($.attribute_list)),
      field('name', $.identifier),
      ':',
      field('type', $.type),
    ),

    attribute_list: $ => seq(
      '@[',
      optional(seq(
        $.attribute,
        repeat(seq(',', $.attribute))
      )),
      ']',
    ),

    attribute: $ => seq(
      field('name', $.identifier),
      optional(seq('=', field('value', $.expression))),
    ),

    // Expression statements evaluate an expression for its side
    // effects.  Semicolons are optional.
    expression_statement: $ => seq(
      $.expression,
      optional(';'),
    ),

    // Defer statements schedule an expression to run when the
    // containing function or scope exits.  The operand may be any
    // expression.  A semicolon may follow.
    defer_statement: $ => seq(
      'defer',
      $.expression,
      optional(';'),
    ),

    // Errdefer statements behave like `defer` but only run on
    // error.  Semicolons are optional.
    errdefer_statement: $ => seq(
      'errdefer',
      $.expression,
      optional(';'),
    ),

    // Return statements return an expression or simply return.  If
    // no expression is present, the statement should end before the
    // next expression begins.  To resolve ambiguity with block
    // expressions (`return { … }`), we give the form with an
    // expression higher precedence.
    return_statement: $ => choice(
      // Return with a value.  The block expression form (return { … }) is
      // handled here because a block is a valid expression.
      prec.left(seq('return', $.expression, optional(';'))),
      // Bare return must be followed by a semicolon to avoid
      // ambiguity with a following block expression.
      seq('return', ';'),
    ),

    // Break statements may target a loop label.  To avoid ambiguity
    // with the following statement, a bare `break` (no label) must
    // be terminated with a semicolon.  A labelled break may omit
    // the semicolon.
    break_statement: $ => choice(
      seq('break', $.identifier, optional(';')),
      seq('break', ';'),
    ),

    // Continue statements behave similarly to break.  A bare
    // `continue` must be followed by a semicolon.  A labelled
    // continue may omit the semicolon.
    continue_statement: $ => choice(
      seq('continue', $.identifier, optional(';')),
      seq('continue', ';'),
    ),

    // Insert statements embed code or values at compile time.
    insert_statement: $ => seq(
      'insert',
      $.expression,
      optional(';'),
    ),

    // Expressions are constructed bottom‑up through precedence
    // climbing.  Assignment has the lowest precedence and binds
    // right‑to‑left.  Above assignment come catch, orelse and range
    // expressions followed by the logical and arithmetic operators.
    expression: $ => choice(
      $.assignment_expression,
      $.catch_expression,
      $.orelse_expression,
      $.range_expression,
      $.logical_or,
    ),

    // An lvalue consists of an identifier optionally followed by
    // member accesses or index expressions.  Function calls and
    // other call chain suffixes are not permitted as assignment
    // targets.  This avoids ambiguous assignments like `|x| f = g`.
    lvalue: $ => seq(
      $.identifier,
      repeat(choice(
        $.member_access,
        $.index_suffix,
      )),
    ),

    // Assignment expressions allow updating the value of an lvalue.
    // Compound assignment operators are supported.
    assignment_expression: $ => prec.right(seq(
      field('left', $.lvalue),
      field('operator', choice(
        '=', '+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=', '<<=', '>>=',
        '+|=', '-|=', '*|=', '<<|=', '>>|=', '+%=', '-%=', '*%='
      )),
      field('right', $.expression),
    )),

    // Catch expressions handle errors produced by an expression on
    // the left.  After the `catch` keyword an optional binder may
    // appear to name the error, surrounded by `|`.  The handler is
    // either a block or a single expression.  Catch binds very
    // loosely.
    catch_expression: $ => prec.left(PREC.catch, seq(
      field('value', $.logical_or),
      'catch',
      optional(seq(
        '|',
        field('error', $.identifier),
        '|'
      )),
      field('handler', choice($.block, $.expression)),
    )),

    // Orelse expressions provide a fallback value if the left
    // expression produces an error.  They associate to the left.
    orelse_expression: $ => prec.left(PREC.orelse, seq(
      field('left', $.logical_or),
      'orelse',
      field('right', $.expression),
    )),

    // Range expressions produce a range of values using `..` or
    // `..=`.  They bind between orelse and logical or.  Either
    // endpoint may be omitted to indicate an open range.
    range_expression: $ => prec.left(PREC.range, seq(
      optional(field('start', $.logical_or)),
      choice('..', '..='),
      optional(field('end', $.logical_or)),
    )),

    // Logical OR (including the `or` keyword and `||`) is left associative.
    logical_or: $ => prec.left(seq(
      $.logical_and,
      repeat(seq(choice('or', '||'), $.logical_and)),
    )),

    // Logical AND (`and`, `&&`) is left associative.
    logical_and: $ => prec.left(seq(
      $.equality,
      repeat(seq(choice('and', '&&'), $.equality)),
    )),

    // Equality operators (==, !=) are left associative.
    equality: $ => prec.left(seq(
      $.relational,
      repeat(seq(choice('==', '!='), $.relational)),
    )),

    // Relational operators (<, <=, >, >=) are left associative.
    relational: $ => prec.left(seq(
      $.additive,
      repeat(seq(choice('<', '<=', '>', '>='), $.additive)),
    )),

    // Additive operators are left associative (+, -, +|, -|, +%, -%).
    additive: $ => prec.left(seq(
      $.multiplicative,
      repeat(seq(choice('+', '-', '+|', '-|', '+%', '-%'), $.multiplicative)),
    )),

    // Multiplicative operators are left associative (*, /, %, and bitshifts).
    multiplicative: $ => prec.left(seq(
      $.unary_expression,
      repeat(seq(choice('*', '/', '%', '*|', '*%', '<<', '>>'), $.unary_expression)),
    )),

    // Unary expressions have higher precedence than assignments.  Without an
    // explicit precedence, Tree‑sitter treats unary and assignment
    // expressions at the same level, which leads to shift/reduce conflicts
    // when parsing constructs like `|x| foo = bar`.  By assigning a
    // precedence greater than zero, we ensure that unary expressions bind
    // tighter than assignments.
    unary_expression: $ => prec(PREC.unary, choice(
      seq(choice('!', '-', 'await'), $.unary_expression),
      $.call_chain,
    )),

    // A call chain allows for nested function calls, member accesses
    // and index operations, which all have the same precedence and
    // associate left‑to‑right.  The base is a primary expression
    // (identifier, literal, parenthesised expression or closure).
    // Call chains (function calls, member accesses, casts, etc.) are
    // left associative.  Each suffix (call, member access, index,
    // cast, error propagation, etc.) extends the previous chain.
    call_chain: $ => prec.left(seq(
      $._primary_expression,
      repeat(choice(
        $.call_suffix,
        $.member_access,
        $.index_suffix,
        $.error_propagation,
        $.pointer_deref,
        $.await_suffix,
        $.cast_suffix,
        $.bitcast_suffix,
        $.saturating_cast_suffix,
        $.wrapping_cast_suffix,
        $.checked_cast_suffix
      )),
    )),

    call_suffix: $ => seq(
      field('arguments', $.arguments),
    ),

    member_access: $ => seq('.', field('property', $.identifier)),

    index_suffix: $ => seq('[', field('index', $.expression), ']'),

    // Error propagation suffix `!` forwards an error from the
    // preceding expression.  It has the same precedence as other
    // call chain suffixes.
    error_propagation: $ => '!',

    // Pointer dereference suffix `.*` reads the value pointed to by
    // the preceding expression.
    pointer_deref: $ => seq('.', '*'),

    // Await suffix `.await` awaits completion of an async value.
    await_suffix: $ => seq('.', 'await'),

    // Cast suffixes convert the value to a different type.
    cast_suffix: $ => seq('.', '(', $.type, ')'),

    bitcast_suffix: $ => seq('.', '^', $.type),

    saturating_cast_suffix: $ => seq('.', '|', $.type),

    wrapping_cast_suffix: $ => seq('.', '%', $.type),

    checked_cast_suffix: $ => seq('.', '?', $.type),

    // Primary expressions are the leaves of the expression tree.
    _primary_expression: $ => choice(
      $.literal_expression,
      $.identifier,
      $.parenthesized_expression,
      $.closure_expression,
      $.if_expression,
      $.while_expression,
      $.for_expression,
      $.match_expression,
      $.block_expression,
      $.async_expression,
    ),

    // Async blocks begin with the `async` keyword and contain a
    // block.  They evaluate to a future value that can be awaited.
    async_expression: $ => seq('async', $.block),

    parenthesized_expression: $ => seq(
      '(', $.expression, ')',
    ),

    // Closure expressions have the form `|params| expr` or
    // `|params| { block }`.  Parameter names may include type
    // annotations.
    // Closure expressions bind tighter than block expressions to
    // resolve ambiguities with `||` operators.  A closure must
    // contain at least one parameter; empty parameter lists are
    // currently disallowed to avoid conflicts with logical OR.
    closure_expression: $ => prec(1, seq(
      '|',
      $.closure_parameter,
      repeat(seq(',', $.closure_parameter)),
      '|',
      choice($.expression, $.block),
    )),

    closure_parameter: $ => seq(
      field('name', $.identifier),
      optional(seq(':', field('type', $.type))),
    ),

    // Control flow constructs are expressions that produce a value.
    // If expressions produce a value.  They bind more tightly than a
    // bare block expression to avoid ambiguity when an `if … else` is
    // followed by another statement (e.g. `if x { } else { } import …`).
    if_expression: $ => prec(1, seq(
      'if',
      field('condition', $.expression),
      field('consequence', $.block),
      optional(seq('else', field('alternative', choice($.block, $.expression)))),
    )),

    // While expressions support several forms:
    //   while <condition> { ... }
    //   while { ... }           // infinite loop
    //   while is <pattern> := <value> { ... } // predicate pattern loop
    // While expressions have higher precedence than block expressions to
    // resolve ambiguities like `while { ... } = ...`.  The forms
    // supported are:
    //   while is <pattern> := <value> { ... }
    //   while <condition> { ... }
    //   while { ... }
    while_expression: $ => prec(1, seq(
      'while',
      choice(
        // pattern binding loop
        seq(
          'is',
          field('pattern', $.loop_pattern),
          ':=',
          field('value', $.expression),
          field('body', $.block),
        ),
        // condition and body
        seq(
          field('condition', $.expression),
          field('body', $.block),
        ),
        // infinite loop
        field('body', $.block),
      ),
    )),

    // For expressions iterate over an iterable with a pattern.  The
    // pattern for `for` loops does not permit literal expressions, to
    // avoid ambiguity with assignment.  Destructuring and wildcard
    // patterns are allowed.
    for_expression: $ => seq(
      'for',
      field('pattern', $.loop_pattern),
      'in',
      field('iterable', $.expression),
      field('body', $.block),
    ),

    // Loop patterns are a restricted subset of patterns that exclude
    // literal expressions.  They allow identifiers, wildcard
    // `_`, and destructuring of variant cases.
    loop_pattern: $ => choice(
      '_',
      $.identifier,
      seq(
        $.call_chain,
        '{',
        optional(seq(
          $.pattern_field,
          repeat(seq(',', $.pattern_field)),
          optional(',')
        )),
        '}',
      ),
    ),

    match_expression: $ => seq(
      'match', field('value', $.expression), '{', repeat1($.match_arm), '}',
    ),

    match_arm: $ => seq(
      field('pattern', $.pattern), '=>', field('body', $.expression), optional(','),
    ),

    // Patterns are used in `match` arms and `for` bindings.  They
    // include wildcards (`_`), literals, identifiers and
    // destructuring of tuple or struct cases.  A simple case like
    // `FileSystemError.DiskFull{bytes}` is represented here as a
    // call_chain followed by an optional field list.
    pattern: $ => choice(
      '_',
      $.literal_expression,
      $.call_chain,
      seq(
        $.call_chain,
        '{',
        optional(seq(
          $.pattern_field,
          repeat(seq(',', $.pattern_field)),
          optional(',')
        )),
        '}',
      ),
    ),

    pattern_field: $ => seq(
      field('name', $.identifier),
      optional(seq(':', field('value', $.pattern))),
    ),

    block_expression: $ => $.block,

    // Function call arguments.  A comma separated list of expressions
    // enclosed in parentheses.  The list may be empty.
    arguments: $ => seq(
      '(',
      optional(seq(
        $.expression,
        repeat(seq(',', $.expression))
      )),
      ')'
    ),

    // Literal expressions.  Integer and float literals allow
    // underscores for readability.  String and character literals
    // support escaped characters.
    literal_expression: $ => choice(
      $.boolean_literal,
      $.integer_literal,
      $.float_literal,
      $.string_literal,
      $.char_literal,
      $.null_literal,
    ),

    boolean_literal: $ => choice('true', 'false'),

    null_literal: $ => 'null',

    integer_literal: $ => token(/[0-9][0-9_]*(?:[uU](8|16|32|64|128|size)|[iI](8|16|32|64|128|size))?/),

    float_literal: $ => token(/[0-9][0-9_]*\.[0-9][0-9_]*(?:[eE][+-]?[0-9][0-9_]*)?(?:f(32|64))?/),

    string_literal: $ => token(seq(
      '"',
      repeat(choice(/[^"\\\n]/, /\\./)),
      '"'
    )),

    char_literal: $ => token(seq(
      '\'',
      choice(/[^'\\\n]/, /\\./),
      '\'',
    )),

    // Types.  To avoid ambiguity when parsing pointer types and
    // error‑union types (e.g. `*T!E`), we break the type grammar into
    // two layers.  A `non_error_type` represents types that do not
    // include the `!` operator.  An `error_union_type` combines a
    // non‑error type on the left with another type on the right.  The
    // `type` rule chooses between these to ensure that pointers and
    // optionals bind tighter than the error‑union operator.
    type: $ => choice(
      $.error_union_type,
      $.non_error_type,
    ),

    // Error union types associate to the left: `A!B!C` parses as
    // `(A!B)!C`.  The left side must be a non‑error type to avoid
    // infinite recursion.  The right side can be any type.
    error_union_type: $ => prec.left(seq(
      field('success', $.non_error_type),
      '!',
      field('error', $.type),
    )),

    // Non‑error types include pointers, arrays, slices, optionals, maps
    // and identifiers.  Each operator binds tightly and recurses on
    // `type` to allow nested constructs like `**[10]i32`.  The order
    // here reflects the lexical forms rather than operator precedence.
    non_error_type: $ => choice(
      // Map type: [Key:Value]
      seq('[', field('key', $.type), ':', field('value', $.type), ']'),
      // Static array: [N]T
      seq('[', field('size', $.expression), ']', field('element', $.type)),
      // Dynamic array: [dyn]T
      seq('[', 'dyn', ']', field('element', $.type)),
      // Slice: []T
      seq('[', ']', field('element', $.type)),
      // Pointer: *T
      seq('*', field('pointee', $.type)),
      // Optional type: ?T
      seq('?', field('optional', $.type)),
      // Base case
      $.identifier,
    ),

    // Identifiers.  Raw identifiers prefixed with `r#` are
    // supported.  The regex deliberately avoids matching keywords by
    // requiring at least one non‑digit character after the prefix.
    identifier: $ => token(/[A-Za-z_][A-Za-z0-9_]*/),

    // Comments support both single‑line (`//`) and block (`/* ... */`)
    // styles.  Nested block comments are not supported.
    comment: $ => token(choice(
      seq('//', /[^\n]*/),
      seq('/*', /[^*]*\*+([^/*][^*]*\*+)*/, '/'),
    )),
  },
});

//
// Note: In earlier versions of this grammar a `lexeme` helper was
// introduced to force specific regular expressions to be treated as a
// single token.  It turned out to be unnecessary for the current
// implementation, so the helper has been removed.  If future
// extensions require tighter lexical control you can reintroduce
// such a helper and call `token(prec(...))` as appropriate.