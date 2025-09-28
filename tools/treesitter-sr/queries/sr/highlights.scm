; Keywords
[
  "import" "type" "proc" "fn" "struct" "enum" "union" "variant"
  "defer" "errdefer" "return" "break" "continue" "insert"
  "async" "await" "match" "if" "else" "while" "for" "in" "is"
  "catch" "orelse" "dyn"
] @keyword

; Booleans / null
(boolean_literal) @boolean
(null_literal) @constant.builtin

; Decls & identifiers
(const_declaration name: (identifier) @constant)
(var_declaration   name: (identifier) @variable)
(function_declaration
  name: (identifier) @function)
(proc_declaration
  name: (identifier) @function)
(type_alias
  name: (identifier) @type.definition)
(struct_declaration
  name: (identifier) @type)
(enum_declaration
  name: (identifier) @type)
(union_declaration
  name: (identifier) @type)

; Struct/enum/union members
(struct_field name: (identifier) @field)
(enum_variant name: (identifier) @constant)
(union_case   name: (identifier) @constant)

; Parameters
(parameter name: (identifier) @parameter)
(closure_parameter name: (identifier) @parameter)

; Attributes
(attribute_list "@[" @punctuation.bracket)
(attribute_list "]"  @punctuation.bracket)
(attribute name: (identifier) @attribute)
(attribute value: (expression) @constant.macro)

; Types
(type) @type
(non_error_type (identifier) @type)
(error_union_type "!" @operator)

; Pointers/arrays/slices/maps/optionals
(non_error_type
  ["*" "[" "]" "?" ":" ] @punctuation.bracket)

; Literals
(string_literal) @string
(char_literal)   @string.char
(integer_literal) @number
(float_literal)   @float

; Calls / member / index / casts
(member_access "." @punctuation.delimiter)
(index_suffix ["[" "]"] @punctuation.bracket)
(call_suffix (arguments) @punctuation.bracket)
(cast_suffix ["." "(" ")"] @punctuation.bracket)
(bitcast_suffix ["." "^"] @operator)
(saturating_cast_suffix ["." "|"] @operator)
(wrapping_cast_suffix ["." "%"] @operator)
(checked_cast_suffix ["." "?"] @operator)
(pointer_deref ["." "*"] @operator)
(await_suffix ["." "await"] @keyword)
(error_propagation "!") @operator

; Operators (arithmetic, logical, comparison, assignment, range)
[
  "+" "-" "*"
  "/" "%" "<<"
  ">>" "+|" "-|" "*|"
  "+%" "-%" "*%"
] @operator
[
  "==" "!=" "<" "<=" ">" ">="
] @operator
[
  "or" "||" "and" "&&"
] @operator
(assignment_expression
  operator: [
    "=" "+=" "-=" "*=" "/=" "%=" "&=" "|=" "^=" "<<=" ">>="
    "+|=" "-|=" "*|=" "<<|=" ">>|=" "+%=" "-%=" "*%="
  ] @operator)
(range_expression [".." "..="] @operator)
(orelse_expression "orelse" @keyword)
(catch_expression "catch" @keyword)

; Control blocks and delimiters
(block ["{" "}"] @punctuation.bracket)
(parameters ["(" ")"] @punctuation.bracket)
(arguments  ["(" ")"] @punctuation.bracket)
(match_expression ["{" "}"] @punctuation.bracket)
(pattern_field ":" @punctuation.delimiter)
("," @punctuation.delimiter)
(";" @punctuation.delimiter)

; Flow keywords
[
  (return_statement)
  (break_statement)
  (continue_statement)
] @keyword

; Comments & extras
(comment) @comment
