; Comments
(comment) @comment

; Literals
(integer_literal) @number
(float_literal) @number
(string_literal) @string
(char_literal) @character
(boolean_literal) @boolean

; Attributes
(attribute
  (identifier) @attribute)
(attribute_argument
  name: (identifier) @attribute
  value: (identifier) @constant)

; Identifiers
(identifier) @variable
(type_identifier) @type
(path (identifier) @namespace)
(type_path (identifier) @namespace)

; Definitions
(const_declaration
  pattern: (identifier) @constant)
(var_declaration
  pattern: (identifier) @variable)
(parameter
  pattern: (identifier) @parameter)
(binding_pattern
  name: (identifier) @variable)
(loop_label
  label: (identifier) @label)
(enum_variant
  name: (identifier) @constant)
(struct_field
  name: (identifier) @field)
(union_field
  name: (identifier) @field)
(variant_case
  name: (identifier) @type)
(struct_literal_field
  name: (identifier) @field)

; Keywords
[("fn") ("proc") ("struct") ("union") ("enum") ("variant")
 ("if") ("else") ("while") ("for") ("in") ("match")
 ("return") ("break") ("continue") ("defer") ("errdefer")
 ("comptime") ("code") ("async") ("import") ("const") ("var")
 ("pub") ("package") ("insert") ("asm") ("mlir") ("error")]
 @keyword

; Operators
(binary_expression operator: (_) @operator)
(unary_expression operator: (_) @operator)
(assignment_statement operator: (_) @operator)
(cast_expression "." @operator)
(pointer_dereference_expression "." @operator)
(error_propagation_expression "!" @operator)
(optional_unwrap_expression "?" @operator)

; Punctuation
["{" "}" "(" ")" "[" "]" "," ":" ";" "=>" "::" ":=" "="] @punctuation.delimiter

; Built-in boolean literals
[("true") ("false")] @boolean
