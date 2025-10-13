(comment) @comment

(string_literal) @string
(raw_string_literal) @string
(char_literal) @character
(integer_literal) @number
(float_literal) @number
(boolean_literal) @boolean

(identifier) @variable
(qualified_identifier (identifier) @namespace)

(function_declaration
  name: (identifier) @function)

(procedure_declaration
  name: (identifier) @function)

(attribute
  (identifier) @attribute)

[("fn") ("proc") ("struct") ("enum") ("if") ("else") ("while") ("for") ("in") ("match") ("return") ("import") ("const") ("let")] @keyword

(basic_type) @type
(pointer_type) @type
(array_type) @type
(slice_type) @type
(tuple_type) @type

(binary_expression ["+" "-" "*" "/" "%" "==" "!=" "<" "<=" ">" ">=" "&&" "||" "&" "|" "^"] @operator)
(unary_expression ["+" "-" "!" "~" "*"] @operator)
(assignment ["=" "+=" "-=" "*=" "/=" "%=" "<<=" ">>=" "&=" "|=" "^="] @operator)
