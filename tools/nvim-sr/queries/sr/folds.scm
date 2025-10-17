(block) @fold
(struct_body) @fold
(union_body) @fold
(enum_body) @fold
(variant_body) @fold
(struct_literal_body) @fold
(match_expression
  "{" @fold.begin
  "}" @fold.end)
(parameter_list) @fold
(argument_list) @fold
(tuple_expression) @fold
(tuple_type) @fold
(array_expression) @fold
