(block
  "{" @indent.begin
  "}" @indent.end) @indent.branch

(match_expression
  "{" @indent.begin
  "}" @indent.end)

(struct_literal_body
  "{" @indent.begin
  "}" @indent.end)

(struct_body
  "{" @indent.begin
  "}" @indent.end)

(union_body
  "{" @indent.begin
  "}" @indent.end)

(enum_body
  "{" @indent.begin
  "}" @indent.end)

(variant_body
  "{" @indent.begin
  "}" @indent.end)

(variant_pattern_fields
  "{" @indent.begin
  "}" @indent.end)

(parameter_list
  "(" @indent.begin
  ")" @indent.end)

(argument_list
  "(" @indent.begin
  ")" @indent.end)

(tuple_expression
  "(" @indent.begin
  ")" @indent.end)

(tuple_type
  "(" @indent.begin
  ")" @indent.end)

(array_expression
  "[" @indent.begin
  "]" @indent.end)

(array_type
  "[" @indent.begin
  "]" @indent.end)

(map_type
  "[" @indent.begin
  "]" @indent.end)

(slice_type
  "[" @indent.begin
  "]" @indent.end)

(dynamic_array_type
  "[" @indent.begin
  "]" @indent.end)

(struct_literal_field value: (_) @indent.align)
(argument_list (_) @indent.align)
(parameter_list (_) @indent.align)
(tuple_expression (_) @indent.align)
(tuple_type (_) @indent.align)
(array_expression (_) @indent.align)
