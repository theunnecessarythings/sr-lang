; Scope definitions
(block) @scope
(match_arm) @scope
(parameter_list) @scope
(closure_parameters) @scope
(struct_body) @scope
(union_body) @scope
(enum_body) @scope
(variant_body) @scope

; Definitions
(const_declaration
  pattern: (identifier) @definition.constant)
(var_declaration
  pattern: (identifier) @definition.var)
(parameter
  pattern: (identifier) @definition.parameter)
(binding_pattern
  name: (identifier) @definition.var)
(loop_label
  label: (identifier) @definition.label)
(struct_field
  name: (identifier) @definition.field)
(union_field
  name: (identifier) @definition.field)
(enum_variant
  name: (identifier) @definition.constant)
(variant_case
  name: (identifier) @definition.type)
