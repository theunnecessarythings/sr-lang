; Scopes
(block) @scope
(function_declaration body: (block) @scope)
(proc_declaration      body: (block) @scope)
(if_expression (block) @scope)
(while_expression (block) @scope)
(for_expression  (block) @scope)
(match_expression "{" @scope) ; open scope for arms

; Definitions
(const_declaration name: (identifier) @definition.constant)
(var_declaration   name: (identifier) @definition.var)
(struct_declaration name: (identifier) @definition.type)
(enum_declaration   name: (identifier) @definition.type)
(union_declaration  name: (identifier) @definition.type)
(type_alias         name: (identifier) @definition.type)
(function_declaration name: (identifier) @definition.function)
(proc_declaration     name: (identifier) @definition.function)
(parameter name: (identifier) @definition.parameter)
(struct_field name: (identifier) @definition.field)
(enum_variant name: (identifier) @definition.constant)
(union_case name: (identifier) @definition.constant)

; References
(identifier) @reference
