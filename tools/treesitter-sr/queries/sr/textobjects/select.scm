; Functions/procs
(function_declaration) @function.outer
(function_declaration body: (block) @function.inner)
(proc_declaration) @function.outer
(proc_declaration  body: (block) @function.inner)

; Types
(struct_declaration) @class.outer
(struct_declaration "{" @class.inner.start "}" @class.inner.end)
(enum_declaration) @class.outer
(enum_declaration  "{" @class.inner.start "}" @class.inner.end)
(union_declaration) @class.outer
(union_declaration "{" @class.inner.start "}" @class.inner.end)

; Blocks
(block) @block.outer
(block "{" @block.inner.start "}" @block.inner.end)

; Conditionals / loops / match
(if_expression) @conditional.outer
(if_expression consequence: (block) @conditional.inner)
(while_expression) @loop.outer
(while_expression body: (block) @loop.inner)
(for_expression) @loop.outer
(for_expression  body: (block) @loop.inner)
(match_expression) @conditional.outer
(match_expression "{" @conditional.inner.start "}" @conditional.inner.end)

; Parameters & arguments
(parameters) @parameter.outer
(arguments)  @parameter.outer
(parameter name: (identifier) @parameter.inner)
