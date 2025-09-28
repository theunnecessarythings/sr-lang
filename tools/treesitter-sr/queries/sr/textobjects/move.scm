; Next/Previous function start/end
(function_declaration name: (identifier) @function.start)
(function_declaration body: (block) @function.end)
(proc_declaration name: (identifier) @function.start)
(proc_declaration  body: (block) @function.end)

; Next/Previous class-like (struct/enum/union)
(struct_declaration name: (identifier) @class.start)
(struct_declaration "}" @class.end)
(enum_declaration name: (identifier) @class.start)
(enum_declaration  "}" @class.end)
(union_declaration name: (identifier) @class.start)
(union_declaration  "}" @class.end)
