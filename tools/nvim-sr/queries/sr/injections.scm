; ====================
; Injections for `sr`
; ====================


; Inject MLIR inside `mlir { ... }` blocks. Adjust the language id to match your editor/runtime.
((mlir_expression (mlir_body (_) @injection.content))
(#set! injection.language "mlir"))


; If you keep raw text nodes for MLIR, inject those too.
((mlir_text) @injection.content
(#set! injection.language "mlir"))


; Optionally inject generic assembly within `asm { ... }` blocks.
((asm_block (block) @injection.content)
(#set! injection.language "asm"))


; Example: treat code { ... } as sr itself (useful for templating constructs).
((code_expression (block) @injection.content)
(#set! injection.language "sr"))
