; Inject SR inside string literals that look like `/* language=sr */ "..."` (comment directive)
((string_literal) @injection.content
  (#match? @injection.content "^/\\*\\s*language=sr\\s*\\*/")
  (#set! injection.language "sr"))

; JSON/regex/etc. stubs you can uncomment later
; ((string_literal) @injection.content
;   (#match? @injection.content "^\\{"))
;   (#set! injection.language "json"))
