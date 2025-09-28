(block "{" @indent.begin)
(block "}" @indent.end)

(parameters "(" @indent.begin)
(parameters ")" @indent.end)

(arguments "(" @indent.begin)
(arguments ")" @indent.end)

(index_suffix "[" @indent.begin)
(index_suffix "]" @indent.end)

; Statements that start an indented block (even when followed on next line)
(if_expression "if" @indent.branch)
(while_expression "while" @indent.branch)
(for_expression "for" @indent.branch)
(match_expression "match" @indent.branch)
