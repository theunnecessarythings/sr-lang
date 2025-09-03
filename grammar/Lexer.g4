lexer grammar Lexer;

@header {#include "LexerBase.h"}

options
{
    superClass = LexerBase;
}

// Keywords
ALIGN : 'align' ;
AND : 'and' ;
ANY : 'any' -> mode(NLSEMI);
AS : 'as' ;
ASM : 'asm' ;
ASYNC : 'async' ;
AWAIT : 'await' -> mode(NLSEMI);
BREAK : 'break' -> mode(NLSEMI);
CATCH : 'catch' ;
COMPTIME : 'comptime' ;
CODE : 'code' ;
COMPLEX : 'complex' ;
CONST : 'const' ;
CONTINUE : 'continue' -> mode(NLSEMI);
DYN: 'dyn' ;
DEFER : 'defer' ;
ELSE : 'else' ;
ENUM : 'enum' ;
ERRDEFER : 'errdefer' ;
ERROR : 'error' ;
EXPORT : 'export' ;
EXTERN : 'extern' ;
FALSE : 'false' -> mode(NLSEMI);
FN : 'fn' ;
FOR : 'for' ;
IF : 'if' ;
IN : 'in' ;
IS : 'is' ;
INSERT : 'insert' ;
IMPORT : 'import' ;
MATCH : 'match' ;
MLIR : 'mlir' ;
NORETURN : 'noreturn' -> mode(NLSEMI);
NULL : 'null' -> mode(NLSEMI);
OPAQUE : 'opaque' ;
OR : 'or' ;
ORELSE : 'orelse' ;
PACKAGE : 'package' ;
PROC : 'proc' ;
PUB : 'pub' ;
RETURN : 'return' -> mode(NLSEMI);
LINKSECTION : 'linksection' ;
SIMD : 'simd' ;
STRUCT : 'struct' ;
THREADLOCAL : 'threadlocal' ;
TENSOR : 'tensor' ;
TEST : 'test' ;
TRUE : 'true' -> mode(NLSEMI);
TYPE : 'type' ;
TYPEOF : 'typeof' ;
UNION : 'union' ;
UNDEFINED : 'undefined' -> mode(NLSEMI);
UNREACHABLE : 'unreachable' ;
VARIANT : 'variant' ;
WHILE : 'while' ;

NON_KEYWORD_IDENTIFIER: (XID_Start XID_Continue* | '_' XID_Continue+) -> mode(NLSEMI);

fragment XID_Start: [\p{L}\p{Nl}] | UNICODE_OIDS;

fragment XID_Continue: XID_Start | [\p{Mn}\p{Mc}\p{Nd}\p{Pc}] | UNICODE_OIDC;

fragment UNICODE_OIDS: '\u1885' ..'\u1886' | '\u2118' | '\u212e' | '\u309b' ..'\u309c';

fragment UNICODE_OIDC: '\u00b7' | '\u0387' | '\u1369' ..'\u1371' | '\u19da';

RAW_IDENTIFIER: 'r#' NON_KEYWORD_IDENTIFIER;
LINE_COMMENT: ('//' (~[/!] | '//') ~[\r\n]* | '//') -> channel (HIDDEN);

BLOCK_COMMENT:
    (
        '/*' (~[*!] | '**' | BLOCK_COMMENT_OR_DOC) (BLOCK_COMMENT_OR_DOC | ~[*])*? '*/'
        | '/**/'
        | '/***/'
    ) -> channel (HIDDEN)
;

INNER_LINE_DOC: '//!' ~[\n\r]* -> channel (HIDDEN); // isolated cr

INNER_BLOCK_DOC: '/*!' ( BLOCK_COMMENT_OR_DOC | ~[*])*? '*/' -> channel (HIDDEN);

OUTER_LINE_DOC: '///' (~[/] ~[\n\r]*)? -> channel (HIDDEN); // isolated cr

OUTER_BLOCK_DOC:
    '/**' (~[*] | BLOCK_COMMENT_OR_DOC) (BLOCK_COMMENT_OR_DOC | ~[*])*? '*/' -> channel (HIDDEN)
;

BLOCK_COMMENT_OR_DOC: ( BLOCK_COMMENT | INNER_BLOCK_DOC | OUTER_BLOCK_DOC) -> channel (HIDDEN);

SHEBANG: {this->SOF()}? '\ufeff'? '#!' ~[\r\n]* -> channel(HIDDEN);

WHITESPACE : [\p{Zs}]          -> channel(HIDDEN);
NEWLINE    : ('\r\n' | [\r\n]) -> channel(HIDDEN);

// tokens char and string
CHAR_LITERAL: '\'' ( ~['\\\n\r\t] | QUOTE_ESCAPE | ASCII_ESCAPE | UNICODE_ESCAPE) '\'' -> mode(NLSEMI);

STRING_LITERAL: '"' ( ~["] | QUOTE_ESCAPE | ASCII_ESCAPE | UNICODE_ESCAPE | ESC_NEWLINE)* '"' -> mode(NLSEMI);

RAW_STRING_LITERAL: 'r' RAW_STRING_CONTENT -> mode(NLSEMI);

fragment RAW_STRING_CONTENT: '#' RAW_STRING_CONTENT '#' | '"' .*? '"';

BYTE_LITERAL: 'b\'' (. | QUOTE_ESCAPE | BYTE_ESCAPE) '\'' -> mode(NLSEMI);

BYTE_STRING_LITERAL: 'b"' (~["] | QUOTE_ESCAPE | BYTE_ESCAPE)* '"' -> mode(NLSEMI);

RAW_BYTE_STRING_LITERAL: 'br' RAW_STRING_CONTENT -> mode(NLSEMI);

RAW_ASM_BLOCK: 'asm' WHITESPACE* '{' .*? '}' -> mode(NLSEMI);


fragment ASCII_ESCAPE: '\\x' OCT_DIGIT HEX_DIGIT | COMMON_ESCAPE;

fragment BYTE_ESCAPE: '\\x' HEX_DIGIT HEX_DIGIT | COMMON_ESCAPE;

fragment COMMON_ESCAPE: '\\' [nrt\\0];

fragment UNICODE_ESCAPE:
    '\\u{' HEX_DIGIT HEX_DIGIT? HEX_DIGIT? HEX_DIGIT? HEX_DIGIT? HEX_DIGIT? '}'
;

fragment QUOTE_ESCAPE: '\\' ['"];

fragment ESC_NEWLINE: '\\' '\n';

// number

IMAGINARY_LITERAL: ((DEC_LITERAL ('.' DEC_LITERAL?)? FLOAT_EXPONENT?) | BIN_LITERAL | OCT_LITERAL | HEX_LITERAL) 'i' -> mode(NLSEMI);

INTEGER_LITERAL: ( DEC_LITERAL | BIN_LITERAL | OCT_LITERAL | HEX_LITERAL) INTEGER_SUFFIX? -> mode(NLSEMI);

DEC_LITERAL: DEC_DIGIT (DEC_DIGIT | '_')*;

HEX_LITERAL: '0x' '_'* HEX_DIGIT (HEX_DIGIT | '_')*;

OCT_LITERAL: '0o' '_'* OCT_DIGIT (OCT_DIGIT | '_')*;

BIN_LITERAL: '0b' '_'* [01] [01_]*;

FLOAT_LITERAL:
                        {this->floatLiteralPossible()}? (
        DEC_LITERAL '.' {this->floatDotPossible()}?
        | DEC_LITERAL ( '.' DEC_LITERAL)? FLOAT_EXPONENT? FLOAT_SUFFIX?
    ) -> mode(NLSEMI)
;

fragment INTEGER_SUFFIX:
    'u8'
    | 'u16'
    | 'u32'
    | 'u64'
    | 'u128'
    | 'usize'
    | 'i8'
    | 'i16'
    | 'i32'
    | 'i64'
    | 'i128'
    | 'isize'
;

fragment FLOAT_SUFFIX: 'f32' | 'f64';

fragment FLOAT_EXPONENT: [eE] [+-]? '_'* DEC_LITERAL;

fragment OCT_DIGIT: [0-7];

fragment DEC_DIGIT: [0-9];

fragment HEX_DIGIT: [0-9a-fA-F];

PLUS    : '+';
MINUS   : '-';
STAR    : '*';
SLASH   : '/';
PERCENT : '%';
CARET   : '^';
BANG    : '!' -> mode(NLSEMI);
B_AND   : '&';
B_OR    : '|';
SHL     : '<<';
SHR     : '>>';
PLUSEQ     : '+=';
MINUSEQ    : '-=';
RARROW     : '->';
STAREQ     : '*=';
SLASHEQ    : '/=';
PERCENTEQ  : '%=';
CARETEQ    : '^=';
ANDEQ      : '&=';
OREQ       : '|=';
SHLEQ      : '<<=';
SHREQ      : '>>=';
SHLPIPE    : '<<|';
SHLPIPEEQ  : '<<|=';
PLUSPIPE   : '+|';
PLUSPIPEEQ : '+|=';
MINUSPIPE  : '-|';
MINUSPIPEEQ: '-|=';
STARPIPE   : '*|';
STARPIPEEQ : '*|=';
PIPEPIPE   : '||';
PLUSPERCENT   : '+%';
PLUSPERCENTEQ : '+%=';
MINUSPERCENT  : '-%';
MINUSPERCENTEQ: '-%=';
STARPERCENT   : '*%';
STARPERCENTEQ : '*%=';
EQ         : '=';
EQEQ       : '==';
NE         : '!=';
GT         : '>';
LT         : '<';
GE         : '>=';
LE         : '<=';
AT         : '@';
UNDERSCORE : '_';
DOT        : '.';
DOTDOT     : '..';
DOTSTAR    : '.*' -> mode(NLSEMI);
DOTDOTDOT  : '...';
DOTDOTEQ   : '..=';
DOTLPAREN : '.(';
DOTLSQUAREBRACKET : '.[';
DOTLCURLYBRACE : '.{';
COMMA      : ',';
SEMI       : ';';
COLON      : ':';
COLONCOLON : '::';
COLONEQ    : ':=';
FATARROW   : '=>';
QUESTION   : '?' -> mode(NLSEMI);

LCURLYBRACE    : '{';
RCURLYBRACE    : '}' -> mode(NLSEMI);
LSQUAREBRACKET : '[';
RSQUAREBRACKET : ']' -> mode(NLSEMI);
LPAREN         : '(';
RPAREN         : ')' -> mode(NLSEMI);
POUND          : '#';


// Hidden tokens
mode NLSEMI;

// spaces/tabs after a “line-terminator introducer” (like ] ) — just skip
WS_NLSEMI : [ \t\f]+ -> skip;

// handle inline // comments WHILE in NLSEMI (stay in NLSEMI)
LINE_COMMENT_NLSEMI : '//' ~[\r\n]* -> channel(HIDDEN);

// emit EOS on newline, semicolon, block comment, or EOF
// the predicate keeps us from inserting EOS before a following '}' on the same line
EOS
  : (({_input->LA(1) != '}'}? ('\r\n' | [\r\n])+)     
  | ';'                                             
  | '/*' .*? '*/'                                  
  | EOF)                                             -> mode(DEFAULT_MODE)
  ;

// Did not find an EOS, so go back to normal lexing
OTHER: -> skip, mode(DEFAULT_MODE);//, channel(HIDDEN);
