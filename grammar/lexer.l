%option noyywrap nodefault yylineno
%option never-interactive
%option pointer

%{
  #include <stdio.h>
  #include <stdlib.h>
  #include <string.h>
  #include "ast.h"
  #include "parser.tab.h"
  static char* dup_text(void){ size_t n=yyleng; char* s=(char*)malloc(n+1); memcpy(s,yytext,n); s[n]=0; return s; }
  #define RET(tok)  do{ return tok; }while(0)
  #define RETS(tok) do{ yylval.str=dup_text(); return tok; }while(0)
%}

%s NLSEMI

WS         [ \t\f]
NL         (\r\n|[\r\n])
ID_START   [A-Za-z]
ID_CONT    [A-Za-z_0-9]
HEX        [0-9A-Fa-f]
OCT        [0-7]
DEC        [0-9]([0-9]|_)*
HEX_LIT    0[xX]_*{HEX}({HEX}|_)*
OCT_LIT    0[oO]_*{OCT}({OCT}|_)*
BIN_LIT    0[bB]_*[01][01_]*
EXP        [eE][+-]?_*{DEC}
INTSUF     (u(8|16|32|64|128|size)|i(8|16|32|64|128|size))
FNSUF      f(32|64)

%%

^#![^\r\n]*                                   ;

<INITIAL,NLSEMI>[ \t\f]+                      ;
<INITIAL>{NL}+                                ;

<INITIAL,NLSEMI>"//"[^\r\n]*                  ;

<INITIAL>\/\*[^*]*\*+([^/*][^*]*\*+)*\/       ;
<NLSEMI>\/\*[^*]*\*+([^/*][^*]*\*+)*\/        { BEGIN(INITIAL); RET(EOS); }

<NLSEMI>{NL}{WS}*\}                           { BEGIN(INITIAL); }
<NLSEMI>{NL}+                                 { BEGIN(INITIAL); RET(EOS); }
<NLSEMI>";"                                   { BEGIN(INITIAL); RET(EOS); }
<NLSEMI><<EOF>>                               { BEGIN(INITIAL); RET(EOS); }

"align"        { RET(ALIGN); }
"and"          { RET(AND); }
"any"          { BEGIN(NLSEMI); RET(ANY); }
"as"           { RET(AS); }
"asm"          { RET(ASM); }
"async"        { RET(ASYNC); }
"await"        { BEGIN(NLSEMI); RET(AWAIT); }
"break"        { BEGIN(NLSEMI); RET(BREAK); }
"catch"        { RET(CATCH); }
"comptime"     { RET(COMPTIME); }
"code"         { RET(CODE); }
"complex"      { RET(COMPLEX); }
"const"        { RET(CONST); }
"continue"     { BEGIN(NLSEMI); RET(CONTINUE); }
"dyn"          { RET(DYN); }
"defer"        { RET(DEFER); }
"else"         { RET(ELSE); }
"enum"         { RET(ENUM); }
"errdefer"     { RET(ERRDEFER); }
"error"        { RET(ERROR); }
"export"       { RET(EXPORT); }
"extern"       { RET(EXTERN); }
"false"        { BEGIN(NLSEMI); RET(FALSE); }
"fn"           { RET(FN); }
"for"          { RET(FOR); }
"if"           { RET(IF); }
"in"           { RET(IN); }
"is"           { RET(IS); }
"insert"       { RET(INSERT); }
"import"       { RET(IMPORT); }
"match"        { RET(MATCH); }
"mlir"         { RET(MLIR); }
"noreturn"     { BEGIN(NLSEMI); RET(NORETURN); }
"null"         { BEGIN(NLSEMI); RET(NULL_KW); }
"opaque"       { RET(OPAQUE); }
"or"           { RET(OR); }
"orelse"       { RET(ORELSE); }
"package"      { RET(PACKAGE); }
"proc"         { RET(PROC); }
"pub"          { RET(PUB); }
"return"       { BEGIN(NLSEMI); RET(RETURN); }
"linksection"  { RET(LINKSECTION); }
"simd"         { RET(SIMD); }
"struct"       { RET(STRUCT); }
"threadlocal"  { RET(THREADLOCAL); }
"tensor"       { RET(TENSOR); }
"test"         { RET(TEST); }
"true"         { BEGIN(NLSEMI); RET(TRUE); }
"type"         { RET(TYPE); }
"typeof"       { RET(TYPEOF); }
"union"        { RET(UNION); }
"undefined"    { BEGIN(NLSEMI); RET(UNDEFINED); }
"unreachable"  { RET(UNREACHABLE); }
"variant"      { RET(VARIANT); }
"while"        { RET(WHILE); }

"_"                                        { RET(UNDERSCORE); }
"r#"{ID_START}{ID_CONT}*                   { BEGIN(NLSEMI); RETS(RAW_IDENTIFIER); }
{ID_START}{ID_CONT}*                       { BEGIN(NLSEMI); RETS(NON_KEYWORD_IDENTIFIER); }
_{ID_CONT}+                                { BEGIN(NLSEMI); RETS(NON_KEYWORD_IDENTIFIER); }

'([^\\'\n\r\t]|\\([nrt\\0'\"x][0-9A-Fa-f]*|u\{[0-9A-Fa-f]{1,6}\}))'      { BEGIN(NLSEMI); RETS(CHAR_LITERAL); }
\"([^\"\\\n]|\\\n|\\([nrt\\0'\"x][0-9A-Fa-f]*|u\{[0-9A-Fa-f]{1,6}\}))*\"  { BEGIN(NLSEMI); RETS(STRING_LITERAL); }
b'([^\\'\n\r\t]|\\[nrt\\0'\"x][0-9A-Fa-f]*)'                             { BEGIN(NLSEMI); RETS(BYTE_LITERAL); }
b\"([^\"\\\n]|\\\n|\\[nrt\\0'\"x][0-9A-Fa-f]*)*\"                        { BEGIN(NLSEMI); RETS(BYTE_STRING_LITERAL); }

({DEC}(\.{DEC}?)?{EXP}?|{BIN_LIT}|{OCT_LIT}|{HEX_LIT})i                  { BEGIN(NLSEMI); RETS(IMAGINARY_LITERAL); }
{DEC}\.{DEC}?{EXP}?{FNSUF}?                                               { BEGIN(NLSEMI); RETS(FLOAT_LITERAL); }
{DEC}({EXP}{FNSUF}?|{FNSUF})                                              { BEGIN(NLSEMI); RETS(FLOAT_LITERAL); }
({DEC}|{BIN_LIT}|{OCT_LIT}|{HEX_LIT}){INTSUF}?                           { BEGIN(NLSEMI); RETS(INTEGER_LITERAL); }

"<<|="      { RET(SHLPIPEEQ); }
"<<|"       { RET(SHLPIPE); }
"+|="       { RET(PLUSPIPEEQ); }
"+|"        { RET(PLUSPIPE); }
"-|="       { RET(MINUSPIPEEQ); }
"-|"        { RET(MINUSPIPE); }
"*|="       { RET(STARPIPEEQ); }
"*|"        { RET(STARPIPE); }
"+%="       { RET(PLUSPERCENTEQ); }
"+%"        { RET(PLUSPERCENT); }
"-%="       { RET(MINUSPERCENTEQ); }
"-%"        { RET(MINUSPERCENT); }
"*%="       { RET(STARPERCENTEQ); }
"*%"        { RET(STARPERCENT); }

"<<="       { RET(SHLEQ); }
">>="       { RET(SHREQ); }
"||"        { RET(PIPEPIPE); }
"=="        { RET(EQEQ); }
"!="        { RET(NE); }
">="        { RET(GE); }
"<="        { RET(LE); }
"+="        { RET(PLUSEQ); }
"-="        { RET(MINUSEQ); }
"->"        { RET(RARROW); }
"*="        { RET(STAREQ); }
"/="        { RET(SLASHEQ); }
"%="        { RET(PERCENTEQ); }
"^="        { RET(CARETEQ); }
"&="        { RET(ANDEQ); }
"|="        { RET(OREQ); }

"..="       { RET(DOTDOTEQ); }
"..."       { RET(DOTDOTDOT); }
".."        { RET(DOTDOT); }
".*"        { BEGIN(NLSEMI); RET(DOTSTAR); }
".("        { RET(DOTLPAREN); }
".["        { RET(DOTLSQUAREBRACKET); }
".{"        { RET(DOTLCURLYBRACE); }

"?"         { BEGIN(NLSEMI); RET(QUESTION); }
"!"         { BEGIN(NLSEMI); RET(BANG); }
"{"         { RET(LCURLYBRACE); }
"}"         { BEGIN(NLSEMI); RET(RCURLYBRACE); }
"["         { RET(LSQUAREBRACKET); }
"]"         { BEGIN(NLSEMI); RET(RSQUAREBRACKET); }
"("         { RET(LPAREN); }
")"         { BEGIN(NLSEMI); RET(RPAREN); }
"+"         { RET(PLUS); }
"-"         { RET(MINUS); }
"*"         { RET(STAR); }
"/"         { RET(SLASH); }
"%"         { RET(PERCENT); }
"^"         { RET(CARET); }
"&"         { RET(B_AND); }
"|"         { RET(B_OR); }
"<<"        { RET(SHL); }
">>"        { RET(SHR); }
"="         { RET(EQ); }
">"         { RET(GT); }
"<"         { RET(LT); }
"@"         { RET(AT); }
"."         { RET(DOT); }
","         { RET(COMMA); }
";"         { RET(SEMI); }
":"         { RET(COLON); }
"::"        { RET(COLONCOLON); }
":="        { RET(COLONEQ); }
"=>"        { RET(FATARROW); }
"#"         { RET(POUND); }

<<EOF>>     { return 0; }

.           ;

%%

