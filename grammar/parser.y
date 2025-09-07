%{
  #include <stdio.h>
  #include <stdlib.h>
  #include <string.h>
  #include "ast.h"

  #define ZL ((SourceLocation){0,0,0,0})

  void yyerror(const char* s);
  int yylex(void);

  AstNode *ast_root = NULL;
%}

// %glr-parser
%define lr.type ielr 
%define parse.error verbose
%define parse.trace
%locations

%code requires {
  #include "ast.h"
  typedef struct { AstNode* name; int is_underscore; } MaybeName;
}

%union {
  char*       str;
  AstNode*    node;
  Op          op;
  int         ival;
  MaybeName   mname;
}

/* ---------- tokens ---------- */
%token
  ALIGN AND ANY AS ASM ASYNC AWAIT BREAK CATCH COMPTIME CODE COMPLEX CONST CONTINUE DYN DEFER
  ELSE ENUM ERRDEFER ERROR EXPORT EXTERN FALSE FN FOR IF IN IS INSERT IMPORT MATCH MLIR
  NORETURN NULL_KW OPAQUE OR ORELSE PACKAGE PROC PUB RETURN LINKSECTION SIMD STRUCT THREADLOCAL
  TENSOR TEST TRUE TYPE TYPEOF UNION UNDEFINED UNREACHABLE VARIANT WHILE

  PLUS MINUS STAR SLASH PERCENT CARET BANG B_AND B_OR SHL SHR
  PLUSEQ MINUSEQ RARROW STAREQ SLASHEQ PERCENTEQ CARETEQ ANDEQ OREQ SHLEQ SHREQ
  SHLPIPE SHLPIPEEQ PLUSPIPE PLUSPIPEEQ MINUSPIPE MINUSPIPEEQ STARPIPE STARPIPEEQ
  PIPEPIPE PLUSPERCENT PLUSPERCENTEQ MINUSPERCENT MINUSPERCENTEQ STARPERCENT STARPERCENTEQ
  EQ EQEQ NE GT LT GE LE AT UNDERSCORE DOT DOTDOT DOTSTAR DOTDOTDOT DOTDOTEQ
  DOTLPAREN DOTLSQUAREBRACKET DOTLCURLYBRACE
  COMMA SEMI COLON COLONCOLON COLONEQ FATARROW QUESTION
  LCURLYBRACE RCURLYBRACE LSQUAREBRACKET RSQUAREBRACKET LPAREN RPAREN POUND

  EOS
;

%token <str> RAW_ASM_BLOCK
%token <str> NON_KEYWORD_IDENTIFIER RAW_IDENTIFIER
%token <str> CHAR_LITERAL STRING_LITERAL RAW_STRING_LITERAL
%token <str> BYTE_LITERAL BYTE_STRING_LITERAL RAW_BYTE_STRING_LITERAL
%token <str> INTEGER_LITERAL FLOAT_LITERAL IMAGINARY_LITERAL

/* ---------- precedence ---------- */
%right EQ PLUSEQ MINUSEQ STAREQ SLASHEQ PERCENTEQ CARETEQ ANDEQ OREQ SHLEQ SHREQ
%right PLUSPIPEEQ MINUSPIPEEQ STARPIPEEQ SHLPIPEEQ PLUSPERCENTEQ MINUSPERCENTEQ STARPERCENTEQ
%left OR
%left AND
%nonassoc EQEQ NE GT LT GE LE
%left B_OR
%left CARET
%left B_AND
%left SHL SHR SHLPIPE
%left PLUS MINUS PLUSPIPE MINUSPIPE PLUSPERCENT MINUSPERCENT
%left STAR SLASH PERCENT STARPIPE STARPERCENT
%right UREF
%right UMINUS_UBANG
%left DOT DOTSTAR
%left LSQUAREBRACKET RSQUAREBRACKET
%left LPAREN RPAREN

/* ---------- start ---------- */
%start program

/* ---------- nonterminal types ---------- */
%type <node>
  program packageDecl_opt packageDecl declarations_opt declaration
  identifier constDecl varDecl type_opt statement expressionStatement insertStatement
  deferStatement errdeferStatement attribute attrs_opt attr
  expression assign_expr catch_expr orelse_expr range_expr or_expr and_expr cmp_expr
  bitor_expr xor_expr bitand_expr shift_expr add_expr mul_expr unary_expr postfix_expr
  primary_expr attribute_opt collectionBody_opt tupleElements_opt expression_opt label_opt
  callParams_opt attr_block_expr attribute_opt_list blocklike_expr label nullExpression
  undefinedExpression functionExpression procedureExpression functionQualifiers
  ASYNC_opt extern_opt abi_opt functionParameters_opt functionParameters functionParam_list
  functionParam COMPTIME_opt functionParamPattern eqExpr_opt literalExpression
  blockExpression statements_opt statements statement_plus
  collectionBody collectionTail_opt restOfMap mapElement_seq_opt mapElement_seq mapElement
  restOfArray restArr_seq tupleElements tuple_head tupleIndex
  structExpression structExprStruct structStructTail_opt structExprFields structExprFieldsTail_opt
  structExprField_list structExprField structBase
  enumerationVariantExpression enumExprStruct 
  enumExprField_list enumExprField callParams
  closureExpression closureParameters_opt closureParameters closureParam typeAnn_opt
  loopExpression loopLabel_opt loopBody infiniteLoopExpression predicateLoopExpression
  predicatePatternLoopExpression iteratorLoopExpression loopLabel
  codeExpression mlirExpression mlirHead_opt mlirBody_opt
  asmExpression importExpression ifExpression elseTail_opt matchExpression matchArms_opt
  matchArms matchRHS matchArm matchArmGuard_opt
  pattern patternAltTail_opt patternNoTopAlt patternWithoutRange literalPattern
  identifierPattern atTail_opt wildcardPattern restPattern rangePattern rangePatternBound
  structPattern structPatternElements_opt structPatternElements structPatEtcTail_opt
  structPatternEtCetera_opt structPatternFields structPatternField_list structPatternField
  structPatternEtCetera tupleStructPattern tupleStructItems_opt tupleStructItems
  tuplePattern tuplePatList tuplePatternItems_opt tuplePatternItems groupedPattern slicePattern patternNoTopAlt_noRest patternWithoutRange_noRest
  slicePatternItems_opt slicePatternItems pathPattern
  type_ typeAtom type_exprable parenthesizedType tupleType tupleTypeTail_opt
  arrayType dynamicArrayType sliceType mapType optionalType errorType structType
  structTypeTail_opt structFields_opt structFields structField_list structField PUB_opt
  enumType parenthesizedType_opt enumItems_opt enumItems enumItem_list enumItem
  enumItemTail_opt variantType variantItems_opt variantItems variantItem_list variantItem
  variantBody_opt enumItemTuple enumItemStruct enumItemDiscriminant tupleFields_opt
  tupleFields tupleField_list tupleField unionType simdType complexType tensorType
  tensorDims rawPointerType CONST_opt bareFunctionType functionTypeQualifiers abi
  functionParametersMaybeNamedVariadic_opt functionParametersMaybeNamedVariadic
  maybeNamedFunctionParameters maybeNamedParam_list maybeNamedParam
  maybeNamedFunctionParametersVariadic inferredType path path_ndot expression_list
  pattern_list type_list COMMA_opt
  EOS_opt catchBinder_opt typeLiteralExpr noreturnType closureParam_list

%type <mname> maybeName_opt
%type <op> compoundAssignOperator comparisonOperator
%type <ival> MINUS_opt

%%

/* =========================
   Top-level & declarations
   ========================= */

program
  : packageDecl_opt declarations_opt
    { ast_root = program_node($1, $2, ZL); $$ = ast_root; }
  ;

packageDecl_opt
  : /* empty */         { $$ = NULL; }
  | packageDecl         { $$ = $1; }
  ;

packageDecl
  : PACKAGE identifier EOS
    { $$ = package_decl($2, ZL); }
  ;

declarations_opt
  : /* empty */                     { $$ = NULL; }
  | declarations_opt declaration    { $$ = decl_list_append($1, $2); }
  ;

declaration
  : constDecl
  | varDecl
  ;

identifier
  : NON_KEYWORD_IDENTIFIER  { $$ = identifier_node($1, ZL); }
  | RAW_IDENTIFIER          { $$ = raw_identifier_node($1, ZL); }
  ;

constDecl
  : patternNoTopAlt COLON type_opt COLON expression EOS
    { $$ = const_decl($1, $3, $5, ZL); }
  | patternNoTopAlt COLONCOLON expression EOS
    { $$ = const_decl($1, NULL, $3, ZL); }
  ;

varDecl
  : patternNoTopAlt COLON type_opt EQ expression EOS
    { $$ = var_decl($1, $3, $5, ZL); }
  | patternNoTopAlt COLONEQ expression EOS
    { $$ = var_decl($1, NULL, $3, ZL); }
  ;

type_opt
  : /* empty */ { $$ = NULL; }
  | type_       { $$ = $1; }
  ;

/* =========================
   Statements & attributes
   ========================= */

statement
  : EOS                        { $$ = NULL; }
  | declaration                { $$ = $1; }
  | insertStatement            { $$ = $1; }
  | deferStatement             { $$ = $1; }
  | errdeferStatement          { $$ = $1; }
  | expressionStatement        { $$ = $1; }
  ;

expressionStatement
  : expression EOS             { $$ = $1; }
  | attr_block_expr EOS_opt    { $$ = $1; }
  ;

EOS_opt
  : /* empty */ { $$ = NULL; }
  | EOS         { $$ = NULL; }
  ;

insertStatement
  : INSERT expression EOS      { $$ = insert_stmt($2, ZL); }
  ;

deferStatement
  : DEFER expression EOS       { $$ = defer_stmt($2, ZL); }
  ;

errdeferStatement
  : ERRDEFER expression EOS    { $$ = errdefer_stmt($2, ZL); }
  ;

/* attributes: @[ a, b=1, ... ]  */
attribute
  : AT LSQUAREBRACKET attrs_opt RSQUAREBRACKET
    { $$ = $3; /* list itself */ }
  ;

attrs_opt
  : /* empty */            { $$ = NULL; }
  | attrs_opt attr         { $$ = attr_list_append($1, $2); }
  ;

attr
  : identifier EQ literalExpression  { $$ = attr_key_value($1, $3, ZL); }
  | identifier                       { $$ = attr_key($1, ZL); }
  ;

/* =========================
   Expression tower
   ========================= */

expression
  : assign_expr { $$ = $1; }
  ;

assign_expr
  : catch_expr                                      { $$ = $1; }
  | unary_expr EQ assign_expr                       { $$ = assign_expr($1, $3, ZL); }
  | unary_expr compoundAssignOperator assign_expr   { $$ = compound_assign_expr($1, $3, $2, ZL); }
  | CONTINUE label_opt expression_opt               { $$ = continue_expr($2, $3, ZL); }
  | BREAK    label_opt expression_opt               { $$ = break_expr($2, $3, ZL); }
  | RETURN   expression_opt                         { $$ = return_expr($2, ZL); }
  ;

compoundAssignOperator
  : PLUSEQ         { $$ = OP_ADD_ASSIGN; }
  | MINUSEQ        { $$ = OP_SUB_ASSIGN; }
  | STAREQ         { $$ = OP_MUL_ASSIGN; }
  | SLASHEQ        { $$ = OP_DIV_ASSIGN; }
  | PERCENTEQ      { $$ = OP_MOD_ASSIGN; }
  | ANDEQ          { $$ = OP_AND_ASSIGN; }
  | OREQ           { $$ = OP_OR_ASSIGN; }
  | CARETEQ        { $$ = OP_XOR_ASSIGN; }
  | SHLEQ          { $$ = OP_SHL_ASSIGN; }
  | SHREQ          { $$ = OP_SHR_ASSIGN; }
  | PLUSPIPEEQ     { $$ = OP_ADD_SAT_ASSIGN; }
  | MINUSPIPEEQ    { $$ = OP_SUB_SAT_ASSIGN; }
  | STARPIPEEQ     { $$ = OP_MUL_SAT_ASSIGN; }
  | SHLPIPEEQ      { $$ = OP_SHL_SAT_ASSIGN; }
  | PLUSPERCENTEQ  { $$ = OP_ADD_WRAP_ASSIGN; }
  | MINUSPERCENTEQ { $$ = OP_SUB_WRAP_ASSIGN; }
  | STARPERCENTEQ  { $$ = OP_MUL_WRAP_ASSIGN; }
  ;

catch_expr
  : orelse_expr                                           { $$ = $1; }
  | catch_expr CATCH catchBinder_opt orelse_expr          { $$ = catch_expr($1, $3, $4, ZL); }
  ;

catchBinder_opt
  : /* empty */                      { $$ = NULL; }
  | B_OR identifier B_OR             { $$ = $2; }
  ;

orelse_expr
  : range_expr                         { $$ = $1; }
  | orelse_expr ORELSE range_expr      { $$ = binary_expr($1, $3, OP_ORELSE, ZL); }
  ;

range_expr
  : or_expr                            { $$ = $1; }
  | or_expr DOTDOT expression_opt      { $$ = binary_expr($1, $3, OP_DOTDOT, ZL); }
  | DOTDOT expression_opt              { $$ = unary_expr($2, OP_DOTDOT, ZL); }
  | or_expr DOTDOTEQ or_expr           { $$ = binary_expr($1, $3, OP_DOTDOTEQ, ZL); }
  ;

or_expr
  : and_expr                     { $$ = $1; }
  | or_expr OR and_expr          { $$ = binary_expr($1, $3, OP_OR, ZL); }
  ;

and_expr
  : cmp_expr                     { $$ = $1; }
  | and_expr AND cmp_expr        { $$ = binary_expr($1, $3, OP_AND, ZL); }
  ;

comparisonOperator
  : EQEQ   { $$ = OP_EQ; }
  | NE     { $$ = OP_NEQ; }
  | GT     { $$ = OP_GT; }
  | LT     { $$ = OP_LT; }
  | GE     { $$ = OP_GTE; }
  | LE     { $$ = OP_LTE; }
  ;

cmp_expr
  : bitor_expr                                  { $$ = $1; }
  | cmp_expr comparisonOperator bitor_expr       { $$ = binary_expr($1, $3, $2, ZL); }
  ;

bitor_expr
  : xor_expr                    { $$ = $1; }
  | bitor_expr B_OR xor_expr    { $$ = binary_expr($1, $3, OP_BOR, ZL); }
  ;

xor_expr
  : bitand_expr                  { $$ = $1; }
  | xor_expr CARET bitand_expr   { $$ = binary_expr($1, $3, OP_BXOR, ZL); }
  ;

bitand_expr
  : shift_expr                    { $$ = $1; }
  | bitand_expr B_AND shift_expr  { $$ = binary_expr($1, $3, OP_BAND, ZL); }
  ;

shift_expr
  : add_expr                       { $$ = $1; }
  | shift_expr SHL add_expr        { $$ = binary_expr($1, $3, OP_SHL, ZL); }
  | shift_expr SHR add_expr        { $$ = binary_expr($1, $3, OP_SHR, ZL); }
  | shift_expr SHLPIPE add_expr    { $$ = binary_expr($1, $3, OP_SHL_SAT, ZL); }
  ;

add_expr
  : mul_expr                           { $$ = $1; }
  | add_expr PLUS         mul_expr     { $$ = binary_expr($1, $3, OP_ADD, ZL); }
  | add_expr MINUS        mul_expr     { $$ = binary_expr($1, $3, OP_SUB, ZL); }
  | add_expr PLUSPIPE     mul_expr     { $$ = binary_expr($1, $3, OP_ADD_SAT, ZL); }
  | add_expr MINUSPIPE    mul_expr     { $$ = binary_expr($1, $3, OP_SUB_SAT, ZL); }
  | add_expr PLUSPERCENT  mul_expr     { $$ = binary_expr($1, $3, OP_ADD_WRAP, ZL); }
  | add_expr MINUSPERCENT mul_expr     { $$ = binary_expr($1, $3, OP_SUB_WRAP, ZL); }
  ;

mul_expr
  : unary_expr                        { $$ = $1; }
  | mul_expr STAR        unary_expr   { $$ = binary_expr($1, $3, OP_MUL, ZL); }
  | mul_expr SLASH       unary_expr   { $$ = binary_expr($1, $3, OP_DIV, ZL); }
  | mul_expr PERCENT     unary_expr   { $$ = binary_expr($1, $3, OP_MOD, ZL); }
  | mul_expr STARPIPE    unary_expr   { $$ = binary_expr($1, $3, OP_MUL_SAT, ZL); }
  | mul_expr STARPERCENT unary_expr   { $$ = binary_expr($1, $3, OP_MUL_WRAP, ZL); }
  ;

unary_expr
  : postfix_expr                               { $$ = $1; }
  | B_AND  unary_expr      %prec UREF          { $$ = unary_expr($2, OP_ADDR, ZL); }
  | MINUS  unary_expr      %prec UMINUS_UBANG  { $$ = unary_expr($2, OP_NEG, ZL); }
  | BANG   unary_expr      %prec UMINUS_UBANG  { $$ = unary_expr($2, OP_NOT, ZL); }
  ;

postfix_expr
  : primary_expr                            { $$ = $1; }
  | postfix_expr DOT identifier             { $$ = field_access_expr($1, $3, ZL); }
  | postfix_expr DOT tupleIndex             { $$ = tuple_index_expr($1, $3, ZL); }
  | postfix_expr DOT AWAIT                  { $$ = await_expr($1, ZL); }
  | postfix_expr DOTLPAREN type_ RPAREN     { $$ = type_cast_expr($1, $3, ZL); }
  | postfix_expr DOT CARET    type_         { $$ = type_cast_expr($1, $4, ZL); }
  | postfix_expr DOT B_OR     type_         { $$ = type_cast_expr($1, $4, ZL); }
  | postfix_expr DOT PERCENT  type_         { $$ = type_cast_expr($1, $4, ZL); }
  | postfix_expr DOT QUESTION type_         { $$ = type_cast_expr($1, $4, ZL); }
  | postfix_expr LPAREN       callParams_opt RPAREN
    { $$ = call_expr($1, $3, ZL); }
  | postfix_expr LSQUAREBRACKET expression RSQUAREBRACKET
    { $$ = index_expr($1, $3, ZL); }
  | postfix_expr DOTSTAR                    { $$ = deref_expr($1, ZL); }
  | postfix_expr BANG        %prec UMINUS_UBANG
    { $$ = errorprop_expr($1, ZL); }
  ;

primary_expr
  : literalExpression                          { $$ = $1; }
  | identifier                                 { $$ = identifier_expr($1->data.identifier.name, ZL); }
  | LPAREN attribute_opt expression RPAREN     { $$ = grouped_expr($2, $3, ZL); }
  | DOTLSQUAREBRACKET attribute_opt collectionBody_opt RSQUAREBRACKET
    { $$ = array_literal($2, $3, ZL); }
  | DOTLPAREN        attribute_opt tupleElements_opt RPAREN
    { $$ = tuple_literal($2, $3, ZL); }
  | structExpression                           { $$ = $1; }
  | enumerationVariantExpression               { $$ = $1; }
  | closureExpression                          { $$ = $1; }
  | codeExpression                             { $$ = $1; }
  | mlirExpression                             { $$ = $1; }
  | asmExpression                              { $$ = $1; }
  | nullExpression                             { $$ = $1; }
  | undefinedExpression                        { $$ = $1; }
  | typeLiteralExpr                            { $$ = $1; }
  | importExpression                           { $$ = $1; }
  | attr_block_expr                            { $$ = $1; }
  | UNREACHABLE                                { $$ = unreachable_expr(ZL); }
  ;

attribute_opt
  : /* empty */  { $$ = NULL; }
  | attribute    { $$ = $1; }
  ;

collectionBody_opt
  : /* empty */      { $$ = NULL; }
  | collectionBody   { $$ = $1; }
  ;

tupleElements_opt
  : /* empty */   { $$ = NULL; }
  | tupleElements { $$ = $1; }
  ;

expression_opt
  : /* empty */  { $$ = NULL; }
  | expression   { $$ = $1; }
  ;

label_opt
  : /* empty */  { $$ = NULL; }
  | label        { $$ = $1; }
  ;

callParams_opt
  : /* empty */  { $$ = NULL; }
  | callParams   { $$ = $1; }
  ;

/* attribute* + a blocklike construct -> attr apply */
attr_block_expr
  : attribute_opt_list blocklike_expr
    { $$ = attr_apply($1, $2, ZL); }
  ;

attribute_opt_list
  : /* empty */                           { $$ = NULL; }
  | attribute_opt_list attribute          { $$ = attr_list_append($1, $2); }
  ;

blocklike_expr
  : blockExpression                    { $$ = $1; }
  | ASYNC blockExpression              { $$ = async_expression($2, ZL); }
  | loopExpression                     { $$ = $1; }
  | ifExpression                       { $$ = $1; }
  | matchExpression                    { $$ = $1; }
  | functionExpression                 { $$ = $1; }
  | procedureExpression                { $$ = $1; }
  | COMPTIME blockExpression           { $$ = comptime_expression($2, ZL); }
  | COMPTIME expression                { $$ = comptime_expression($2, ZL); }
  ;

label
  : COLON NON_KEYWORD_IDENTIFIER   { $$ = label_node($2, ZL); }
  ;

nullExpression
  : NULL_KW                       { $$ = null_expr(ZL); }
  ;

undefinedExpression
  : UNDEFINED                     { $$ = undefined_expr(ZL); }
  ;

/* =========================
   Functions / procedures
   ========================= */

functionExpression
  : functionQualifiers FN LPAREN functionParameters_opt RPAREN type_opt blockExpression
    { $$ = function_expression_node($1, $4, $6, $7, 0, ZL); }
  | functionQualifiers FN LPAREN functionParameters_opt RPAREN type_opt RAW_ASM_BLOCK
    { AstNode* body = asm_expression($7, ZL);
      $$ = function_expression_node($1, $4, $6, body, 1, ZL); }
  ;

procedureExpression
  : functionQualifiers PROC LPAREN functionParameters_opt RPAREN type_opt blockExpression
    { $$ = procedure_expression_node($1, $4, $6, $7, 0, ZL); }
  | functionQualifiers PROC LPAREN functionParameters_opt RPAREN type_opt RAW_ASM_BLOCK
    { AstNode* body = asm_expression($7, ZL);
      $$ = procedure_expression_node($1, $4, $6, body, 1, ZL); }
  ;

functionQualifiers
  : ASYNC_opt extern_opt       { $$ = func_qualifiers($1, $2, ZL); }
  ;

ASYNC_opt
  : /* empty */  { $$ = NULL; }
  | ASYNC        { $$ = async_qualifier(ZL); }
  ;

extern_opt
  : /* empty */            { $$ = NULL; }
  | EXTERN abi_opt         { $$ = extern_qualifier($2, ZL); }
  ;

abi_opt
  : /* empty */  { $$ = NULL; }
  | abi          { $$ = $1; }
  ;

functionParameters_opt
  : /* empty */          { $$ = NULL; }
  | functionParameters   { $$ = $1; }
  ;

functionParameters
  : functionParam_list COMMA_opt  { $$ = $1; }
  ;

functionParam_list
  : functionParam                           { $$ = function_parameters_append(NULL, $1); }
  | functionParam_list COMMA functionParam  { $$ = function_parameters_append($1, $3); }
  ;

functionParam
  : attribute_opt COMPTIME_opt functionParamPattern
    { $$ = function_param($1, $2, $3, ZL); }
  | attribute_opt COMPTIME_opt DOTDOTDOT
    { $$ = function_param($1, $2, new_node(NODE_ELLIPSIS, ZL), ZL); }
  | attribute_opt COMPTIME_opt type_
    { $$ = function_param($1, $2, $3, ZL); }
  ;

COMPTIME_opt
  : /* empty */ { $$ = NULL; }
  | COMPTIME    { $$ = comptime_qualifier(ZL); }
  ;

functionParamPattern
  : pattern COLON type_ eqExpr_opt
    { $$ = function_param_pattern($1, $3, $4, ZL); }
  | pattern COLON DOTDOTDOT eqExpr_opt
    { $$ = function_param_pattern($1, new_node(NODE_ELLIPSIS, ZL), $4, ZL); }
  ;

eqExpr_opt
  : /* empty */          { $$ = NULL; }
  | EQ expression        { $$ = eq_expr($2, ZL); }
  ;

/* =========================
   Literals, blocks, stmts
   ========================= */

literalExpression
  : CHAR_LITERAL                  { $$ = literal_node(NODE_CHAR_LITERAL, $1, ZL); }
  | STRING_LITERAL                { $$ = literal_node(NODE_STRING_LITERAL, $1, ZL); }
  | RAW_STRING_LITERAL            { $$ = literal_node(NODE_RAW_STRING_LITERAL, $1, ZL); }
  | BYTE_LITERAL                  { $$ = literal_node(NODE_BYTE_LITERAL, $1, ZL); }
  | BYTE_STRING_LITERAL           { $$ = literal_node(NODE_BYTE_STRING_LITERAL, $1, ZL); }
  | RAW_BYTE_STRING_LITERAL       { $$ = literal_node(NODE_RAW_BYTE_STRING_LITERAL, $1, ZL); }
  | INTEGER_LITERAL               { $$ = literal_node(NODE_INTEGER_LITERAL, $1, ZL); }
  | FLOAT_LITERAL                 { $$ = literal_node(NODE_FLOAT_LITERAL, $1, ZL); }
  | IMAGINARY_LITERAL             { $$ = literal_node(NODE_IMAGINARY_LITERAL, $1, ZL); }
  | TRUE                          { $$ = literal_node(NODE_BOOL_LITERAL, strdup("true"), ZL); }
  | FALSE                         { $$ = literal_node(NODE_BOOL_LITERAL, strdup("false"), ZL); }
  ;

blockExpression
  : LCURLYBRACE attribute_opt statements_opt RCURLYBRACE
    { $$ = block_expression($2, $3, ZL); }
  ;

statements_opt
  : /* empty */   { $$ = NULL; }
  | statements    { $$ = $1; }
  ;

statements
  : statement_plus expression_opt  { $$ = statement_list_append($1, $2); }
  | expression                     { $$ = statement_list_append(NULL, $1); }
  ;

statement_plus
  : statement                      { $$ = statement_list_append(NULL, $1); }
  | statement_plus statement       { $$ = statement_list_append($1, $2); }
  ;

/* =========================
   Collection bodies
   ========================= */

collectionBody
  : expression collectionTail_opt
    { $$ = collection_body($1, $2, ZL); }
  ;

collectionTail_opt
  : /* empty */   { $$ = NULL; }
  | restOfMap     { $$ = $1; }
  | restOfArray   { $$ = $1; }
  ;

restOfMap
  : COLON expression mapElement_seq_opt
    { $$ = map_tail($2, $3, ZL); }
  ;

mapElement_seq_opt
  : /* empty */               { $$ = NULL; }
  | mapElement_seq COMMA_opt  { $$ = $1; }
  ;

mapElement_seq
  : mapElement                        { $$ = map_element_list_append(NULL, $1); }
  | mapElement_seq COMMA mapElement   { $$ = map_element_list_append($1, $3); }
  ;

mapElement
  : expression COLON expression   { $$ = map_element($1, $3, ZL); }
  ;

// restOfArray
//   : restArr_seq_opt               { $$ = $1; }
//   | EOS expression                { $$ = array_rest_list_append(NULL, array_rest_element($2, ZL)); }
//   ;

restOfArray : restArr_seq COMMA_opt  { $$ = $1; }
            | EOS expression         { $$ = array_rest_list_append(NULL, array_rest_element($2, ZL)); }
            
            ;

restArr_seq
  : COMMA expression                { $$ = array_rest_list_append(NULL, array_rest_element($2, ZL)); }
  | restArr_seq COMMA expression    { $$ = array_rest_list_append($1, array_rest_element($3, ZL)); }
  ;

tupleElements
  : tuple_head expression_opt
    {
      AstNode* list = $1;
      if ($2) list = tuple_head_list_append(list, tuple_head_element($2, ZL));
      $$ = list;
    }
  ;

tuple_head
  : expression COMMA
    { $$ = tuple_head_list_append(NULL, tuple_head_element($1, ZL)); }
  | tuple_head expression COMMA
    { $$ = tuple_head_list_append($1,  tuple_head_element($2, ZL)); }
  ;

tupleIndex
  : INTEGER_LITERAL  { $$ = literal_node(NODE_INTEGER_LITERAL, $1, ZL); }
  ;

/* =========================
   Struct / enum variant expr
   ========================= */

structExpression
  : structExprStruct   { $$ = $1; }
  ;

structExprStruct
  : path LCURLYBRACE attribute_opt structStructTail_opt RCURLYBRACE
    {
      AstNode* fields = NULL; AstNode* base = NULL;
      if ($4 && $4->type == NODE_STRUCT_FIELD_LIST) fields = $4; else base = $4;
      $$ = struct_expression($1, $3, fields, base, ZL);
    }
  ;

structStructTail_opt
  : /* empty */          { $$ = NULL; }
  | structExprFields     { $$ = $1; }
  | structBase           { $$ = $1; }
  ;

structExprFields
  : structExprField_list structExprFieldsTail_opt
    { $$ = $1; /* base (if any) is handled in the caller */ }
  ;

structExprFieldsTail_opt
  : /* empty */                 { $$ = NULL; }
  | COMMA structBase            { $$ = $2; }
  | COMMA_opt                   { $$ = NULL; }
  ;

structExprField_list
  : structExprField                              { $$ = struct_field_list_append(NULL, $1); }
  | structExprField_list COMMA structExprField   { $$ = struct_field_list_append($1, $3); }
  ;

structExprField
  : attribute_opt identifier
    { $$ = struct_field($1, $2, 0, NULL, ZL); }
  | attribute_opt identifier COLON expression
    { $$ = struct_field($1, $2, 0, $4, ZL); }
  | attribute_opt tupleIndex COLON expression
    { $$ = struct_field($1, $2, 1, $4, ZL); }
  ;

structBase
  : DOTDOT expression  { $$ = struct_base($2, ZL); }
  ;

enumerationVariantExpression
  : enumExprStruct  { $$ = $1; }
  ;

// enumExprStruct
//   : path LCURLYBRACE enumExprFields_opt RCURLYBRACE
//     { $$ = enum_variant_expression($1, $3, ZL); }
//   ;

enumExprStruct
  : path LCURLYBRACE enumExprField_list COMMA_opt RCURLYBRACE
    { $$ = enum_variant_expression($1, $3, ZL); }
  | path LCURLYBRACE RCURLYBRACE
    { $$ = enum_variant_expression($1, NULL, ZL); }
  ;

enumExprField_list
  : enumExprField                           { $$ = enum_variant_field_list_append(NULL, $1); }
  | enumExprField_list COMMA enumExprField  { $$ = enum_variant_field_list_append($1, $3); }
  ;

enumExprField
  : identifier                    { $$ = enum_variant_field($1, 0, NULL, ZL); }
  | identifier COLON expression   { $$ = enum_variant_field($1, 0, $3, ZL); }
  | tupleIndex COLON expression   { $$ = enum_variant_field($1, 1, $3, ZL); }
  ;

callParams
  : expression_list COMMA_opt  { $$ = $1; }
  ;

/* =========================
   Closures
   ========================= */

closureExpression
  : PIPEPIPE expression
    { $$ = closure_expression(NULL, NULL, $2, 0, ZL); }
  | PIPEPIPE type_ blockExpression
    { $$ = closure_expression(NULL, $2, $3, 1, ZL); }
  | B_OR closureParameters_opt B_OR expression
    { $$ = closure_expression($2, NULL, $4, 0, ZL); }
  | B_OR closureParameters_opt B_OR type_ blockExpression
    { $$ = closure_expression($2, $4, $5, 1, ZL); }
  ;

closureParameters_opt
  : /* empty */         { $$ = NULL; }
  | closureParameters   { $$ = $1; }
  ;

closureParameters
  : closureParam_list COMMA_opt  { $$ = $1; }
  ;

closureParam_list
  : closureParam                          { $$ = closure_params_append(NULL, $1); }
  | closureParam_list COMMA closureParam  { $$ = closure_params_append($1, $3); }
  ;

closureParam
  : attribute_opt pattern typeAnn_opt
    { $$ = closure_param($1, $2, $3, ZL); }
  ;

typeAnn_opt
  : /* empty */     { $$ = NULL; }
  | COLON type_     { $$ = type_annotation($2, ZL); }
  ;

/* =========================
   Loops
   ========================= */

loopExpression
  : loopLabel_opt loopBody
    { $$ = $2; if ($$) $$->data.loopExpr.label = $1; }
  ;

loopLabel_opt
  : /* empty */ { $$ = NULL; }
  | loopLabel   { $$ = $1; }
  ;

loopBody
  : infiniteLoopExpression             { $$ = $1; }
  | predicateLoopExpression            { $$ = $1; }
  | predicatePatternLoopExpression     { $$ = $1; }
  | iteratorLoopExpression             { $$ = $1; }
  ;

infiniteLoopExpression
  : WHILE blockExpression
    { $$ = loop_expression_infinite(NULL, $2, ZL); }
  ;

predicateLoopExpression
  : WHILE expression blockExpression
    { $$ = loop_expression_predicate(NULL, $2, $3, ZL); }
  ;

predicatePatternLoopExpression
  : WHILE IS pattern COLONEQ expression blockExpression
    { $$ = loop_expression_predicate_pattern(NULL, $3, $5, $6, ZL); }
  ;

iteratorLoopExpression
  : FOR pattern IN expression blockExpression
    { $$ = loop_expression_iterator(NULL, $2, $4, $5, ZL); }
  ;

loopLabel
  : NON_KEYWORD_IDENTIFIER COLON
    { $$ = identifier_node($1, ZL); }
  ;

/* =========================
   Code / MLIR / ASM / import
   ========================= */

// codeExpression
//   : CODE LCURLYBRACE codeContent_opt RCURLYBRACE
//     { $$ = code_expression($3, ZL); }
//   ;


codeExpression :
  CODE LCURLYBRACE statements_opt RCURLYBRACE 
    { $$ = code_expression($3, ZL); }
  ;


mlirExpression
  : MLIR mlirHead_opt LCURLYBRACE mlirBody_opt RCURLYBRACE
    { $$ = mlir_expression($2, $4, ZL); }
  ;

mlirHead_opt
  : /* empty */   { $$ = NULL; }
  | TYPE          { $$ = type_path(path_single(identifier_node("type", ZL), ZL), ZL); }
  | identifier    { $$ = $1; }
  ;

mlirBody_opt
  : /* empty */  { $$ = NULL; }
  ;

asmExpression
  : RAW_ASM_BLOCK  { $$ = asm_expression($1, ZL); }
  ;

importExpression
  : IMPORT path    { $$ = import_expression($2, ZL); }
  ;

/* =========================
   If / match
   ========================= */

ifExpression
  : IF expression blockExpression elseTail_opt
    { $$ = if_expression($2, $3, $4, ZL); }
  ;

elseTail_opt
  : /* empty */           { $$ = NULL; }
  | ELSE blockExpression  { $$ = $2; }
  | ELSE ifExpression     { $$ = $2; }
  ;

matchExpression
  : MATCH expression LCURLYBRACE attribute_opt matchArms_opt RCURLYBRACE
    { $$ = match_expression($2, $4, $5, ZL); }
  ;

matchArms_opt
  : /* empty */  { $$ = NULL; }
  | matchArms    { $$ = $1; }
  ;

matchArms
  : matchArm FATARROW matchRHS COMMA matchArms
    { AstNode* arm = match_arm($1->data.matchArm.attr, $1, $3, ZL); $$ = match_arm_list_append($5, arm); }
  | matchArm FATARROW matchRHS COMMA
    { AstNode* arm = match_arm($1->data.matchArm.attr, $1, $3, ZL); $$ = match_arm_list_append(NULL, arm); }
  ;

matchRHS
  : expression       { $$ = $1; }
  ;

matchArm
  : attribute_opt pattern matchArmGuard_opt
    { AstNode* head = match_arm_head($2, $3, ZL); head->data.matchArm.attr = $1; $$ = head; }
  ;

matchArmGuard_opt
  : /* empty */     { $$ = NULL; }
  | IF expression   { $$ = match_guard($2, ZL); }
  ;

/* =========================
   Patterns
   ========================= */

pattern
  : patternNoTopAlt patternAltTail_opt
    { $$ = ($2 ? binary_expr($1, $2, OP_BOR, ZL) : $1); }
  ;

patternAltTail_opt
  : /* empty */                                  { $$ = NULL; }
  | patternAltTail_opt B_OR patternNoTopAlt      { $$ = ($1 ? binary_expr($1, $3, OP_BOR, ZL) : $3); }
  ;

patternNoTopAlt
  : patternWithoutRange  { $$ = $1; }
  | rangePattern         { $$ = $1; }
  ;

patternWithoutRange
  : literalPattern       { $$ = $1; }
  | identifierPattern    { $$ = $1; }
  | wildcardPattern      { $$ = $1; }
  | restPattern          { $$ = $1; }
  | structPattern        { $$ = $1; }
  | tupleStructPattern   { $$ = $1; }
  | tuplePattern         { $$ = $1; }
  | groupedPattern       { $$ = $1; }
  | slicePattern         { $$ = $1; }
  | pathPattern          { $$ = $1; }
  ;

literalPattern
  : TRUE                          { $$ = pattern_literal(literal_node(NODE_BOOL_LITERAL, strdup("true"), ZL), ZL); }
  | FALSE                         { $$ = pattern_literal(literal_node(NODE_BOOL_LITERAL, strdup("false"), ZL), ZL); }
  | CHAR_LITERAL                  { $$ = pattern_literal(literal_node(NODE_CHAR_LITERAL, $1, ZL), ZL); }
  | BYTE_LITERAL                  { $$ = pattern_literal(literal_node(NODE_BYTE_LITERAL, $1, ZL), ZL); }
  | STRING_LITERAL                { $$ = pattern_literal(literal_node(NODE_STRING_LITERAL, $1, ZL), ZL); }
  | RAW_STRING_LITERAL            { $$ = pattern_literal(literal_node(NODE_RAW_STRING_LITERAL, $1, ZL), ZL); }
  | BYTE_STRING_LITERAL           { $$ = pattern_literal(literal_node(NODE_BYTE_STRING_LITERAL, $1, ZL), ZL); }
  | RAW_BYTE_STRING_LITERAL       { $$ = pattern_literal(literal_node(NODE_RAW_BYTE_STRING_LITERAL, $1, ZL), ZL); }
  | MINUS_opt INTEGER_LITERAL
    { AstNode* lit = literal_node(NODE_INTEGER_LITERAL, $2, ZL); $$ = $1 ? pattern_literal(unary_expr(lit, OP_NEG, ZL), ZL) : pattern_literal(lit, ZL); }
  | MINUS_opt FLOAT_LITERAL
    { AstNode* lit = literal_node(NODE_FLOAT_LITERAL, $2, ZL); $$ = $1 ? pattern_literal(unary_expr(lit, OP_NEG, ZL), ZL) : pattern_literal(lit, ZL); }
  | IMAGINARY_LITERAL
    { $$ = pattern_literal(literal_node(NODE_IMAGINARY_LITERAL, $1, ZL), ZL); }
  ;

MINUS_opt
  : /* empty */ { $$ = 0; }
  | MINUS       { $$ = 1; }
  ;

identifierPattern
  : identifier atTail_opt
    { $$ = pattern_identifier($1, $2, ZL); }
  ;

atTail_opt
  : /* empty */     { $$ = NULL; }
  | AT pattern      { $$ = $2; }
  ;

wildcardPattern
  : UNDERSCORE      { $$ = pattern_wildcard(ZL); }
  ;

restPattern
  : DOTDOT          { $$ = pattern_rest(ZL); }
  ;

rangePattern
  : rangePatternBound DOTDOTEQ rangePatternBound
    { $$ = pattern_range(RANGE_CLOSED, $1, $3, ZL); }
  | rangePatternBound DOTDOT rangePatternBound
    { $$ = pattern_range(RANGE_HALF_OPEN, $1, $3, ZL); }
  | rangePatternBound DOTDOT
    { $$ = pattern_range(RANGE_FROM, $1, NULL, ZL); }
  | DOTDOT rangePatternBound
    { $$ = pattern_range(RANGE_TO, NULL, $2, ZL); }
  ;

rangePatternBound
  : CHAR_LITERAL     { $$ = literal_node(NODE_CHAR_LITERAL, $1, ZL); }
  | BYTE_LITERAL     { $$ = literal_node(NODE_BYTE_LITERAL, $1, ZL); }
  | MINUS_opt INTEGER_LITERAL
    { AstNode* lit = literal_node(NODE_INTEGER_LITERAL, $2, ZL); $$ = $1 ? unary_expr(lit, OP_NEG, ZL) : lit; }
  | MINUS_opt FLOAT_LITERAL
    { AstNode* lit = literal_node(NODE_FLOAT_LITERAL, $2, ZL); $$ = $1 ? unary_expr(lit, OP_NEG, ZL) : lit; }
  | pathPattern      { $$ = $1; }
  ;


structPattern
  : path LCURLYBRACE structPatternElements_opt RCURLYBRACE
    {
      AstNode *fields = NULL;
      int has_etc = 0;
      if ($3 && $3->type == NODE_PATTERN_STRUCT_ELEMS) {
        fields = $3->data.patStructElems.fields;
        has_etc = $3->data.patStructElems.has_etc;
      }
      $$ = pattern_struct($1, fields, has_etc, ZL);
    }
  ;

// structPattern
//   : path LCURLYBRACE structPatternElements_opt RCURLYBRACE
//     { $$ = pattern_struct($1, $3, 0, ZL); }
//   ;

structPatternElements_opt
  : /* empty */            { $$ = NULL; }
  | structPatternElements  { $$ = $1; }
  ;

structPatternElements
  : structPatternFields structPatEtcTail_opt
    { int has_etc = ($2 != NULL); $$ = pattern_struct_elems($1, has_etc, ZL); }
  | structPatternEtCetera
    { $$ = pattern_struct_elems(NULL, 1, ZL); }
  ;

structPatEtcTail_opt
  : /* empty */                       { $$ = NULL; }
  | COMMA structPatternEtCetera_opt   { $$ = $2; }
  ;

structPatternEtCetera_opt
  : /* empty */          { $$ = NULL; }
  | structPatternEtCetera{ $$ = $1; }
  ;

structPatternFields
  : structPatternField_list  { $$ = $1; }
  ;

structPatternField_list
  : structPatternField                              { $$ = pattern_struct_field_list_append(NULL, $1); }
  | structPatternField_list COMMA structPatternField{ $$ = pattern_struct_field_list_append($1, $3); }
  ;

structPatternField
  : attribute_opt tupleIndex COLON pattern
    { $$ = pattern_struct_field($1, $2, 1, $4, ZL); }
  | attribute_opt identifier COLON pattern
    { $$ = pattern_struct_field($1, $2, 0, $4, ZL); }
  | attribute_opt identifier
    { $$ = pattern_struct_field($1, $2, 0, NULL, ZL); }
  ;

structPatternEtCetera
  : attribute_opt DOTDOT  { (void)$1; $$ = new_node(NODE_PATTERN_REST, ZL); }
  ;

tupleStructPattern
  : path LPAREN tupleStructItems_opt RPAREN
    { $$ = pattern_tuple_struct($1, $3, ZL); }
  ;

tupleStructItems_opt
  : /* empty */          { $$ = NULL; }
  | tupleStructItems     { $$ = $1; }
  ;

tupleStructItems
  : pattern_list COMMA_opt   { $$ = $1; }
  ;

tuplePattern
  : LPAREN tuplePatternItems_opt RPAREN
    { $$ = pattern_tuple($2, ZL); }
  ;

tuplePatternItems_opt
  : /* empty */         { $$ = NULL; }
  | tuplePatternItems   { $$ = $1; }
  ;

// tuplePatternItems
//   : pattern COMMA                 { $$ = expr_list_append(NULL, $1); }
//   | restPattern                   { $$ = expr_list_append(NULL, $1); }
//   | pattern_list COMMA_opt        { $$ = $1; }
//   ;

tuplePatList
  : pattern
    { $$ = expr_list_append(NULL, $1); }
  | tuplePatList COMMA pattern
    { $$ = expr_list_append($1, $3); }
  ;

tuplePatternItems
  : tuplePatList COMMA
    { $$ = $1; }                    
  | restPattern
    { $$ = expr_list_append(NULL, $1); }   
  ;

/* grouped patterns cannot be a bare `..` */
groupedPattern
  : LPAREN patternNoTopAlt_noRest RPAREN  { $$ = pattern_grouped($2, ZL); }
  ;

patternNoTopAlt_noRest
  : patternWithoutRange_noRest  { $$ = $1; }
  | rangePattern                { $$ = $1; }
  ;

patternWithoutRange_noRest
  : literalPattern         { $$ = $1; }
  | identifierPattern      { $$ = $1; }
  | wildcardPattern        { $$ = $1; }
  | structPattern          { $$ = $1; } 
  | tupleStructPattern     { $$ = $1; }
  | tuplePattern           { $$ = $1; }
  | groupedPattern         { $$ = $1; }
  | slicePattern           { $$ = $1; }
  | pathPattern            { $$ = $1; }
  ;

slicePattern
  : LSQUAREBRACKET slicePatternItems_opt RSQUAREBRACKET
    { $$ = pattern_slice($2, ZL); }
  ;

slicePatternItems_opt
  : /* empty */       { $$ = NULL; }
  | slicePatternItems { $$ = $1; }
  ;

slicePatternItems
  : pattern_list COMMA_opt { $$ = $1; }
  ;

pathPattern
  : path_ndot    { $$ = pattern_path($1, ZL); }
  ;

/* =========================
   Types
   ========================= */

type_ : typeAtom
      | typeAtom BANG typeAtom
      ;

// type_
//   : typeAtom typeBang_opt
//     {
//       if ($2) {
//         AstNode* tup = type_tuple_append(NULL, $1);
//         tup = type_tuple_append(tup, $2);
//         $$ = tup;
//       } else $$ = $1;
//     }
//   ;

typeAtom
  : parenthesizedType     { $$ = $1; }
  | path                  { $$ = type_path($1, ZL); }
  | tupleType             { $$ = $1; }
  | noreturnType          { $$ = $1; }
  | rawPointerType        { $$ = $1; }
  | arrayType             { $$ = $1; }
  | dynamicArrayType      { $$ = $1; }
  | sliceType             { $$ = $1; }
  | mapType               { $$ = $1; }
  | optionalType          { $$ = $1; }
  | errorType             { $$ = $1; }
  | simdType              { $$ = $1; }
  | complexType           { $$ = $1; }
  | tensorType            { $$ = $1; }
  | inferredType          { $$ = $1; }
  | structType            { $$ = $1; }
  | enumType              { $$ = $1; }
  | variantType           { $$ = $1; }
  | unionType             { $$ = $1; }
  | bareFunctionType      { $$ = $1; }
  | TYPE                  { $$ = type_path(path_single(identifier_node("type", ZL), ZL), ZL); }
  ;

type_exprable
  : noreturnType
  | rawPointerType
  | arrayType
  | dynamicArrayType
  | sliceType
  | mapType
  | optionalType
  | errorType
  | simdType
  | complexType
  | tensorType
  | inferredType
  | structType
  | enumType
  | variantType
  | unionType
  | bareFunctionType
  | TYPE    { $$ = type_path(path_single(identifier_node("type", ZL), ZL), ZL); }
  ;

typeLiteralExpr
  : type_exprable  { $$ = $1; }
  ;

parenthesizedType
  : LPAREN type_ RPAREN  { $$ = type_paren($2, ZL); }
  ;

noreturnType
  : NORETURN  { $$ = type_noreturn(ZL); }
  ;

tupleType
  : LPAREN tupleTypeTail_opt RPAREN
    { $$ = $2 ? $2 : type_tuple_append(NULL, NULL); }
  ;

tupleTypeTail_opt
  : /* empty */                                    { $$ = NULL; }
  | type_ COMMA type_list COMMA_opt
    { AstNode* list = type_tuple_append(NULL, $1);
      AstNode* cur = $3;
      if (cur && cur->type == NODE_TYPE_TUPLE) {
        for (size_t i=0;i<cur->data.tTuple.list.count;i++)
          list = type_tuple_append(list, cur->data.tTuple.list.items[i]);
      } else {
        list = type_tuple_append(list, cur);
      }
      $$ = list;
    }
  ;

arrayType
  : LSQUAREBRACKET expression RSQUAREBRACKET type_
    { $$ = type_array($2, $4, ZL); }
  ;

dynamicArrayType
  : LSQUAREBRACKET DYN RSQUAREBRACKET type_
    { $$ = type_dynamic_array($4, ZL); }
  ;

sliceType
  : LSQUAREBRACKET RSQUAREBRACKET type_
    { $$ = type_slice($3, ZL); }
  ;

mapType
  : LSQUAREBRACKET type_ COLON type_ RSQUAREBRACKET
    { $$ = type_map($2, $4, ZL); }
  ;

optionalType
  : QUESTION type_   { $$ = type_optional($2, ZL); }
  ;

errorType
  : ERROR LCURLYBRACE variantItems_opt declarations_opt RCURLYBRACE
    { $$ = type_error($3, $4, ZL); }
  ;

structType
  : STRUCT structTypeTail_opt
    { $$ = $2 ? $2 : type_struct(NULL, NULL, ZL); }
  ;

structTypeTail_opt
  : /* empty */  { $$ = NULL; }
  | LCURLYBRACE structFields_opt declarations_opt RCURLYBRACE
    { $$ = type_struct($2, $3, ZL); }
  ;

structFields_opt
  : /* empty */  { $$ = NULL; }
  | structFields { $$ = $1; }
  ;

structFields
  : structField_list COMMA_opt  { $$ = $1; }
  ;

structField_list
  : structField                           { $$ = type_struct_field_list_append(NULL, $1); }
  | structField_list COMMA structField    { $$ = type_struct_field_list_append($1, $3); }
  ;

structField
  : attribute_opt PUB_opt identifier COLON type_
    { $$ = type_struct_field($1, $2 ? 1 : 0, $3, $5, ZL); }
  ;

PUB_opt
  : /* empty */  { $$ = NULL; }
  | PUB          { $$ = (AstNode*)1; }
  ;

enumType
  : ENUM parenthesizedType_opt LCURLYBRACE enumItems_opt declarations_opt RCURLYBRACE
    { $$ = type_enum($2, $4, $5, ZL); }
  ;

parenthesizedType_opt
  : /* empty */      { $$ = NULL; }
  | parenthesizedType{ $$ = $1; }
  ;

enumItems_opt
  : /* empty */  { $$ = NULL; }
  | enumItems    { $$ = $1; }
  ;

enumItems
  : enumItem_list COMMA_opt  { $$ = $1; }
  ;

enumItem_list
  : enumItem                        { $$ = type_enum_item_list_append(NULL, $1); }
  | enumItem_list COMMA enumItem    { $$ = type_enum_item_list_append($1, $3); }
  ;

enumItem
  : attribute_opt PUB_opt identifier enumItemTail_opt
    { $$ = type_enum_item($1, $2?1:0, $3, $4, ZL); }
  ;

enumItemTail_opt
  : /* empty */             { $$ = NULL; }
  | enumItemDiscriminant    { $$ = $1; }
  ;

variantType
  : VARIANT LCURLYBRACE variantItems_opt declarations_opt RCURLYBRACE
    { $$ = type_variant($3, $4, ZL); }
  ;

variantItems_opt
  : /* empty */  { $$ = NULL; }
  | variantItems { $$ = $1; }
  ;

variantItems
  : variantItem_list COMMA_opt  { $$ = $1; }
  ;

variantItem_list
  : variantItem                          { $$ = type_variant_item_list_append(NULL, $1); }
  | variantItem_list COMMA variantItem   { $$ = type_variant_item_list_append($1, $3); }
  ;

variantItem
  : attribute_opt PUB_opt identifier variantBody_opt
    { $$ = type_variant_item($1, $2?1:0, $3, $4, ZL); }
  ;

variantBody_opt
  : /* empty */     { $$ = NULL; }
  | enumItemStruct  { $$ = $1; }
  | enumItemTuple   { $$ = $1; }
  | enumItemDiscriminant { $$ = $1; }
  ;

enumItemTuple
  : LPAREN tupleFields_opt RPAREN
    { $$ = $2 ? $2 : type_tuple_append(NULL, NULL); }
  ;

enumItemStruct
  : LCURLYBRACE structFields_opt RCURLYBRACE
    { $$ = $2; }
  ;

enumItemDiscriminant
  : EQ expression   { $$ = $2; }
  ;

tupleFields_opt
  : /* empty */   { $$ = NULL; }
  | tupleFields   { $$ = $1; }
  ;

tupleFields
  : tupleField_list COMMA_opt  { $$ = $1; }
  ;

tupleField_list
  : tupleField                          { $$ = type_tuple_append(NULL, $1); }
  | tupleField_list COMMA tupleField    { $$ = type_tuple_append($1, $3); }
  ;

tupleField
  : attribute_opt PUB_opt type_
    { (void)$1; (void)$2; $$ = $3; }
  ;

unionType
  : UNION LCURLYBRACE structFields_opt declarations_opt RCURLYBRACE
    { $$ = type_union($3, $4, ZL); }
  ;

simdType
  : SIMD LPAREN expression COMMA type_ RPAREN
    { $$ = type_simd($3, $5, ZL); }
  ;

complexType
  : COMPLEX LPAREN type_ RPAREN
    { $$ = type_complex($3, ZL); }
  ;

tensorType
  : TENSOR LPAREN tensorDims COMMA type_ RPAREN
    { $3->data.tTensor.elem = $5; $$ = $3; }
  ;

tensorDims
  : INTEGER_LITERAL
    { AstNode* t = type_tensor_new(NULL, ZL);
      t = type_tensor_dims_append(t, literal_node(NODE_INTEGER_LITERAL, $1, ZL));
      $$ = t;
    }
  | tensorDims COMMA INTEGER_LITERAL
    { $$ = type_tensor_dims_append($1, literal_node(NODE_INTEGER_LITERAL, $3, ZL)); }
  | tensorDims COMMA
    { $$ = $1; }
  ;

rawPointerType
  : STAR CONST_opt type_
    { $$ = type_raw_pointer($2?1:0, $3, ZL); }
  ;

CONST_opt
  : /* empty */  { $$ = NULL; }
  | CONST        { $$ = (AstNode*)1; }
  ;

bareFunctionType
  : functionTypeQualifiers FN LPAREN functionParametersMaybeNamedVariadic_opt RPAREN type_opt
    { $$ = type_bare_function($1, $4, $6, ZL); }
  ;

functionTypeQualifiers
  : extern_opt { $$ = $1; }
  ;

abi
  : STRING_LITERAL      { $$ = abi_node($1, ZL); }
  | RAW_STRING_LITERAL  { $$ = abi_node($1, ZL); }
  ;

functionParametersMaybeNamedVariadic_opt
  : /* empty */                         { $$ = NULL; }
  | functionParametersMaybeNamedVariadic{ $$ = $1; }
  ;

functionParametersMaybeNamedVariadic
  : maybeNamedFunctionParameters            { $$ = $1; }
  | maybeNamedFunctionParametersVariadic    { $$ = $1; }
  ;

maybeNamedFunctionParameters
  : maybeNamedParam_list COMMA_opt  { $$ = $1; }
  ;

maybeNamedParam_list
  : maybeNamedParam                            { $$ = type_maybe_named_param_list_append(type_maybe_named_param_list_new(ZL), $1); }
  | maybeNamedParam_list COMMA maybeNamedParam { $$ = type_maybe_named_param_list_append($1, $3); }
  ;

maybeNamedParam
  : attribute_opt maybeName_opt type_
    { $$ = type_maybe_named_param($1, $2.name, $2.is_underscore, $3, ZL); }
  ;

maybeName_opt
  : /* empty */                 { $$ = (MaybeName){ NULL, 0 }; }
  | identifier COLON            { $$ = (MaybeName){ $1, 0 }; }
  | UNDERSCORE COLON            { $$ = (MaybeName){ NULL, 1 }; }
  ;

maybeNamedFunctionParametersVariadic
  : maybeNamedParam_list COMMA attribute_opt DOTDOTDOT
    { AstNode* list = $1 ? $1 : type_maybe_named_param_list_new(ZL);
      $$ = type_maybe_named_param_list_set_variadic(list, $3);
    }
  ;

inferredType
  : ANY   { $$ = type_inferred(ZL); }
  ;

/* =========================
   Paths
   ========================= */

path
  : identifier                { $$ = path_single($1, ZL); }
  | path DOT identifier       { $$ = path_append($1, $3); }
  ;

path_ndot
  : identifier DOT identifier { $$ = path_append(path_single($1, ZL), $3); }
  | path_ndot DOT identifier  { $$ = path_append($1, $3); }
  ;

/* =========================
   Generic lists
   ========================= */

expression_list
  : expression                          { $$ = expr_list_append(NULL, $1); }
  | expression_list COMMA expression    { $$ = expr_list_append($1, $3); }
  ;

pattern_list
  : pattern                         { $$ = expr_list_append(NULL, $1); }
  | pattern_list COMMA pattern      { $$ = expr_list_append($1, $3); }
  ;

type_list
  : type_                      { $$ = type_tuple_append(NULL, $1); }
  | type_list COMMA type_      { $$ = type_tuple_append($1, $3); }
  ;

COMMA_opt
  : /* empty */ { $$ = NULL; }
  | COMMA       { $$ = NULL; }
  ;

%%

void yyerror(const char* s){ fprintf(stderr,"%s\n",s); }

#ifdef YYDEBUG
extern int yydebug;
#endif
extern int yy_flex_debug;

int main(int argc, char** argv){
  if (argc > 1) {
    extern FILE* yyin;
    yyin = fopen(argv[1], "r");
    if (!yyin) { perror(argv[1]); return 1; }
  }
 #ifdef YYDEBUG
   yydebug = 0;
 #endif
   yy_flex_debug = 0;
  int rc = yyparse();
  extern AstNode *ast_root;
  if (ast_root) {
    extern void ast_print(const AstNode *root, FILE *out);
    ast_print(ast_root, stdout);
  }
  return rc;
}

