parser grammar Parser;

options {
    tokenVocab = Lexer;
}

program : packageDecl? (declaration)*  EOF;

packageDecl
    : PACKAGE identifier EOS
    ;

declaration
    : constDecl
    | varDecl
    ;

identifier : NON_KEYWORD_IDENTIFIER | RAW_IDENTIFIER ;

constDecl : patternNoTopAlt (COLON (type_)? COLON | COLONCOLON) expression EOS;
varDecl   : patternNoTopAlt (COLON (type_)? EQ | COLONEQ) expression EOS;

statement :
     EOS
    | declaration
    | insertStatement
    | deferStatement
    | errdeferStatement
    | expressionStatement
    ;

expressionStatement : expression EOS
    | expressionWithBlock EOS?
    ;

insertStatement
    : INSERT expression EOS
    ;

unreachableExpression
    : UNREACHABLE
    ;

deferStatement
    : DEFER expression EOS
    ;

errdeferStatement
    : ERRDEFER expression EOS
    ;

attribute
    : AT LSQUAREBRACKET attr* RSQUAREBRACKET
    ;
attr
    : identifier EQ literalExpression
    | identifier
    ;


expression
    : literalExpression                                              # LiteralExpression_
    | identifier                                                     # NameExpression
    | expression DOT identifier LPAREN callParams? RPAREN            # MethodCallExpression
    | expression DOT identifier                                      # FieldExpression
    | expression DOT tupleIndex                                      # TupleIndexingExpression
    | expression DOT AWAIT                                           # AwaitExpression
    | expression DOTLPAREN type_ RPAREN                              # TypeCastExpression
    | expression DOT CARET type_                                     # BitCastExpression
    | expression DOT B_OR type_                                      # SaturatingCastExpression
    | expression DOT PERCENT type_                                   # WrappingCastExpression
    | expression DOT QUESTION type_                                  # CheckedCastExpression
    | expression LPAREN callParams? RPAREN                           # CallExpression
    | expression LSQUAREBRACKET expression RSQUAREBRACKET            # IndexExpression
    | B_AND expression                                               # ReferenceExpression
    | expression BANG                                                # ErrorPropagationExpression
    | expression DOTSTAR                                             # DereferenceExpression
    | (MINUS | BANG) expression                                      # NegationExpression
    | expression (STAR | SLASH | PERCENT | STARPIPE | STARPERCENT) expression # ArithmeticOrLogicalExpression
    | expression (PLUS | MINUS | PLUSPIPE | MINUSPIPE | PLUSPERCENT | MINUSPERCENT) expression # ArithmeticOrLogicalExpression
    | expression (SHL | SHR | SHLPIPE) expression                    # ArithmeticOrLogicalExpression
    | expression B_AND expression                                    # ArithmeticOrLogicalExpression
    | expression CARET expression                                    # ArithmeticOrLogicalExpression
    | expression B_OR expression                                     # ArithmeticOrLogicalExpression
    | expression comparisonOperator expression                       # ComparisonExpression
    | expression AND expression                                      # LazyBooleanExpression
    | expression OR expression                                       # LazyBooleanExpression
    | expression DOTDOT expression?                                  # RangeExpression
    | DOTDOT expression?                                             # RangeExpression
    | DOTDOTEQ expression                                            # RangeExpression
    | expression DOTDOTEQ expression                                 # RangeExpression
    | expression EQ expression                                       # AssignmentExpression
    | expression compoundAssignOperator expression                   # CompoundAssignmentExpression
    | CONTINUE label? expression?                                    # ContinueExpression
    | BREAK label? expression?                                       # BreakExpression
    | RETURN expression?                                             # ReturnExpression
    | LPAREN attribute* expression RPAREN                            # GroupedExpression
    | DOTLSQUAREBRACKET attribute* collectionBody? RSQUAREBRACKET    # CollectionExpression
    | DOTLPAREN attribute* tupleElements? RPAREN                     # TupleExpression
    | structExpression                                               # StructExpression_
    | enumerationVariantExpression                                   # EnumerationVariantExpression_
    | closureExpression                                              # ClosureExpression_
    | expressionWithBlock                                            # ExpressionWithBlock_
    | codeExpression                                                 # CodeExpression_
    | mlirExpression                                                 # MlirExpression_
    | asmExpression                                                  # AsmExpression_
    | expression ORELSE expression                                   # OrElseExpression
    | expression CATCH (B_OR identifier B_OR)? expression            # CatchExpression
    | importExpression                                               # ImportExpression_
    | unreachableExpression                                          # UnreachableExpression_
    | nullExpression                                                 # NullExpression_
    | undefinedExpression                                            # UndefinedExpression_
    | typeExpression                                                 # TypeExpression_
    ;

label : COLON NON_KEYWORD_IDENTIFIER ;

nullExpression
    : NULL
    ;

undefinedExpression
    : UNDEFINED
    ;

comparisonOperator
    : EQEQ
    | NE
    | GT
    | LT
    | GE
    | LE
    ;

compoundAssignOperator
    : PLUSEQ
    | MINUSEQ
    | STAREQ
    | SLASHEQ
    | PERCENTEQ
    | ANDEQ
    | OREQ
    | CARETEQ
    | SHLEQ
    | SHREQ
    | PLUSPIPEEQ
    | MINUSPIPEEQ
    | STARPIPEEQ
    | SHLPIPEEQ
    | PLUSPERCENTEQ
    | MINUSPERCENTEQ
    | STARPERCENTEQ
    ;

expressionWithBlock
    : attribute+ expressionWithBlock
    | blockExpression
    | asyncBlockExpression
    | loopExpression
    | ifExpression
    | matchExpression
    | functionExpression
    | procedureExpression
    | comptimeExpression
    ;

functionExpression
    : functionQualifiers FN LPAREN functionParameters? RPAREN type_? (
        blockExpression
        | RAW_ASM_BLOCK
        // | EOS
    )
    ;

procedureExpression
    : functionQualifiers PROC LPAREN functionParameters? RPAREN type_? (
        blockExpression
        | RAW_ASM_BLOCK
        // | EOS
    )
    ;

functionQualifiers
    : ASYNC? (EXTERN abi?)?
    ;


functionParameters
    : functionParam (COMMA functionParam)* COMMA?
    ;

functionParam
    : attribute* COMPTIME? (functionParamPattern | DOTDOTDOT | type_)
    ;

functionParamPattern
    : pattern COLON (type_ | DOTDOTDOT) (EQ expression)?
    ;



literalExpression
    : CHAR_LITERAL
    | STRING_LITERAL
    | RAW_STRING_LITERAL
    | BYTE_LITERAL
    | BYTE_STRING_LITERAL
    | RAW_BYTE_STRING_LITERAL
    | INTEGER_LITERAL
    | FLOAT_LITERAL
    | IMAGINARY_LITERAL
    | TRUE
    | FALSE
    ;


blockExpression
    : LCURLYBRACE attribute* statements? RCURLYBRACE
    ;

statements
    : statement+ expression?
    | expression
    ;

asyncBlockExpression
    : ASYNC blockExpression
    ;

collectionBody
    : expression (restOfMap | restOfArray)?
    ;

restOfMap
    : COLON expression (COMMA mapElement)* COMMA?
    ;

mapElement
    : expression COLON expression
    ;

restOfArray
    : (COMMA expression)* COMMA?
    | EOS expression
    ;

tupleElements
    : (expression COMMA)+ expression?
    ;

tupleIndex
    : INTEGER_LITERAL
    ;

structExpression
    : structExprStruct
    | structExprTuple
    | structExprUnit
    ;

structExprStruct
    : dottedName LCURLYBRACE attribute* (structExprFields | structBase)? RCURLYBRACE
    ;

structExprFields
    : structExprField (COMMA structExprField)* (COMMA structBase | COMMA?)
    ;

structExprField
    : attribute* (identifier | (identifier | tupleIndex) COLON expression)
    ;

structBase
    : DOTDOT expression
    ;

structExprTuple
    : dottedName LPAREN attribute* (expression ( COMMA expression)* COMMA?)? RPAREN
    ;

structExprUnit
    : dottedName
    ;

enumerationVariantExpression
    : enumExprStruct
    | enumExprTuple
    | enumExprFieldless
    ;

enumExprStruct
    : dottedName LCURLYBRACE enumExprFields? RCURLYBRACE
    ;

enumExprFields
    : enumExprField (COMMA enumExprField)* COMMA?
    ;

enumExprField
    : identifier
    | (identifier | tupleIndex) COLON expression
    ;

enumExprTuple
    : dottedName LPAREN (expression (COMMA expression)* COMMA?)? RPAREN
    ;

enumExprFieldless
    : dottedName
    ;

callParams
    : expression (COMMA expression)* COMMA?
    ;

closureExpression
    : (PIPEPIPE | B_OR closureParameters? B_OR) (expression | type_ blockExpression)
    ;

closureParameters
    : closureParam (COMMA closureParam)* COMMA?
    ;

closureParam
    : attribute* pattern (COLON type_)?
    ;

loopExpression
    : loopLabel? (
        infiniteLoopExpression
        | predicateLoopExpression
        | predicatePatternLoopExpression
        | iteratorLoopExpression
    )
    ;

infiniteLoopExpression
    : WHILE blockExpression
    ;

predicateLoopExpression
    : WHILE expression /*except structExpression*/ blockExpression
    ;

predicatePatternLoopExpression
    : WHILE IS pattern COLONEQ expression blockExpression
    ;

iteratorLoopExpression
    : FOR pattern IN expression blockExpression
    ;

loopLabel
    : NON_KEYWORD_IDENTIFIER COLON
    ;

comptimeExpression
    : COMPTIME (blockExpression | expression)
    ;

codeExpression
    : CODE LCURLYBRACE codeContent RCURLYBRACE
    ;

codeContent
    : statements?
    ;

typeExpression
    : type_
    ;

mlirExpression
    : MLIR (TYPE | identifier)? LCURLYBRACE mlirContent? RCURLYBRACE
    ;

mlirContent
    : mlirElement+
    ;

mlirElement
    : LCURLYBRACE mlirContent? RCURLYBRACE
    | ~(LCURLYBRACE | RCURLYBRACE)
    ;

asmExpression
    : RAW_ASM_BLOCK
    ;

importExpression
    : IMPORT dottedName
    ;

ifExpression
    : IF expression blockExpression (ELSE (blockExpression | ifExpression))?
    ;

matchExpression
    : MATCH expression LCURLYBRACE attribute* matchArms? RCURLYBRACE
    ;

matchArms
    : (matchArm FATARROW matchArmExpression)* matchArm FATARROW expression COMMA?
    ;

matchArmExpression
    : expression COMMA
    | expressionWithBlock COMMA?
    ;

matchArm
    : attribute* pattern matchArmGuard?
    ;

matchArmGuard
    : IF expression
    ;

pattern
    : patternNoTopAlt (B_OR patternNoTopAlt)*
    ;

patternNoTopAlt
    : patternWithoutRange
    | rangePattern
    ;

patternWithoutRange
    : literalPattern
    | identifierPattern
    | wildcardPattern
    | restPattern
    | structPattern
    | tupleStructPattern
    | tuplePattern
    | groupedPattern
    | slicePattern
    | pathPattern
    ;

literalPattern
    : TRUE
    | FALSE
    | CHAR_LITERAL
    | BYTE_LITERAL
    | STRING_LITERAL
    | RAW_STRING_LITERAL
    | BYTE_STRING_LITERAL
    | RAW_BYTE_STRING_LITERAL
    | MINUS? INTEGER_LITERAL
    | MINUS? FLOAT_LITERAL
    | IMAGINARY_LITERAL
    ;

identifierPattern
    : identifier (AT pattern)?
    ;

wildcardPattern
    : UNDERSCORE
    ;

restPattern
    : DOTDOT
    ;

rangePattern
    : rangePatternBound DOTDOTEQ rangePatternBound # InclusiveRangePattern
    | rangePatternBound DOTDOT rangePatternBound  # ExclusiveRangePattern
    | rangePatternBound DOTDOT                    # HalfOpenRangePattern
    | DOTDOT rangePatternBound                     # HalfOpenRangePattern
    ;

rangePatternBound
    : CHAR_LITERAL
    | BYTE_LITERAL
    | MINUS? INTEGER_LITERAL
    | MINUS? FLOAT_LITERAL
    | pathPattern
    ;

structPattern
    : dottedName LCURLYBRACE structPatternElements? RCURLYBRACE
    ;

structPatternElements
    : structPatternFields (COMMA structPatternEtCetera?)?
    | structPatternEtCetera
    ;

structPatternFields
    : structPatternField (COMMA structPatternField)*
    ;

structPatternField
    : attribute* (tupleIndex COLON pattern | identifier COLON pattern | identifier)
    ;

structPatternEtCetera
    : attribute* DOTDOT
    ;

tupleStructPattern
    : dottedName LPAREN tupleStructItems? RPAREN
    ;

tupleStructItems
    : pattern (COMMA pattern)* COMMA?
    ;

tuplePattern
    : LPAREN tuplePatternItems? RPAREN
    ;

tuplePatternItems
    : pattern COMMA
    | restPattern
    | pattern (COMMA pattern)+ COMMA?
    ;

groupedPattern
    : LPAREN pattern RPAREN
    ;

slicePattern
    : LSQUAREBRACKET slicePatternItems? RSQUAREBRACKET
    ;

slicePatternItems
    : pattern (COMMA pattern)* COMMA?
    ;

pathPattern
    : dottedName
    ;


type_
    : typeAtom (BANG typeAtom)*
    ;

typeAtom
    : parenthesizedType
    | typePath
    | tupleType
    | noreturnType
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
    | TYPE
    ;

parenthesizedType
    : LPAREN type_ RPAREN
    ;

noreturnType
    : NORETURN
    ;

tupleType
    : LPAREN ((type_ COMMA)+ type_?)? RPAREN
    ;

arrayType
    : LSQUAREBRACKET expression RSQUAREBRACKET type_
    ;

dynamicArrayType
    : LSQUAREBRACKET DYN RSQUAREBRACKET type_
    ;

sliceType
    : LSQUAREBRACKET  RSQUAREBRACKET type_
    ;

mapType
    : LSQUAREBRACKET type_ COLON type_ RSQUAREBRACKET
    ;

optionalType
    : QUESTION type_
    ;

errorType
    : ERROR LCURLYBRACE variantItems? declaration* RCURLYBRACE
    ;

structType
    : STRUCT (LCURLYBRACE structFields? declaration* RCURLYBRACE)?
    ;

structFields
    : structField (COMMA structField)* COMMA?
    ;

structField
    : attribute* PUB? identifier COLON type_
    ;

enumType
    : ENUM parenthesizedType? LCURLYBRACE enumItems? declaration* RCURLYBRACE
    ;

enumItems
    : enumItem (COMMA enumItem)* COMMA?
    ;

enumItem
    : attribute* PUB? identifier (
         enumItemDiscriminant
    )?
    ;

variantType
    : VARIANT LCURLYBRACE variantItems? declaration* RCURLYBRACE
    ;

variantItems
    : variantItem (COMMA variantItem)* COMMA?
    ;

variantItem
    : attribute* PUB? identifier (
        enumItemStruct
        | enumItemTuple
        | enumItemDiscriminant
    )?
    ;

enumItemTuple
    : LPAREN tupleFields? RPAREN
    ;

enumItemStruct
    : LCURLYBRACE structFields? RCURLYBRACE
    ;

enumItemDiscriminant
    : EQ expression
    ;

tupleFields
    : tupleField (COMMA tupleField)* COMMA?
    ;

tupleField
    : attribute* PUB? type_
    ;

unionType
    : UNION LCURLYBRACE structFields? declaration* RCURLYBRACE
    ;


simdType
    : SIMD LPAREN expression COMMA type_ RPAREN
    ;

complexType
    : COMPLEX LPAREN type_ RPAREN
    ;

tensorType
    : TENSOR LPAREN tensorDims COMMA type_ RPAREN
    ;

tensorDims
    : INTEGER_LITERAL (COMMA INTEGER_LITERAL)* COMMA?
    ;

rawPointerType
    : STAR CONST? type_
    ;

bareFunctionType
    : functionTypeQualifiers FN LPAREN functionParametersMaybeNamedVariadic? RPAREN type_?
    ;

functionTypeQualifiers
    : (EXTERN abi?)?
    ;


abi
    : STRING_LITERAL
    | RAW_STRING_LITERAL
    ;

functionParametersMaybeNamedVariadic
    : maybeNamedFunctionParameters
    | maybeNamedFunctionParametersVariadic
    ;

maybeNamedFunctionParameters
    : maybeNamedParam (COMMA maybeNamedParam)* COMMA?
    ;

maybeNamedParam
    : attribute* ((identifier | UNDERSCORE) COLON)? type_
    ;

maybeNamedFunctionParametersVariadic
    : (maybeNamedParam COMMA)* maybeNamedParam COMMA attribute* DOTDOTDOT
    ;

inferredType
    : ANY
    ;

dottedName
    : identifier (DOT identifier)*
    ;

typePath
    : identifier (DOT identifier)*
    ;
