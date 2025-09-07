#ifndef AST_H
#define AST_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stddef.h>

/* ---------- Locations  ---------- */
typedef struct {
  int first_line;
  int first_column;
  int last_line;
  int last_column;
} SourceLocation;

/* Forward decl */
typedef struct AstNode AstNode;

/* ---------- Operator enum ---------- */
typedef enum {
  /* Binary */
  OP_ADD,
  OP_SUB,
  OP_MUL,
  OP_DIV,
  OP_MOD,
  OP_OR,
  OP_AND, /* logical OR/AND (from keywords) */
  OP_XOR,
  OP_SHL,
  OP_SHR,
  OP_EQ,
  OP_NEQ,
  OP_LT,
  OP_LTE,
  OP_GT,
  OP_GTE,
  OP_ORELSE,
  OP_DOTDOT,
  OP_DOTDOTEQ,
  OP_BOR,
  OP_BXOR,
  OP_BAND,
  OP_SHL_SAT,
  OP_ADD_SAT,
  OP_SUB_SAT,
  OP_ADD_WRAP,
  OP_SUB_WRAP,
  OP_MUL_SAT,
  OP_MUL_WRAP,
  /* Unary */
  OP_ADDR,
  OP_NEG,
  OP_NOT,
  /* Compound-assign */
  OP_ADD_ASSIGN,
  OP_SUB_ASSIGN,
  OP_MUL_ASSIGN,
  OP_DIV_ASSIGN,
  OP_MOD_ASSIGN,
  OP_AND_ASSIGN,
  OP_OR_ASSIGN,
  OP_XOR_ASSIGN,
  OP_SHL_ASSIGN,
  OP_SHR_ASSIGN,
  OP_ADD_SAT_ASSIGN,
  OP_SUB_SAT_ASSIGN,
  OP_MUL_SAT_ASSIGN,
  OP_SHL_SAT_ASSIGN,
  OP_ADD_WRAP_ASSIGN,
  OP_SUB_WRAP_ASSIGN,
  OP_MUL_WRAP_ASSIGN
} Op;

/* ---------- Node kinds ---------- */
typedef enum {
  NODE_UNKNOWN = 0,

  /* Root */
  NODE_PROGRAM,
  NODE_PACKAGE_DECL,
  NODE_DECLARATION_LIST,

  /* Decls */
  NODE_CONST_DECL,
  NODE_VAR_DECL,

  /* Identifiers, paths, literals */
  NODE_IDENTIFIER,
  NODE_RAW_IDENTIFIER,
  NODE_PATH, /* path of identifiers, >=1 segments */
  NODE_IDENTIFIER_EXPR,
  NODE_INTEGER_LITERAL,
  NODE_STRING_LITERAL,
  NODE_RAW_STRING_LITERAL,
  NODE_CHAR_LITERAL,
  NODE_FLOAT_LITERAL,
  NODE_IMAGINARY_LITERAL,
  NODE_BYTE_LITERAL,
  NODE_BYTE_STRING_LITERAL,
  NODE_RAW_BYTE_STRING_LITERAL,
  NODE_BOOL_LITERAL,

  /* Attributes */
  NODE_ATTRIBUTE,  /* key(:value)? */
  NODE_ATTR_LIST,  /* list of NODE_ATTRIBUTE */
  NODE_ATTR_APPLY, /* wrapper: attrs applied to target node */

  /* Statements / blocks */
  NODE_STATEMENT_LIST,
  NODE_BLOCK_EXPRESSION,
  NODE_INSERT_STMT,
  NODE_DEFER_STMT,
  NODE_ERRDEFER_STMT,
  NODE_CONTINUE,
  NODE_BREAK,
  NODE_RETURN,
  NODE_LABEL,
  NODE_NULL,
  NODE_UNDEFINED,
  NODE_UNREACHABLE_EXPR,

  /* Expressions */
  NODE_EXPRESSION_LIST,
  NODE_ASSIGN_EXPR,
  NODE_COMPOUND_ASSIGN_EXPR,
  NODE_BINARY_EXPR,
  NODE_UNARY_EXPR,

  /* Postfix/selectors */
  NODE_FIELD_ACCESS,
  NODE_TUPLE_INDEX,
  NODE_AWAIT,
  NODE_TYPE_CAST,
  NODE_CALL,
  NODE_INDEX,
  NODE_DEREF,
  NODE_ERROR_PROP,

  /* Grouping & literal collections */
  NODE_GROUPED_EXPR,
  NODE_ARRAY_LITERAL,
  NODE_TUPLE_LITERAL,
  NODE_COLLECTION_BODY, /* head expr + tail (map/array/tuple specifics) */
  NODE_MAP_ELEMENT,
  NODE_MAP_ELEMENT_LIST,
  NODE_MAP_TAIL,
  NODE_ARRAY_REST_ELEMENT,
  NODE_ARRAY_REST_ELEMENT_LIST,
  NODE_TUPLE_HEAD_ELEMENT,
  NODE_TUPLE_HEAD_ELEMENT_LIST,

  /* Struct / enum variant expressions */
  NODE_STRUCT_EXPRESSION,
  NODE_STRUCT_FIELD, /* name/index with value? */
  NODE_STRUCT_FIELD_LIST,
  NODE_STRUCT_BASE, /* ..expr */

  NODE_ENUM_VARIANT_EXPRESSION,
  NODE_ENUM_VARIANT_FIELD, /* name or index with value? */
  NODE_ENUM_VARIANT_FIELD_LIST,

  /* Closures */
  NODE_CLOSURE_EXPRESSION,
  NODE_CLOSURE_PARAMETERS, /* list of closureParam */
  NODE_CLOSURE_PARAM,      /* attr? pattern typeAnn? */

  /* Code / MLIR / ASM / import */
  NODE_CODE_EXPRESSION,
  NODE_MLIR_EXPRESSION, /* head? body? */
  NODE_ASM_EXPRESSION,  /* raw text */
  NODE_IMPORT_EXPRESSION,

  /* Control expressions */
  NODE_IF_EXPRESSION,
  NODE_LOOP_EXPRESSION,
  NODE_MATCH_EXPRESSION,
  NODE_MATCH_ARM,
  NODE_MATCH_ARM_LIST,
  NODE_MATCH_GUARD,

  /* Catch */
  NODE_CATCH_EXPR,

  /* Function/procedure expressions */
  NODE_FUNCTION_EXPRESSION,
  NODE_PROCEDURE_EXPRESSION,
  NODE_FUNCTION_QUALIFIERS,
  NODE_ASYNC_QUALIFIER,
  NODE_EXTERN_QUALIFIER,
  NODE_ABI, /* string literal */
  NODE_FUNCTION_PARAMETERS,
  NODE_FUNCTION_PARAM,
  NODE_ELLIPSIS,
  NODE_COMPTIME_QUALIFIER,
  NODE_FUNCTION_PARAM_PATTERN,
  NODE_EQ_EXPR,
  NODE_TYPE_ANNOTATION,

  NODE_ASYNC_EXPRESSION,
  NODE_COMPTIME_EXPRESSION,

  /* Patterns */
  NODE_PATTERN_WILDCARD,   /* _ */
  NODE_PATTERN_LITERAL,    /* wraps a literal */
  NODE_PATTERN_IDENTIFIER, /* name [ @ subpattern ] */
  NODE_PATTERN_REST,       /* .. */
  NODE_PATTERN_RANGE,      /* bounds w/ variant kind */
  NODE_PATTERN_STRUCT,     /* path { fields / .. } */
  NODE_PATTERN_STRUCT_FIELD,
  NODE_PATTERN_STRUCT_FIELD_LIST,
  NODE_PATTERN_TUPLE_STRUCT, /* Path(x,y,...) */
  NODE_PATTERN_TUPLE,        /* (a, b, ...) */
  NODE_PATTERN_GROUPED,      /* (pat) */
  NODE_PATTERN_SLICE,        /* [a, b, ...] */
  NODE_PATTERN_PATH,         /* qualified name */
  NODE_PATTERN_STRUCT_ELEMS,

  /* Types */
  NODE_TYPE_PAREN,
  NODE_TYPE_PATH,
  NODE_TYPE_TUPLE,
  NODE_TYPE_NORETURN,
  NODE_TYPE_RAW_POINTER,
  NODE_TYPE_ARRAY,
  NODE_TYPE_DYNAMIC_ARRAY,
  NODE_TYPE_SLICE,
  NODE_TYPE_MAP,
  NODE_TYPE_OPTIONAL,
  NODE_TYPE_ERROR,
  NODE_TYPE_SIMD,
  NODE_TYPE_COMPLEX,
  NODE_TYPE_TENSOR,
  NODE_TYPE_INFERRED, /* ANY */
  NODE_TYPE_STRUCT,
  NODE_TYPE_ENUM,
  NODE_TYPE_VARIANT,
  NODE_TYPE_UNION,
  NODE_TYPE_BARE_FUNCTION,

  /* Struct/Enum/Variant/Union members for types */
  NODE_TYPE_STRUCT_FIELD,
  NODE_TYPE_STRUCT_FIELD_LIST,
  NODE_TYPE_ENUM_ITEM,
  NODE_TYPE_ENUM_ITEM_LIST,
  NODE_TYPE_VARIANT_ITEM,
  NODE_TYPE_VARIANT_ITEM_LIST,

  /* Function type params (maybe-named) */
  NODE_TYPE_MAYBE_NAMED_PARAM,
  NODE_TYPE_MAYBE_NAMED_PARAM_LIST
} NodeType;

/* ---------- Common list type ---------- */
typedef struct {
  AstNode **items;
  size_t count, capacity;
} NodeList;

/* ---------- Payload structs ---------- */

/* Root & decls */
typedef struct {
  AstNode *packageDecl;
  AstNode *decls;
} AstNodeProgram;
typedef struct {
  AstNode *name;
} AstNodePackageDecl;
typedef struct {
  AstNode *pattern, *type, *expr;
} AstNodeConstDecl;
typedef struct {
  AstNode *pattern, *type, *expr;
} AstNodeVarDecl;

/* Identifiers, paths, literals */
typedef struct {
  char *name;
} AstNodeIdentifier;
typedef struct {
  NodeList segments;
} AstNodePath;
typedef struct {
  char *name;
} AstNodeIdentifierExpr;
typedef struct {
  char *value;
} AstNodeLiteral;

/* Attributes */
typedef struct {
  AstNode *key, *value;
} AstNodeAttribute;
typedef struct {
  NodeList list;
} AstNodeAttrList;
typedef struct {
  AstNode *attrs;
  AstNode *target;
} AstNodeAttrApply;

/* Statements / blocks / flow */
typedef struct {
  NodeList list;
} AstNodeStatementList;
typedef struct {
  AstNode *attr;
  AstNode *statements;
} AstNodeBlockExpression;
typedef struct {
  AstNode *expr;
} AstNodeStatement;
typedef struct {
  char *name;
} AstNodeLabel;
typedef struct {
  AstNode *label;
  AstNode *expr;
} AstNodeContinue;
typedef struct {
  AstNode *label;
  AstNode *expr;
} AstNodeBreak;
typedef struct {
  AstNode *expr;
} AstNodeReturn;

/* Expressions */
typedef struct {
  NodeList list;
} AstNodeExpressionList;
typedef struct {
  AstNode *lhs, *rhs;
} AstNodeAssignExpr;
typedef struct {
  AstNode *lhs, *rhs;
  Op op;
} AstNodeCompoundAssignExpr;
typedef struct {
  AstNode *lhs, *rhs;
  Op op;
} AstNodeBinaryExpr;
typedef struct {
  AstNode *operand;
  Op op;
} AstNodeUnaryExpr;

/* Postfix/selectors */
typedef struct {
  AstNode *target, *field;
} AstNodeFieldAccess;
typedef struct {
  AstNode *target, *index;
} AstNodeTupleIndex;
typedef struct {
  AstNode *target;
} AstNodePostfix; /* await/deref/errorprop */
typedef struct {
  AstNode *target, *type;
} AstNodeTypeCast;
typedef struct {
  AstNode *target, *params;
} AstNodeCall; /* params = expr list */
typedef struct {
  AstNode *target, *indexExpr;
} AstNodeIndex;

/* Grouping / collection */
typedef struct {
  AstNode *attr, *expr;
} AstNodeGroupedExpr;
typedef struct {
  AstNode *attr, *body;
} AstNodeArrayLiteral;
typedef struct {
  AstNode *attr, *elements;
} AstNodeTupleLiteral;

typedef struct {
  AstNode *expression, *tail;
} AstNodeCollectionBody;
typedef struct {
  AstNode *key, *value;
} AstNodeMapElement;
typedef struct {
  NodeList list;
} AstNodeMapElementList;
typedef struct {
  AstNode *expr;
} AstNodeArrayRestElement;
typedef struct {
  NodeList list;
} AstNodeArrayRestElementList;
typedef struct {
  AstNode *expr;
} AstNodeTupleHeadElement;
typedef struct {
  NodeList list;
} AstNodeTupleHeadElementList;

/* Struct / enum variant expressions */
typedef struct {
  AstNode *attr;
  AstNode *key;
  AstNode *value;
  int key_is_index;
} AstNodeStructField;
typedef struct {
  NodeList list;
} AstNodeStructFieldList;
typedef struct {
  AstNode *expr;
} AstNodeStructBase;
typedef struct {
  AstNode *path;
  AstNode *attr;
  AstNode *fields;
  AstNode *base;
} AstNodeStructExpression;

typedef struct {
  AstNode *key;
  AstNode *value;
  int key_is_index;
} AstNodeEnumVariantField;
typedef struct {
  NodeList list;
} AstNodeEnumVariantFieldList;
typedef struct {
  AstNode *path;
  AstNode *fields;
} AstNodeEnumVariantExpression;

typedef struct {
  AstNode *first_value;
  AstNode *rest;
} AstNodeMapTail;
typedef struct {
  AstNode *fields;
  int has_etc;
} AstNodePatternStructElems;

/* Closures */
typedef struct {
  AstNode *attr;
  AstNode *pattern;
  AstNode *typeAnn;
} AstNodeClosureParam;
typedef struct {
  NodeList list;
} AstNodeClosureParameters;
typedef struct {
  AstNode *params;
  AstNode *ret_type;
  AstNode *body;
  int body_is_block;
} AstNodeClosureExpression;

/* Code / MLIR / ASM / import */
typedef struct {
  AstNode *statements;
} AstNodeCodeExpression;
typedef struct {
  AstNode *head;
  AstNode *body;
} AstNodeMlirExpression;
typedef struct {
  char *text;
} AstNodeAsmExpression;
typedef struct {
  AstNode *path;
} AstNodeImportExpression;
typedef struct {
  AstNode *expr;
} AstNodeAsyncExpression;
typedef struct {
  AstNode *expr;
} AstNodeComptimeExpression;

/* Control expressions */
typedef struct {
  AstNode *cond;
  AstNode *thenBr;
  AstNode *elseBr;
} AstNodeIfExpression;

typedef enum {
  LOOP_INF,
  LOOP_PREDICATE,
  LOOP_PREDICATE_PATTERN,
  LOOP_ITERATOR
} LoopKind;
typedef struct {
  LoopKind kind;
  AstNode *label;     /* identifier or NULL */
  AstNode *cond;      /* predicate / iterator expr */
  AstNode *pattern;   /* for pattern & iterator loops */
  AstNode *iter_expr; /* for iterator loops */
  AstNode *body;      /* blockExpression */
} AstNodeLoopExpression;

typedef struct {
  AstNode *pattern;
  AstNode *guard;
} AstNodeMatchArmHead;
typedef struct {
  AstNode *attr;
  AstNode *head;
  AstNode *rhs;
} AstNodeMatchArm;
typedef struct {
  NodeList list;
} AstNodeMatchArmList;
typedef struct {
  AstNode *expr;
  AstNode *attr;
  AstNode *arms;
} AstNodeMatchExpression;
typedef struct {
  AstNode *expr;
} AstNodeMatchGuard;

/* Catch */
typedef struct {
  AstNode *expr, *binder, *handler;
} AstNodeCatchExpr;

/* Functions / procedures */
typedef struct {
  AstNode *qualifiers, *params, *ret_type, *body;
  int body_is_asm;
} AstNodeFunctionExpression;
typedef struct {
  AstNode *qualifiers, *params, *ret_type, *body;
  int body_is_asm;
} AstNodeProcedureExpression;
typedef struct {
  AstNode *async_q, *extern_q;
} AstNodeFunctionQualifiers;
typedef struct {
  AstNode *abi;
} AstNodeExternQualifier;
typedef struct {
  char *value;
} AstNodeAbi;

typedef struct {
  NodeList list;
} AstNodeFunctionParameters;
typedef struct {
  AstNode *attr, *comptime, *param_type;
} AstNodeFunctionParam;
typedef struct {
  AstNode *pattern, *type, *default_eq;
} AstNodeFunctionParamPattern;
typedef struct {
  AstNode *expr;
} AstNodeEqExpr;
typedef struct {
  AstNode *type;
} AstNodeTypeAnnotation;

/* Patterns */
typedef struct {
  AstNode *literal;
} AstNodePatternLiteral;
typedef struct {
  AstNode *name;
  AstNode *at;
} AstNodePatternIdentifier;
typedef enum {
  RANGE_CLOSED,
  RANGE_HALF_OPEN,
  RANGE_FROM,
  RANGE_TO
} PatternRangeKind;
typedef struct {
  PatternRangeKind kind;
  AstNode *lhs;
  AstNode *rhs;
} AstNodePatternRange;

typedef struct {
  AstNode *attr;
  AstNode *key;
  AstNode *pat;
  int key_is_index;
} AstNodePatternStructField;
typedef struct {
  NodeList list;
} AstNodePatternStructFieldList;
typedef struct {
  AstNode *path;
  AstNode *fields;
  int has_etc;
} AstNodePatternStruct;
typedef struct {
  AstNode *path;
  AstNode *items;
} AstNodePatternTupleStruct;
typedef struct {
  AstNode *items;
} AstNodePatternTuple;
typedef struct {
  AstNode *pat;
} AstNodePatternGrouped;
typedef struct {
  AstNode *items;
} AstNodePatternSlice;
typedef struct {
  AstNode *path;
} AstNodePatternPath;

/* Types */
typedef struct {
  AstNode *inner;
} AstNodeTypeParen;
typedef struct {
  AstNode *path;
} AstNodeTypePath;
typedef struct {
  NodeList list;
} AstNodeTypeTuple;
typedef struct {
  int is_const;
  AstNode *pointee;
} AstNodeTypeRawPointer;
typedef struct {
  AstNode *len_expr;
  AstNode *elem;
} AstNodeTypeArray;
typedef struct {
  AstNode *elem;
} AstNodeTypeDynamicArray;
typedef struct {
  AstNode *elem;
} AstNodeTypeSlice;
typedef struct {
  AstNode *key, *value;
} AstNodeTypeMap;
typedef struct {
  AstNode *base;
} AstNodeTypeOptional;
typedef struct {
  AstNode *variants;
  AstNode *decls;
} AstNodeTypeError;
typedef struct {
  AstNode *lanes, *elem;
} AstNodeTypeSimd;
typedef struct {
  AstNode *elem;
} AstNodeTypeComplex;
typedef struct {
  NodeList dims;
  AstNode *elem;
} AstNodeTypeTensor;

typedef struct {
  AstNode *attr;
  int is_pub;
  AstNode *name;
  AstNode *type;
} AstNodeTypeStructField;
typedef struct {
  NodeList list;
} AstNodeTypeStructFieldList;
typedef struct {
  AstNode *fields;
  AstNode *decls;
} AstNodeTypeStruct;

typedef struct {
  AstNode *attr;
  int is_pub;
  AstNode *name;
  AstNode *discriminant;
} AstNodeTypeEnumItem;
typedef struct {
  NodeList list;
} AstNodeTypeEnumItemList;
typedef struct {
  AstNode *underlying;
  AstNode *items;
  AstNode *decls;
} AstNodeTypeEnum;

typedef struct {
  AstNode *attr;
  int is_pub;
  AstNode *name;
  AstNode *body;
} AstNodeTypeVariantItem;
typedef struct {
  NodeList list;
} AstNodeTypeVariantItemList;
typedef struct {
  AstNode *items;
  AstNode *decls;
} AstNodeTypeVariant;

typedef struct {
  AstNode *fields;
  AstNode *decls;
} AstNodeTypeUnion;

/* bare function types (maybe-named params) */
typedef struct {
  AstNode *attr;
  AstNode *name;
  int is_underscore;
  AstNode *type;
} AstNodeTypeMaybeNamedParam;
typedef struct {
  NodeList list;
  int has_variadic;
  AstNode *vararg_attr;
} AstNodeTypeMaybeNamedParamList;
typedef struct {
  AstNode *extern_q;
  AstNode *params;
  AstNode *ret_type;
} AstNodeTypeBareFunction;

/* ---------- The master node ---------- */
struct AstNode {
  NodeType type;
  SourceLocation loc;
  union {
    /* Root/decls */
    AstNodeProgram program;
    AstNodePackageDecl packageDecl;
    NodeList declList; /* for NODE_DECLARATION_LIST */

    AstNodeConstDecl constDecl;
    AstNodeVarDecl varDecl;

    /* Identifiers, paths, literals */
    AstNodeIdentifier identifier;
    AstNodePath path;
    AstNodeIdentifierExpr identifierExpr;
    AstNodeLiteral literal;

    /* Attributes */
    AstNodeAttribute attribute;
    AstNodeAttrList attrList;
    AstNodeAttrApply attrApply;

    /* Statements/blocks/flow */
    AstNodeStatementList statementList;
    AstNodeBlockExpression blockExpression;
    AstNodeStatement statement;
    AstNodeLabel label;
    AstNodeContinue cont;
    AstNodeBreak brk;
    AstNodeReturn ret;

    /* Expressions */
    AstNodeExpressionList exprList;
    AstNodeAssignExpr assignExpr;
    AstNodeCompoundAssignExpr compoundAssignExpr;
    AstNodeBinaryExpr binaryExpr;
    AstNodeUnaryExpr unaryExpr;

    /* Postfix/selectors */
    AstNodeFieldAccess fieldAccess;
    AstNodeTupleIndex tupleIndex;
    AstNodePostfix postfix;
    AstNodeTypeCast typeCast;
    AstNodeCall call;
    AstNodeIndex index;

    /* Grouping / collections */
    AstNodeGroupedExpr groupedExpr;
    AstNodeArrayLiteral arrayLiteral;
    AstNodeTupleLiteral tupleLiteral;
    AstNodeCollectionBody collectionBody;
    AstNodeMapElement mapElement;
    AstNodeMapElementList mapElementList;
    AstNodeArrayRestElement arrayRestElement;
    AstNodeArrayRestElementList arrayRestElementList;
    AstNodeTupleHeadElement tupleHeadElement;
    AstNodeTupleHeadElementList tupleHeadElementList;

    /* Struct/enum variant exprs */
    AstNodeStructField structField;
    AstNodeStructFieldList structFieldList;
    AstNodeStructBase structBase;
    AstNodeStructExpression structExpr;

    AstNodeEnumVariantField enumVariantField;
    AstNodeEnumVariantFieldList enumVariantFieldList;
    AstNodeEnumVariantExpression enumVariantExpr;

    /* Closures */
    AstNodeClosureParam closureParam;
    AstNodeClosureParameters closureParams;
    AstNodeClosureExpression closureExpr;

    /* Code/MLIR/ASM/import */
    AstNodeCodeExpression codeExpr;
    AstNodeMlirExpression mlirExpr;
    AstNodeAsmExpression asmExpr;
    AstNodeImportExpression importExpr;
    AstNodeAsyncExpression asyncExpr;
    AstNodeComptimeExpression comptimeExpr;

    /* Control */
    AstNodeIfExpression ifExpr;
    AstNodeLoopExpression loopExpr;
    AstNodeMatchArm matchArm;
    AstNodeMatchArmList matchArmList;
    AstNodeMatchExpression matchExpr;
    AstNodeMatchGuard matchGuard;

    /* Catch */
    AstNodeCatchExpr catchExpr;

    /* Functions/procs */
    AstNodeFunctionExpression funcExpr;
    AstNodeProcedureExpression procExpr;
    AstNodeFunctionQualifiers funcQuals;
    AstNodeExternQualifier externQual;
    AstNodeAbi abi;
    AstNodeFunctionParameters funcParams;
    AstNodeFunctionParam funcParam;
    AstNodeFunctionParamPattern funcParamPattern;
    AstNodeEqExpr eqExpr;
    AstNodeTypeAnnotation typeAnn;

    /* Patterns */
    AstNodePatternLiteral patLiteral;
    AstNodePatternIdentifier patIdent;
    AstNodePatternRange patRange;
    AstNodePatternStructField patStructField;
    AstNodePatternStructFieldList patStructFieldList;
    AstNodePatternStruct patStruct;
    AstNodePatternTupleStruct patTupleStruct;
    AstNodePatternTuple patTuple;
    AstNodePatternGrouped patGrouped;
    AstNodePatternSlice patSlice;
    AstNodePatternPath patPath;

    AstNodeMapTail mapTail;
    AstNodePatternStructElems patStructElems;

    /* Types */
    AstNodeTypeParen tParen;
    AstNodeTypePath tPath;
    AstNodeTypeTuple tTuple;
    AstNodeTypeRawPointer tRawPtr;
    AstNodeTypeArray tArray;
    AstNodeTypeDynamicArray tDynArray;
    AstNodeTypeSlice tSlice;
    AstNodeTypeMap tMap;
    AstNodeTypeOptional tOpt;
    AstNodeTypeError tError;
    AstNodeTypeSimd tSimd;
    AstNodeTypeComplex tComplex;
    AstNodeTypeTensor tTensor;

    AstNodeTypeStructField tStructField;
    AstNodeTypeStructFieldList tStructFieldList;
    AstNodeTypeStruct tStruct;

    AstNodeTypeEnumItem tEnumItem;
    AstNodeTypeEnumItemList tEnumItemList;
    AstNodeTypeEnum tEnum;

    AstNodeTypeVariantItem tVarItem;
    AstNodeTypeVariantItemList tVarItemList;
    AstNodeTypeVariant tVariant;

    AstNodeTypeUnion tUnion;

    /* bare function types */
    AstNodeTypeMaybeNamedParam tMaybeNamedParam;
    AstNodeTypeMaybeNamedParamList tMaybeNamedParamList;
    AstNodeTypeBareFunction tBareFn;
  } data;
};

/* ---------- Constructors / helpers ---------- */

/* Node core */
AstNode *new_node(NodeType type, SourceLocation loc);
SourceLocation loc_make(int fl, int fc, int ll, int lc);

/* Program/decls */
AstNode *program_node(AstNode *packageDecl, AstNode *decls, SourceLocation loc);
AstNode *package_decl(AstNode *name, SourceLocation loc);
AstNode *const_decl(AstNode *pattern, AstNode *type, AstNode *expr,
                    SourceLocation loc);
AstNode *var_decl(AstNode *pattern, AstNode *type, AstNode *expr,
                  SourceLocation loc);
AstNode *decl_list_append(AstNode *list, AstNode *decl);

/* Identifiers, paths, literals */
AstNode *identifier_node(const char *name, SourceLocation loc);
AstNode *raw_identifier_node(const char *name, SourceLocation loc);
AstNode *identifier_expr(const char *name, SourceLocation loc);
AstNode *path_single(AstNode *ident, SourceLocation loc);
AstNode *path_append(AstNode *path, AstNode *ident);
AstNode *literal_node(NodeType kind, char *owned_text, SourceLocation loc);

/* Attributes */
AstNode *attr_key(AstNode *key, SourceLocation loc);
AstNode *attr_key_value(AstNode *key, AstNode *value, SourceLocation loc);
AstNode *attr_list_append(AstNode *list, AstNode *attr);
AstNode *attr_apply(AstNode *attrs, AstNode *target, SourceLocation loc);

/* Statements / blocks / flow */
AstNode *statement_list_append(AstNode *list, AstNode *stmt);
AstNode *block_expression(AstNode *attr, AstNode *statements,
                          SourceLocation loc);
AstNode *insert_stmt(AstNode *expr, SourceLocation loc);
AstNode *defer_stmt(AstNode *expr, SourceLocation loc);
AstNode *errdefer_stmt(AstNode *expr, SourceLocation loc);
AstNode *label_node(const char *name, SourceLocation loc);
AstNode *continue_expr(AstNode *label, AstNode *expr, SourceLocation loc);
AstNode *break_expr(AstNode *label, AstNode *expr, SourceLocation loc);
AstNode *return_expr(AstNode *expr, SourceLocation loc);
AstNode *null_expr(SourceLocation loc);
AstNode *undefined_expr(SourceLocation loc);
AstNode *unreachable_expr(SourceLocation loc);

/* Expressions */
AstNode *expr_list_append(AstNode *list, AstNode *expr);
AstNode *assign_expr(AstNode *lhs, AstNode *rhs, SourceLocation loc);
AstNode *compound_assign_expr(AstNode *lhs, AstNode *rhs, Op op,
                              SourceLocation loc);
AstNode *binary_expr(AstNode *lhs, AstNode *rhs, Op op, SourceLocation loc);
AstNode *unary_expr(AstNode *operand, Op op, SourceLocation loc);
int cmp_token_to_op(int token, Op *out);

/* Postfix/selectors */
AstNode *field_access_expr(AstNode *target, AstNode *field, SourceLocation loc);
AstNode *tuple_index_expr(AstNode *target, AstNode *index, SourceLocation loc);
AstNode *await_expr(AstNode *target, SourceLocation loc);
AstNode *type_cast_expr(AstNode *target, AstNode *type, SourceLocation loc);
AstNode *call_expr(AstNode *target, AstNode *params, SourceLocation loc);
AstNode *index_expr(AstNode *target, AstNode *indexExpr, SourceLocation loc);
AstNode *deref_expr(AstNode *target, SourceLocation loc);
AstNode *errorprop_expr(AstNode *target, SourceLocation loc);

/* Grouping / collections */
AstNode *grouped_expr(AstNode *attr, AstNode *expr, SourceLocation loc);
AstNode *array_literal(AstNode *attr, AstNode *body, SourceLocation loc);
AstNode *tuple_literal(AstNode *attr, AstNode *elements, SourceLocation loc);
AstNode *collection_body(AstNode *head_expr, AstNode *tail, SourceLocation loc);

AstNode *map_element(AstNode *key, AstNode *value, SourceLocation loc);
AstNode *map_element_list_append(AstNode *list, AstNode *elem);
AstNode *array_rest_element(AstNode *expr, SourceLocation loc);
AstNode *array_rest_list_append(AstNode *list, AstNode *elem);
AstNode *tuple_head_element(AstNode *expr, SourceLocation loc);
AstNode *tuple_head_list_append(AstNode *list, AstNode *elem);

/* Struct / enum variant expressions */
AstNode *struct_field(AstNode *attr, AstNode *key, int key_is_index,
                      AstNode *value, SourceLocation loc);
AstNode *struct_field_list_append(AstNode *list, AstNode *field);
AstNode *struct_base(AstNode *expr, SourceLocation loc);
AstNode *struct_expression(AstNode *path, AstNode *attr, AstNode *fields,
                           AstNode *base, SourceLocation loc);

AstNode *enum_variant_field(AstNode *key, int key_is_index, AstNode *value,
                            SourceLocation loc);
AstNode *enum_variant_field_list_append(AstNode *list, AstNode *field);
AstNode *enum_variant_expression(AstNode *path, AstNode *fields,
                                 SourceLocation loc);

/* Closures */
AstNode *closure_param(AstNode *attr, AstNode *pattern, AstNode *typeAnn,
                       SourceLocation loc);
AstNode *closure_params_append(AstNode *list, AstNode *param);
AstNode *closure_expression(AstNode *params, AstNode *ret_type, AstNode *body,
                            int body_is_block, SourceLocation loc);

/* Code/MLIR/ASM/import */
AstNode *code_expression(AstNode *statements, SourceLocation loc);
AstNode *mlir_expression(AstNode *head, AstNode *body, SourceLocation loc);
AstNode *asm_expression(char *owned_text, SourceLocation loc);
AstNode *import_expression(AstNode *path, SourceLocation loc);
AstNode *async_expression(AstNode *expr, SourceLocation loc);
AstNode *comptime_expression(AstNode *expr, SourceLocation loc);

/* Control */
AstNode *if_expression(AstNode *cond, AstNode *thenBr, AstNode *elseBr,
                       SourceLocation loc);
AstNode *loop_expression_infinite(AstNode *label, AstNode *body,
                                  SourceLocation loc);
AstNode *loop_expression_predicate(AstNode *label, AstNode *cond, AstNode *body,
                                   SourceLocation loc);
AstNode *loop_expression_predicate_pattern(AstNode *label, AstNode *pattern,
                                           AstNode *expr, AstNode *body,
                                           SourceLocation loc);
AstNode *loop_expression_iterator(AstNode *label, AstNode *pattern,
                                  AstNode *iter_expr, AstNode *body,
                                  SourceLocation loc);

AstNode *match_guard(AstNode *expr, SourceLocation loc);
AstNode *match_arm_head(AstNode *pattern, AstNode *guard, SourceLocation loc);
AstNode *match_arm(AstNode *attr, AstNode *head, AstNode *rhs,
                   SourceLocation loc);
AstNode *match_arm_list_append(AstNode *list, AstNode *arm);
AstNode *match_expression(AstNode *expr, AstNode *attr, AstNode *arms,
                          SourceLocation loc);

/* Catch */
AstNode *catch_expr(AstNode *expr, AstNode *binder, AstNode *handler,
                    SourceLocation loc);

/* Functions/procs */
AstNode *func_qualifiers(AstNode *async_q, AstNode *extern_q,
                         SourceLocation loc);
AstNode *async_qualifier(SourceLocation loc);
AstNode *extern_qualifier(AstNode *abi, SourceLocation loc);
AstNode *abi_node(char *owned_text, SourceLocation loc);

AstNode *function_parameters_append(AstNode *list, AstNode *param);
AstNode *function_param(AstNode *attr, AstNode *comptime, AstNode *param_type,
                        SourceLocation loc);
AstNode *comptime_qualifier(SourceLocation loc);
AstNode *function_param_pattern(AstNode *pattern, AstNode *type,
                                AstNode *default_eq, SourceLocation loc);
AstNode *eq_expr(AstNode *expr, SourceLocation loc);
AstNode *type_annotation(AstNode *type, SourceLocation loc);

AstNode *function_expression_node(AstNode *quals, AstNode *params,
                                  AstNode *ret_type, AstNode *body,
                                  int body_is_asm, SourceLocation loc);
AstNode *procedure_expression_node(AstNode *quals, AstNode *params,
                                   AstNode *ret_type, AstNode *body,
                                   int body_is_asm, SourceLocation loc);

/* Patterns */
AstNode *pattern_wildcard(SourceLocation loc);
AstNode *pattern_literal(AstNode *literal, SourceLocation loc);
AstNode *pattern_identifier(AstNode *name, AstNode *at, SourceLocation loc);
AstNode *pattern_rest(SourceLocation loc);
AstNode *pattern_range(PatternRangeKind kind, AstNode *lhs, AstNode *rhs,
                       SourceLocation loc);
AstNode *pattern_struct_field(AstNode *attr, AstNode *key, int key_is_index,
                              AstNode *pat, SourceLocation loc);
AstNode *pattern_struct_field_list_append(AstNode *list, AstNode *field);
AstNode *pattern_struct(AstNode *path, AstNode *fields, int has_etc,
                        SourceLocation loc);
AstNode *pattern_tuple_struct(AstNode *path, AstNode *items,
                              SourceLocation loc);
AstNode *pattern_tuple(AstNode *items, SourceLocation loc);
AstNode *pattern_grouped(AstNode *pat, SourceLocation loc);
AstNode *pattern_slice(AstNode *items, SourceLocation loc);
AstNode *pattern_path(AstNode *path, SourceLocation loc);

/* Types */
AstNode *type_paren(AstNode *inner, SourceLocation loc);
AstNode *type_path(AstNode *path, SourceLocation loc);
AstNode *type_tuple_append(AstNode *list, AstNode *type);
AstNode *type_noreturn(SourceLocation loc);
AstNode *type_raw_pointer(int is_const, AstNode *pointee, SourceLocation loc);
AstNode *type_array(AstNode *len_expr, AstNode *elem, SourceLocation loc);
AstNode *type_dynamic_array(AstNode *elem, SourceLocation loc);
AstNode *type_slice(AstNode *elem, SourceLocation loc);
AstNode *type_map(AstNode *key, AstNode *value, SourceLocation loc);
AstNode *type_optional(AstNode *base, SourceLocation loc);
AstNode *type_error(AstNode *variants, AstNode *decls, SourceLocation loc);
AstNode *type_simd(AstNode *lanes, AstNode *elem, SourceLocation loc);
AstNode *type_complex(AstNode *elem, SourceLocation loc);
AstNode *type_tensor_dims_append(AstNode *t, AstNode *int_lit); /* helper */
AstNode *type_tensor_new(AstNode *elem, SourceLocation loc);
AstNode *type_inferred(SourceLocation loc);

AstNode *type_struct_field(AstNode *attr, int is_pub, AstNode *name,
                           AstNode *type, SourceLocation loc);
AstNode *type_struct_field_list_append(AstNode *list, AstNode *field);
AstNode *type_struct(AstNode *fields, AstNode *decls, SourceLocation loc);

AstNode *type_enum_item(AstNode *attr, int is_pub, AstNode *name,
                        AstNode *discriminant, SourceLocation loc);
AstNode *type_enum_item_list_append(AstNode *list, AstNode *item);
AstNode *type_enum(AstNode *underlying, AstNode *items, AstNode *decls,
                   SourceLocation loc);

AstNode *type_variant_item(AstNode *attr, int is_pub, AstNode *name,
                           AstNode *body, SourceLocation loc);
AstNode *type_variant_item_list_append(AstNode *list, AstNode *item);
AstNode *type_variant(AstNode *items, AstNode *decls, SourceLocation loc);

AstNode *type_union(AstNode *fields, AstNode *decls, SourceLocation loc);

/* bare function types (maybe-named) */
AstNode *type_maybe_named_param(AstNode *attr, AstNode *name, int is_underscore,
                                AstNode *type, SourceLocation loc);
AstNode *type_maybe_named_param_list_new(SourceLocation loc);
AstNode *type_maybe_named_param_list_append(AstNode *list, AstNode *param);
AstNode *type_maybe_named_param_list_set_variadic(AstNode *list,
                                                  AstNode *vararg_attr);
AstNode *type_bare_function(AstNode *extern_q, AstNode *params,
                            AstNode *ret_type, SourceLocation loc);

AstNode *map_tail(AstNode *first_value, AstNode *rest_list, SourceLocation loc);
AstNode *pattern_struct_elems(AstNode *fields, int has_etc, SourceLocation loc);

/* Util list helpers (exposed for actions if you want) */
void nodelist_init(NodeList *L);
void nodelist_push(NodeList *L, AstNode *n);

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* AST_H */
