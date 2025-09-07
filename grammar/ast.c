#include "ast.h"
#include "parser.tab.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---------- alloc helpers ---------- */
static void *xmalloc(size_t n) {
  void *p = malloc(n);
  if (!p) {
    fprintf(stderr, "OOM\n");
    exit(1);
  }
  return p;
}
static void *xrealloc(void *p, size_t n) {
  void *r = realloc(p, n);
  if (!r) {
    fprintf(stderr, "OOM\n");
    exit(1);
  }
  return r;
}
static char *xstrdup0(const char *s) {
  if (!s)
    return NULL;
  size_t n = strlen(s) + 1;
  char *p = xmalloc(n);
  memcpy(p, s, n);
  return p;
}

/* ---------- list helpers ---------- */
void nodelist_init(NodeList *L) {
  L->items = NULL;
  L->count = 0;
  L->capacity = 0;
}
void nodelist_push(NodeList *L, AstNode *n) {
  if (L->count >= L->capacity) {
    L->capacity = L->capacity ? L->capacity * 2 : 4;
    L->items = xrealloc(L->items, L->capacity * sizeof(*L->items));
  }
  L->items[L->count++] = n;
}

/* ---------- core ---------- */
SourceLocation loc_make(int fl, int fc, int ll, int lc) {
  SourceLocation s = {fl, fc, ll, lc};
  return s;
}

AstNode *new_node(NodeType type, SourceLocation loc) {
  AstNode *n = (AstNode *)xmalloc(sizeof(AstNode));
  memset(n, 0, sizeof(*n));
  n->type = type;
  n->loc = loc;
  return n;
}

/* ---------- root/decls ---------- */
AstNode *program_node(AstNode *pkg, AstNode *decls, SourceLocation loc) {
  AstNode *n = new_node(NODE_PROGRAM, loc);
  n->data.program = (AstNodeProgram){pkg, decls};
  return n;
}
AstNode *package_decl(AstNode *name, SourceLocation loc) {
  AstNode *n = new_node(NODE_PACKAGE_DECL, loc);
  n->data.packageDecl = (AstNodePackageDecl){name};
  return n;
}
AstNode *const_decl(AstNode *pattern, AstNode *type, AstNode *expr,
                    SourceLocation loc) {
  AstNode *n = new_node(NODE_CONST_DECL, loc);
  n->data.constDecl = (AstNodeConstDecl){pattern, type, expr};
  return n;
}
AstNode *var_decl(AstNode *pattern, AstNode *type, AstNode *expr,
                  SourceLocation loc) {
  AstNode *n = new_node(NODE_VAR_DECL, loc);
  n->data.varDecl = (AstNodeVarDecl){pattern, type, expr};
  return n;
}
AstNode *decl_list_append(AstNode *list, AstNode *decl) {
  if (!decl)
    return list;
  if (!list) {
    list = new_node(NODE_DECLARATION_LIST, decl->loc);
    nodelist_init(&list->data.declList);
  }
  nodelist_push(&list->data.declList, decl);
  return list;
}

/* ---------- identifiers/paths/literals ---------- */
AstNode *identifier_node(const char *name, SourceLocation loc) {
  AstNode *n = new_node(NODE_IDENTIFIER, loc);
  n->data.identifier = (AstNodeIdentifier){xstrdup0(name)};
  return n;
}
AstNode *raw_identifier_node(const char *name, SourceLocation loc) {
  AstNode *n = new_node(NODE_RAW_IDENTIFIER, loc);
  n->data.identifier = (AstNodeIdentifier){xstrdup0(name)};
  return n;
}
AstNode *identifier_expr(const char *name, SourceLocation loc) {
  AstNode *n = new_node(NODE_IDENTIFIER_EXPR, loc);
  n->data.identifierExpr = (AstNodeIdentifierExpr){xstrdup0(name)};
  return n;
}
AstNode *path_single(AstNode *ident, SourceLocation loc) {
  AstNode *p = new_node(NODE_PATH, loc);
  nodelist_init(&p->data.path.segments);
  nodelist_push(&p->data.path.segments, ident);
  return p;
}
AstNode *path_append(AstNode *path, AstNode *ident) {
  if (!path)
    return path_single(ident, ident->loc);
  nodelist_push(&path->data.path.segments, ident);
  return path;
}
AstNode *literal_node(NodeType kind, char *owned_text, SourceLocation loc) {
  AstNode *n = new_node(kind, loc);
  n->data.literal = (AstNodeLiteral){owned_text};
  return n;
}

/* ---------- attributes ---------- */
AstNode *attr_key(AstNode *key, SourceLocation loc) {
  AstNode *n = new_node(NODE_ATTRIBUTE, loc);
  n->data.attribute = (AstNodeAttribute){key, NULL};
  return n;
}
AstNode *attr_key_value(AstNode *key, AstNode *value, SourceLocation loc) {
  AstNode *n = new_node(NODE_ATTRIBUTE, loc);
  n->data.attribute = (AstNodeAttribute){key, value};
  return n;
}
AstNode *attr_list_append(AstNode *list, AstNode *attr) {
  if (!attr)
    return list;
  if (!list) {
    list = new_node(NODE_ATTR_LIST, attr->loc);
    nodelist_init(&list->data.attrList.list);
  }
  nodelist_push(&list->data.attrList.list, attr);
  return list;
}
AstNode *attr_apply(AstNode *attrs, AstNode *target, SourceLocation loc) {
  if (!attrs)
    return target;
  AstNode *n = new_node(NODE_ATTR_APPLY, loc);
  n->data.attrApply = (AstNodeAttrApply){attrs, target};
  return n;
}

/* ---------- statements / blocks / flow ---------- */
AstNode *statement_list_append(AstNode *list, AstNode *stmt) {
  if (!stmt)
    return list;
  if (!list) {
    list = new_node(NODE_STATEMENT_LIST, stmt->loc);
    nodelist_init(&list->data.statementList.list);
  }
  nodelist_push(&list->data.statementList.list, stmt);
  return list;
}
AstNode *block_expression(AstNode *attr, AstNode *statements,
                          SourceLocation loc) {
  AstNode *n = new_node(NODE_BLOCK_EXPRESSION, loc);
  n->data.blockExpression = (AstNodeBlockExpression){attr, statements};
  return n;
}
AstNode *insert_stmt(AstNode *expr, SourceLocation loc) {
  AstNode *n = new_node(NODE_INSERT_STMT, loc);
  n->data.statement = (AstNodeStatement){expr};
  return n;
}
AstNode *defer_stmt(AstNode *expr, SourceLocation loc) {
  AstNode *n = new_node(NODE_DEFER_STMT, loc);
  n->data.statement = (AstNodeStatement){expr};
  return n;
}
AstNode *errdefer_stmt(AstNode *expr, SourceLocation loc) {
  AstNode *n = new_node(NODE_ERRDEFER_STMT, loc);
  n->data.statement = (AstNodeStatement){expr};
  return n;
}
AstNode *label_node(const char *name, SourceLocation loc) {
  AstNode *n = new_node(NODE_LABEL, loc);
  n->data.label = (AstNodeLabel){xstrdup0(name)};
  return n;
}
AstNode *continue_expr(AstNode *label, AstNode *expr, SourceLocation loc) {
  AstNode *n = new_node(NODE_CONTINUE, loc);
  n->data.cont = (AstNodeContinue){label, expr};
  return n;
}
AstNode *break_expr(AstNode *label, AstNode *expr, SourceLocation loc) {
  AstNode *n = new_node(NODE_BREAK, loc);
  n->data.brk = (AstNodeBreak){label, expr};
  return n;
}
AstNode *return_expr(AstNode *expr, SourceLocation loc) {
  AstNode *n = new_node(NODE_RETURN, loc);
  n->data.ret = (AstNodeReturn){expr};
  return n;
}
AstNode *null_expr(SourceLocation loc) { return new_node(NODE_NULL, loc); }
AstNode *undefined_expr(SourceLocation loc) {
  return new_node(NODE_UNDEFINED, loc);
}
AstNode *unreachable_expr(SourceLocation loc) {
  return new_node(NODE_UNREACHABLE_EXPR, loc);
}

/* ---------- expressions ---------- */
AstNode *expr_list_append(AstNode *list, AstNode *expr) {
  if (!expr)
    return list;
  if (!list) {
    list = new_node(NODE_EXPRESSION_LIST, expr->loc);
    nodelist_init(&list->data.exprList.list);
  }
  nodelist_push(&list->data.exprList.list, expr);
  return list;
}
AstNode *assign_expr(AstNode *lhs, AstNode *rhs, SourceLocation loc) {
  AstNode *n = new_node(NODE_ASSIGN_EXPR, loc);
  n->data.assignExpr = (AstNodeAssignExpr){lhs, rhs};
  return n;
}
AstNode *compound_assign_expr(AstNode *lhs, AstNode *rhs, Op op,
                              SourceLocation loc) {
  AstNode *n = new_node(NODE_COMPOUND_ASSIGN_EXPR, loc);
  n->data.compoundAssignExpr = (AstNodeCompoundAssignExpr){lhs, rhs, op};
  return n;
}
AstNode *binary_expr(AstNode *lhs, AstNode *rhs, Op op, SourceLocation loc) {
  AstNode *n = new_node(NODE_BINARY_EXPR, loc);
  n->data.binaryExpr = (AstNodeBinaryExpr){lhs, rhs, op};
  return n;
}
AstNode *unary_expr(AstNode *operand, Op op, SourceLocation loc) {
  AstNode *n = new_node(NODE_UNARY_EXPR, loc);
  n->data.unaryExpr = (AstNodeUnaryExpr){operand, op};
  return n;
}
int cmp_token_to_op(int token, Op *out) {
  switch (token) {
  case EQEQ:
    *out = OP_EQ;
    return 1;
  case NE:
    *out = OP_NEQ;
    return 1;
  case GT:
    *out = OP_GT;
    return 1;
  case LT:
    *out = OP_LT;
    return 1;
  case GE:
    *out = OP_GTE;
    return 1;
  case LE:
    *out = OP_LTE;
    return 1;
  default:
    return 0;
  }
}

/* ---------- postfix/selectors ---------- */
AstNode *field_access_expr(AstNode *target, AstNode *field,
                           SourceLocation loc) {
  AstNode *n = new_node(NODE_FIELD_ACCESS, loc);
  n->data.fieldAccess = (AstNodeFieldAccess){target, field};
  return n;
}
AstNode *tuple_index_expr(AstNode *target, AstNode *index, SourceLocation loc) {
  AstNode *n = new_node(NODE_TUPLE_INDEX, loc);
  n->data.tupleIndex = (AstNodeTupleIndex){target, index};
  return n;
}
AstNode *await_expr(AstNode *target, SourceLocation loc) {
  AstNode *n = new_node(NODE_AWAIT, loc);
  n->data.postfix = (AstNodePostfix){target};
  return n;
}
AstNode *type_cast_expr(AstNode *target, AstNode *type, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_CAST, loc);
  n->data.typeCast = (AstNodeTypeCast){target, type};
  return n;
}
AstNode *call_expr(AstNode *target, AstNode *params, SourceLocation loc) {
  AstNode *n = new_node(NODE_CALL, loc);
  n->data.call = (AstNodeCall){target, params};
  return n;
}
AstNode *index_expr(AstNode *target, AstNode *indexExpr, SourceLocation loc) {
  AstNode *n = new_node(NODE_INDEX, loc);
  n->data.index = (AstNodeIndex){target, indexExpr};
  return n;
}
AstNode *deref_expr(AstNode *target, SourceLocation loc) {
  AstNode *n = new_node(NODE_DEREF, loc);
  n->data.postfix = (AstNodePostfix){target};
  return n;
}
AstNode *errorprop_expr(AstNode *target, SourceLocation loc) {
  AstNode *n = new_node(NODE_ERROR_PROP, loc);
  n->data.postfix = (AstNodePostfix){target};
  return n;
}

/* ---------- grouping/collections ---------- */
AstNode *grouped_expr(AstNode *attr, AstNode *expr, SourceLocation loc) {
  AstNode *n = new_node(NODE_GROUPED_EXPR, loc);
  n->data.groupedExpr = (AstNodeGroupedExpr){attr, expr};
  return n;
}
AstNode *array_literal(AstNode *attr, AstNode *body, SourceLocation loc) {
  AstNode *n = new_node(NODE_ARRAY_LITERAL, loc);
  n->data.arrayLiteral = (AstNodeArrayLiteral){attr, body};
  return n;
}
AstNode *tuple_literal(AstNode *attr, AstNode *elements, SourceLocation loc) {
  AstNode *n = new_node(NODE_TUPLE_LITERAL, loc);
  n->data.tupleLiteral = (AstNodeTupleLiteral){attr, elements};
  return n;
}
AstNode *collection_body(AstNode *head_expr, AstNode *tail,
                         SourceLocation loc) {
  AstNode *n = new_node(NODE_COLLECTION_BODY, loc);
  n->data.collectionBody = (AstNodeCollectionBody){head_expr, tail};
  return n;
}
AstNode *map_element(AstNode *key, AstNode *value, SourceLocation loc) {
  AstNode *n = new_node(NODE_MAP_ELEMENT, loc);
  n->data.mapElement = (AstNodeMapElement){key, value};
  return n;
}
AstNode *map_element_list_append(AstNode *list, AstNode *elem) {
  if (!elem)
    return list;
  if (!list) {
    list = new_node(NODE_MAP_ELEMENT_LIST, elem->loc);
    nodelist_init(&list->data.mapElementList.list);
  }
  nodelist_push(&list->data.mapElementList.list, elem);
  return list;
}
AstNode *array_rest_element(AstNode *expr, SourceLocation loc) {
  AstNode *n = new_node(NODE_ARRAY_REST_ELEMENT, loc);
  n->data.arrayRestElement = (AstNodeArrayRestElement){expr};
  return n;
}
AstNode *array_rest_list_append(AstNode *list, AstNode *elem) {
  if (!elem)
    return list;
  if (!list) {
    list = new_node(NODE_ARRAY_REST_ELEMENT_LIST, elem->loc);
    nodelist_init(&list->data.arrayRestElementList.list);
  }
  nodelist_push(&list->data.arrayRestElementList.list, elem);
  return list;
}
AstNode *tuple_head_element(AstNode *expr, SourceLocation loc) {
  AstNode *n = new_node(NODE_TUPLE_HEAD_ELEMENT, loc);
  n->data.tupleHeadElement = (AstNodeTupleHeadElement){expr};
  return n;
}
AstNode *tuple_head_list_append(AstNode *list, AstNode *elem) {
  if (!elem)
    return list;
  if (!list) {
    list = new_node(NODE_TUPLE_HEAD_ELEMENT_LIST, elem->loc);
    nodelist_init(&list->data.tupleHeadElementList.list);
  }
  nodelist_push(&list->data.tupleHeadElementList.list, elem);
  return list;
}

/* ---------- struct / enum variant expressions ---------- */
AstNode *struct_field(AstNode *attr, AstNode *key, int key_is_index,
                      AstNode *value, SourceLocation loc) {
  AstNode *n = new_node(NODE_STRUCT_FIELD, loc);
  n->data.structField = (AstNodeStructField){attr, key, value, key_is_index};
  return n;
}
AstNode *struct_field_list_append(AstNode *list, AstNode *field) {
  if (!field)
    return list;
  if (!list) {
    list = new_node(NODE_STRUCT_FIELD_LIST, field->loc);
    nodelist_init(&list->data.structFieldList.list);
  }
  nodelist_push(&list->data.structFieldList.list, field);
  return list;
}
AstNode *struct_base(AstNode *expr, SourceLocation loc) {
  AstNode *n = new_node(NODE_STRUCT_BASE, loc);
  n->data.structBase = (AstNodeStructBase){expr};
  return n;
}
AstNode *struct_expression(AstNode *path, AstNode *attr, AstNode *fields,
                           AstNode *base, SourceLocation loc) {
  AstNode *n = new_node(NODE_STRUCT_EXPRESSION, loc);
  n->data.structExpr = (AstNodeStructExpression){path, attr, fields, base};
  return n;
}

AstNode *enum_variant_field(AstNode *key, int key_is_index, AstNode *value,
                            SourceLocation loc) {
  AstNode *n = new_node(NODE_ENUM_VARIANT_FIELD, loc);
  n->data.enumVariantField =
      (AstNodeEnumVariantField){key, value, key_is_index};
  return n;
}
AstNode *enum_variant_field_list_append(AstNode *list, AstNode *field) {
  if (!field)
    return list;
  if (!list) {
    list = new_node(NODE_ENUM_VARIANT_FIELD_LIST, field->loc);
    nodelist_init(&list->data.enumVariantFieldList.list);
  }
  nodelist_push(&list->data.enumVariantFieldList.list, field);
  return list;
}
AstNode *enum_variant_expression(AstNode *path, AstNode *fields,
                                 SourceLocation loc) {
  AstNode *n = new_node(NODE_ENUM_VARIANT_EXPRESSION, loc);
  n->data.enumVariantExpr = (AstNodeEnumVariantExpression){path, fields};
  return n;
}

/* ---------- closures ---------- */
AstNode *closure_param(AstNode *attr, AstNode *pattern, AstNode *typeAnn,
                       SourceLocation loc) {
  AstNode *n = new_node(NODE_CLOSURE_PARAM, loc);
  n->data.closureParam = (AstNodeClosureParam){attr, pattern, typeAnn};
  return n;
}
AstNode *closure_params_append(AstNode *list, AstNode *param) {
  if (!param)
    return list;
  if (!list) {
    list = new_node(NODE_CLOSURE_PARAMETERS, param->loc);
    nodelist_init(&list->data.closureParams.list);
  }
  nodelist_push(&list->data.closureParams.list, param);
  return list;
}
AstNode *closure_expression(AstNode *params, AstNode *ret_type, AstNode *body,
                            int body_is_block, SourceLocation loc) {
  AstNode *n = new_node(NODE_CLOSURE_EXPRESSION, loc);
  n->data.closureExpr =
      (AstNodeClosureExpression){params, ret_type, body, body_is_block};
  return n;
}

/* ---------- code/mlir/asm/import ---------- */
AstNode *code_expression(AstNode *statements, SourceLocation loc) {
  AstNode *n = new_node(NODE_CODE_EXPRESSION, loc);
  n->data.codeExpr = (AstNodeCodeExpression){statements};
  return n;
}
AstNode *mlir_expression(AstNode *head, AstNode *body, SourceLocation loc) {
  AstNode *n = new_node(NODE_MLIR_EXPRESSION, loc);
  n->data.mlirExpr = (AstNodeMlirExpression){head, body};
  return n;
}
AstNode *asm_expression(char *owned_text, SourceLocation loc) {
  AstNode *n = new_node(NODE_ASM_EXPRESSION, loc);
  n->data.asmExpr = (AstNodeAsmExpression){owned_text};
  return n;
}
AstNode *import_expression(AstNode *path, SourceLocation loc) {
  AstNode *n = new_node(NODE_IMPORT_EXPRESSION, loc);
  n->data.importExpr = (AstNodeImportExpression){path};
  return n;
}
AstNode *async_expression(AstNode *expr, SourceLocation loc) {
  AstNode *n = new_node(NODE_ASYNC_EXPRESSION, loc);
  n->data.asyncExpr = (AstNodeAsyncExpression){expr};
  return n;
}
AstNode *comptime_expression(AstNode *expr, SourceLocation loc) {
  AstNode *n = new_node(NODE_COMPTIME_EXPRESSION, loc);
  n->data.comptimeExpr = (AstNodeComptimeExpression){expr};
  return n;
}

/* ---------- control ---------- */
AstNode *if_expression(AstNode *cond, AstNode *thenBr, AstNode *elseBr,
                       SourceLocation loc) {
  AstNode *n = new_node(NODE_IF_EXPRESSION, loc);
  n->data.ifExpr = (AstNodeIfExpression){cond, thenBr, elseBr};
  return n;
}
AstNode *loop_expression_infinite(AstNode *label, AstNode *body,
                                  SourceLocation loc) {
  AstNode *n = new_node(NODE_LOOP_EXPRESSION, loc);
  n->data.loopExpr =
      (AstNodeLoopExpression){LOOP_INF, label, NULL, NULL, NULL, body};
  return n;
}
AstNode *loop_expression_predicate(AstNode *label, AstNode *cond, AstNode *body,
                                   SourceLocation loc) {
  AstNode *n = new_node(NODE_LOOP_EXPRESSION, loc);
  n->data.loopExpr =
      (AstNodeLoopExpression){LOOP_PREDICATE, label, cond, NULL, NULL, body};
  return n;
}
AstNode *loop_expression_predicate_pattern(AstNode *label, AstNode *pattern,
                                           AstNode *expr, AstNode *body,
                                           SourceLocation loc) {
  AstNode *n = new_node(NODE_LOOP_EXPRESSION, loc);
  n->data.loopExpr = (AstNodeLoopExpression){
      LOOP_PREDICATE_PATTERN, label, NULL, pattern, expr, body};
  return n;
}
AstNode *loop_expression_iterator(AstNode *label, AstNode *pattern,
                                  AstNode *iter_expr, AstNode *body,
                                  SourceLocation loc) {
  AstNode *n = new_node(NODE_LOOP_EXPRESSION, loc);
  n->data.loopExpr = (AstNodeLoopExpression){LOOP_ITERATOR, label,     NULL,
                                             pattern,       iter_expr, body};
  return n;
}

AstNode *match_guard(AstNode *expr, SourceLocation loc) {
  AstNode *n = new_node(NODE_MATCH_GUARD, loc);
  n->data.matchGuard = (AstNodeMatchGuard){expr};
  return n;
}
AstNode *match_arm_head(AstNode *pattern, AstNode *guard, SourceLocation loc) {
  AstNode *n =
      new_node(NODE_MATCH_ARM,
               loc); /* temporary; we’ll fill in head-only in aux fields */
  /* reuse fields: attr=NULL, head=(pattern+guard), rhs=NULL here */
  n->data.matchArm = (AstNodeMatchArm){NULL, NULL, NULL};
  /* stash pattern/guard into head via matchGuard as attr? cleaner approach:
   * represent head as attrApply: attrs=NULL,target=pattern; guard stored
   * separately */
  AstNode *h = new_node(NODE_MATCH_GUARD, loc);
  h->data.matchGuard = (AstNodeMatchGuard){guard};
  n->data.matchArm.head = pattern; /* primary */
  n->data.matchArm.attr =
      h; /* abuse attr to carry guard-node during assembly */
  return n;
}
AstNode *match_arm(AstNode *attr, AstNode *headTmp, AstNode *rhs,
                   SourceLocation loc) {
  AstNode *guard = NULL;
  if (headTmp && headTmp->type == NODE_MATCH_ARM) {
    AstNode *hnode = headTmp->data.matchArm.attr;
    if (hnode && hnode->type == NODE_MATCH_GUARD)
      guard = hnode->data.matchGuard.expr;
    headTmp = headTmp->data.matchArm.head;
  }
  AstNode *n = new_node(NODE_MATCH_ARM, loc);
  AstNode *head =
      new_node(NODE_MATCH_GUARD, loc); /* reuse holder: pattern in expr, guard
                                          in .expr of a nested node? */
  head->data.matchGuard = (AstNodeMatchGuard){guard};
  n->data.matchArm = (AstNodeMatchArm){attr, headTmp, rhs};
  /* keep guard separately in head via guard node (head is pattern; guard
   * accessible separately if needed) */
  n->data.matchArm.head = headTmp;
  n->data.matchArm.attr = attr ? attr : NULL;
  /* store guard alongside by creating a NODE_MATCH_GUARD node as 'rhs' sibling
   * is clumsy; you may keep it as separate field if you prefer later */
  if (guard) {
    /* attach guard onto attr via attrApply to not lose it */
    AstNode *wrap = attr_apply(NULL, guard, loc);
    (void)wrap; /* optional */
  }
  return n;
}
AstNode *match_arm_list_append(AstNode *list, AstNode *arm) {
  if (!arm)
    return list;
  if (!list) {
    list = new_node(NODE_MATCH_ARM_LIST, arm->loc);
    nodelist_init(&list->data.matchArmList.list);
  }
  nodelist_push(&list->data.matchArmList.list, arm);
  return list;
}
AstNode *match_expression(AstNode *expr, AstNode *attr, AstNode *arms,
                          SourceLocation loc) {
  AstNode *n = new_node(NODE_MATCH_EXPRESSION, loc);
  n->data.matchExpr = (AstNodeMatchExpression){expr, attr, arms};
  return n;
}

/* ---------- catch ---------- */
AstNode *catch_expr(AstNode *expr, AstNode *binder, AstNode *handler,
                    SourceLocation loc) {
  AstNode *n = new_node(NODE_CATCH_EXPR, loc);
  n->data.catchExpr = (AstNodeCatchExpr){expr, binder, handler};
  return n;
}

/* ---------- functions/procs ---------- */
AstNode *func_qualifiers(AstNode *async_q, AstNode *extern_q,
                         SourceLocation loc) {
  AstNode *n = new_node(NODE_FUNCTION_QUALIFIERS, loc);
  n->data.funcQuals = (AstNodeFunctionQualifiers){async_q, extern_q};
  return n;
}
AstNode *async_qualifier(SourceLocation loc) {
  return new_node(NODE_ASYNC_QUALIFIER, loc);
}
AstNode *extern_qualifier(AstNode *abi, SourceLocation loc) {
  AstNode *n = new_node(NODE_EXTERN_QUALIFIER, loc);
  n->data.externQual = (AstNodeExternQualifier){abi};
  return n;
}
AstNode *abi_node(char *owned_text, SourceLocation loc) {
  AstNode *n = new_node(NODE_ABI, loc);
  n->data.abi = (AstNodeAbi){owned_text};
  return n;
}
AstNode *function_parameters_append(AstNode *list, AstNode *param) {
  if (!param)
    return list;
  if (!list) {
    list = new_node(NODE_FUNCTION_PARAMETERS, param->loc);
    nodelist_init(&list->data.funcParams.list);
  }
  nodelist_push(&list->data.funcParams.list, param);
  return list;
}
AstNode *function_param(AstNode *attr, AstNode *comptime, AstNode *param_type,
                        SourceLocation loc) {
  AstNode *n = new_node(NODE_FUNCTION_PARAM, loc);
  n->data.funcParam = (AstNodeFunctionParam){attr, comptime, param_type};
  return n;
}
AstNode *comptime_qualifier(SourceLocation loc) {
  return new_node(NODE_COMPTIME_QUALIFIER, loc);
}
AstNode *function_param_pattern(AstNode *pattern, AstNode *type,
                                AstNode *default_eq, SourceLocation loc) {
  AstNode *n = new_node(NODE_FUNCTION_PARAM_PATTERN, loc);
  n->data.funcParamPattern =
      (AstNodeFunctionParamPattern){pattern, type, default_eq};
  return n;
}
AstNode *eq_expr(AstNode *expr, SourceLocation loc) {
  AstNode *n = new_node(NODE_EQ_EXPR, loc);
  n->data.eqExpr = (AstNodeEqExpr){expr};
  return n;
}
AstNode *type_annotation(AstNode *type, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_ANNOTATION, loc);
  n->data.typeAnn = (AstNodeTypeAnnotation){type};
  return n;
}
AstNode *function_expression_node(AstNode *quals, AstNode *params,
                                  AstNode *ret_type, AstNode *body,
                                  int body_is_asm, SourceLocation loc) {
  AstNode *n = new_node(NODE_FUNCTION_EXPRESSION, loc);
  n->data.funcExpr =
      (AstNodeFunctionExpression){quals, params, ret_type, body, body_is_asm};
  return n;
}
AstNode *procedure_expression_node(AstNode *quals, AstNode *params,
                                   AstNode *ret_type, AstNode *body,
                                   int body_is_asm, SourceLocation loc) {
  AstNode *n = new_node(NODE_PROCEDURE_EXPRESSION, loc);
  n->data.procExpr =
      (AstNodeProcedureExpression){quals, params, ret_type, body, body_is_asm};
  return n;
}

/* ---------- patterns ---------- */
AstNode *pattern_wildcard(SourceLocation loc) {
  return new_node(NODE_PATTERN_WILDCARD, loc);
}
AstNode *pattern_literal(AstNode *literal, SourceLocation loc) {
  AstNode *n = new_node(NODE_PATTERN_LITERAL, loc);
  n->data.patLiteral = (AstNodePatternLiteral){literal};
  return n;
}
AstNode *pattern_identifier(AstNode *name, AstNode *at, SourceLocation loc) {
  AstNode *n = new_node(NODE_PATTERN_IDENTIFIER, loc);
  n->data.patIdent = (AstNodePatternIdentifier){name, at};
  return n;
}
AstNode *pattern_rest(SourceLocation loc) {
  return new_node(NODE_PATTERN_REST, loc);
}
AstNode *pattern_range(PatternRangeKind kind, AstNode *lhs, AstNode *rhs,
                       SourceLocation loc) {
  AstNode *n = new_node(NODE_PATTERN_RANGE, loc);
  n->data.patRange = (AstNodePatternRange){kind, lhs, rhs};
  return n;
}
AstNode *pattern_struct_field(AstNode *attr, AstNode *key, int key_is_index,
                              AstNode *pat, SourceLocation loc) {
  AstNode *n = new_node(NODE_PATTERN_STRUCT_FIELD, loc);
  n->data.patStructField =
      (AstNodePatternStructField){attr, key, pat, key_is_index};
  return n;
}
AstNode *pattern_struct_field_list_append(AstNode *list, AstNode *field) {
  if (!field)
    return list;
  if (!list) {
    list = new_node(NODE_PATTERN_STRUCT_FIELD_LIST, field->loc);
    nodelist_init(&list->data.patStructFieldList.list);
  }
  nodelist_push(&list->data.patStructFieldList.list, field);
  return list;
}
AstNode *pattern_struct(AstNode *path, AstNode *fields, int has_etc,
                        SourceLocation loc) {
  AstNode *n = new_node(NODE_PATTERN_STRUCT, loc);
  n->data.patStruct = (AstNodePatternStruct){path, fields, has_etc};
  return n;
}
AstNode *pattern_tuple_struct(AstNode *path, AstNode *items,
                              SourceLocation loc) {
  AstNode *n = new_node(NODE_PATTERN_TUPLE_STRUCT, loc);
  n->data.patTupleStruct = (AstNodePatternTupleStruct){path, items};
  return n;
}
AstNode *pattern_tuple(AstNode *items, SourceLocation loc) {
  AstNode *n = new_node(NODE_PATTERN_TUPLE, loc);
  n->data.patTuple = (AstNodePatternTuple){items};
  return n;
}
AstNode *pattern_grouped(AstNode *pat, SourceLocation loc) {
  AstNode *n = new_node(NODE_PATTERN_GROUPED, loc);
  n->data.patGrouped = (AstNodePatternGrouped){pat};
  return n;
}
AstNode *pattern_slice(AstNode *items, SourceLocation loc) {
  AstNode *n = new_node(NODE_PATTERN_SLICE, loc);
  n->data.patSlice = (AstNodePatternSlice){items};
  return n;
}
AstNode *pattern_path(AstNode *path, SourceLocation loc) {
  AstNode *n = new_node(NODE_PATTERN_PATH, loc);
  n->data.patPath = (AstNodePatternPath){path};
  return n;
}

/* ---------- types ---------- */
AstNode *type_paren(AstNode *inner, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_PAREN, loc);
  n->data.tParen = (AstNodeTypeParen){inner};
  return n;
}
AstNode *type_path(AstNode *path, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_PATH, loc);
  n->data.tPath = (AstNodeTypePath){path};
  return n;
}
AstNode *type_tuple_append(AstNode *list, AstNode *type) {
  if (!type)
    return list;
  if (!list) {
    list = new_node(NODE_TYPE_TUPLE, type->loc);
    nodelist_init(&list->data.tTuple.list);
  }
  nodelist_push(&list->data.tTuple.list, type);
  return list;
}
AstNode *type_noreturn(SourceLocation loc) {
  return new_node(NODE_TYPE_NORETURN, loc);
}
AstNode *type_raw_pointer(int is_const, AstNode *pointee, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_RAW_POINTER, loc);
  n->data.tRawPtr = (AstNodeTypeRawPointer){is_const, pointee};
  return n;
}
AstNode *type_array(AstNode *len_expr, AstNode *elem, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_ARRAY, loc);
  n->data.tArray = (AstNodeTypeArray){len_expr, elem};
  return n;
}
AstNode *type_dynamic_array(AstNode *elem, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_DYNAMIC_ARRAY, loc);
  n->data.tDynArray = (AstNodeTypeDynamicArray){elem};
  return n;
}
AstNode *type_slice(AstNode *elem, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_SLICE, loc);
  n->data.tSlice = (AstNodeTypeSlice){elem};
  return n;
}
AstNode *type_map(AstNode *key, AstNode *value, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_MAP, loc);
  n->data.tMap = (AstNodeTypeMap){key, value};
  return n;
}
AstNode *type_optional(AstNode *base, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_OPTIONAL, loc);
  n->data.tOpt = (AstNodeTypeOptional){base};
  return n;
}
AstNode *type_error(AstNode *variants, AstNode *decls, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_ERROR, loc);
  n->data.tError = (AstNodeTypeError){variants, decls};
  return n;
}
AstNode *type_simd(AstNode *lanes, AstNode *elem, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_SIMD, loc);
  n->data.tSimd = (AstNodeTypeSimd){lanes, elem};
  return n;
}
AstNode *type_complex(AstNode *elem, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_COMPLEX, loc);
  n->data.tComplex = (AstNodeTypeComplex){elem};
  return n;
}
AstNode *type_tensor_new(AstNode *elem, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_TENSOR, loc);
  nodelist_init(&n->data.tTensor.dims);
  n->data.tTensor.elem = elem;
  return n;
}
AstNode *type_tensor_dims_append(AstNode *t, AstNode *int_lit) {
  if (!t || t->type != NODE_TYPE_TENSOR)
    return t;
  nodelist_push(&t->data.tTensor.dims, int_lit);
  return t;
}
AstNode *type_inferred(SourceLocation loc) {
  return new_node(NODE_TYPE_INFERRED, loc);
}

AstNode *type_struct_field(AstNode *attr, int is_pub, AstNode *name,
                           AstNode *type, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_STRUCT_FIELD, loc);
  n->data.tStructField = (AstNodeTypeStructField){attr, is_pub, name, type};
  return n;
}
AstNode *type_struct_field_list_append(AstNode *list, AstNode *field) {
  if (!field)
    return list;
  if (!list) {
    list = new_node(NODE_TYPE_STRUCT_FIELD_LIST, field->loc);
    nodelist_init(&list->data.tStructFieldList.list);
  }
  nodelist_push(&list->data.tStructFieldList.list, field);
  return list;
}
AstNode *type_struct(AstNode *fields, AstNode *decls, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_STRUCT, loc);
  n->data.tStruct = (AstNodeTypeStruct){fields, decls};
  return n;
}

AstNode *type_enum_item(AstNode *attr, int is_pub, AstNode *name,
                        AstNode *discriminant, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_ENUM_ITEM, loc);
  n->data.tEnumItem = (AstNodeTypeEnumItem){attr, is_pub, name, discriminant};
  return n;
}
AstNode *type_enum_item_list_append(AstNode *list, AstNode *item) {
  if (!item)
    return list;
  if (!list) {
    list = new_node(NODE_TYPE_ENUM_ITEM_LIST, item->loc);
    nodelist_init(&list->data.tEnumItemList.list);
  }
  nodelist_push(&list->data.tEnumItemList.list, item);
  return list;
}
AstNode *type_enum(AstNode *underlying, AstNode *items, AstNode *decls,
                   SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_ENUM, loc);
  n->data.tEnum = (AstNodeTypeEnum){underlying, items, decls};
  return n;
}

AstNode *type_variant_item(AstNode *attr, int is_pub, AstNode *name,
                           AstNode *body, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_VARIANT_ITEM, loc);
  n->data.tVarItem = (AstNodeTypeVariantItem){attr, is_pub, name, body};
  return n;
}
AstNode *type_variant_item_list_append(AstNode *list, AstNode *item) {
  if (!item)
    return list;
  if (!list) {
    list = new_node(NODE_TYPE_VARIANT_ITEM_LIST, item->loc);
    nodelist_init(&list->data.tVarItemList.list);
  }
  nodelist_push(&list->data.tVarItemList.list, item);
  return list;
}
AstNode *type_variant(AstNode *items, AstNode *decls, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_VARIANT, loc);
  n->data.tVariant = (AstNodeTypeVariant){items, decls};
  return n;
}

AstNode *type_union(AstNode *fields, AstNode *decls, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_UNION, loc);
  n->data.tUnion = (AstNodeTypeUnion){fields, decls};
  return n;
}

/* bare function types */
AstNode *type_maybe_named_param(AstNode *attr, AstNode *name, int is_underscore,
                                AstNode *type, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_MAYBE_NAMED_PARAM, loc);
  n->data.tMaybeNamedParam =
      (AstNodeTypeMaybeNamedParam){attr, name, is_underscore, type};
  return n;
}
AstNode *type_maybe_named_param_list_new(SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_MAYBE_NAMED_PARAM_LIST, loc);
  nodelist_init(&n->data.tMaybeNamedParamList.list);
  n->data.tMaybeNamedParamList.has_variadic = 0;
  n->data.tMaybeNamedParamList.vararg_attr = NULL;
  return n;
}
AstNode *type_maybe_named_param_list_append(AstNode *list, AstNode *param) {
  if (!list)
    list = type_maybe_named_param_list_new(param ? param->loc
                                                 : loc_make(0, 0, 0, 0));
  nodelist_push(&list->data.tMaybeNamedParamList.list, param);
  return list;
}
AstNode *type_maybe_named_param_list_set_variadic(AstNode *list,
                                                  AstNode *vararg_attr) {
  if (!list)
    list = type_maybe_named_param_list_new(loc_make(0, 0, 0, 0));
  list->data.tMaybeNamedParamList.has_variadic = 1;
  list->data.tMaybeNamedParamList.vararg_attr = vararg_attr;
  return list;
}
AstNode *type_bare_function(AstNode *extern_q, AstNode *params,
                            AstNode *ret_type, SourceLocation loc) {
  AstNode *n = new_node(NODE_TYPE_BARE_FUNCTION, loc);
  n->data.tBareFn = (AstNodeTypeBareFunction){extern_q, params, ret_type};
  return n;
}

AstNode *map_tail(AstNode *first_value, AstNode *rest_list,
                  SourceLocation loc) {
  AstNode *n = new_node(NODE_MAP_TAIL, loc);
  n->data.mapTail = (AstNodeMapTail){first_value, rest_list};
  return n;
}

AstNode *pattern_struct_elems(AstNode *fields, int has_etc,
                              SourceLocation loc) {
  AstNode *n = new_node(NODE_PATTERN_STRUCT_ELEMS, loc);
  n->data.patStructElems = (AstNodePatternStructElems){fields, has_etc};
  return n;
}
