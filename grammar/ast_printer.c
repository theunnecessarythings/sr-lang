#include "ast.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Simple, readable AST printer.
 * Usage: after parsing, call:
 *   extern AstNode *ast_root; // from parser
 *   ast_print(ast_root, stdout);
 */

static void ast_print_node(const AstNode *n, int indent, FILE *out);
static void print_indent(int n, FILE *out) {
  while (n--)
    fputc(' ', out);
}
static void print_loc(SourceLocation loc, FILE *out) {
  fprintf(out, " @%d:%d-%d:%d", loc.first_line, loc.first_column, loc.last_line,
          loc.last_column);
}

static const char *op_name(Op op) {
  switch (op) {
  case OP_ADD:
    return "+";
  case OP_SUB:
    return "-";
  case OP_MUL:
    return "*";
  case OP_DIV:
    return "/";
  case OP_MOD:
    return "%";
  case OP_OR:
    return "or";
  case OP_AND:
    return "and";
  case OP_XOR:
    return "xor";
  case OP_SHL:
    return "<<";
  case OP_SHR:
    return ">>";
  case OP_EQ:
    return "==";
  case OP_NEQ:
    return "!=";
  case OP_LT:
    return "<";
  case OP_LTE:
    return "<=";
  case OP_GT:
    return ">";
  case OP_GTE:
    return ">=";
  case OP_ORELSE:
    return "orelse";
  case OP_DOTDOT:
    return "..";
  case OP_DOTDOTEQ:
    return "..=";
  case OP_BOR:
    return "|";
  case OP_BXOR:
    return "^";
  case OP_BAND:
    return "&";
  case OP_SHL_SAT:
    return "<<<";
  case OP_ADD_SAT:
    return "+|";
  case OP_SUB_SAT:
    return "-|";
  case OP_ADD_WRAP:
    return "+%";
  case OP_SUB_WRAP:
    return "-%";
  case OP_MUL_SAT:
    return "*|";
  case OP_MUL_WRAP:
    return "*%";
  case OP_ADDR:
    return "& (addr)";
  case OP_NEG:
    return "- (neg)";
  case OP_NOT:
    return "!";
  case OP_ADD_ASSIGN:
    return "+=";
  case OP_SUB_ASSIGN:
    return "-=";
  case OP_MUL_ASSIGN:
    return "*=";
  case OP_DIV_ASSIGN:
    return "/=";
  case OP_MOD_ASSIGN:
    return "%=";
  case OP_AND_ASSIGN:
    return "&=";
  case OP_OR_ASSIGN:
    return "|=";
  case OP_XOR_ASSIGN:
    return "^=";
  case OP_SHL_ASSIGN:
    return "<<=";
  case OP_SHR_ASSIGN:
    return ">>=";
  case OP_ADD_SAT_ASSIGN:
    return "+|=";
  case OP_SUB_SAT_ASSIGN:
    return "-|=";
  case OP_MUL_SAT_ASSIGN:
    return "*|=";
  case OP_SHL_SAT_ASSIGN:
    return "<<<=";
  case OP_ADD_WRAP_ASSIGN:
    return "+%=";
  case OP_SUB_WRAP_ASSIGN:
    return "-%=";
  case OP_MUL_WRAP_ASSIGN:
    return "*%=";
  }
  return "?op";
}

static void print_list(const NodeList *L, int indent, FILE *out) {
  if (!L || L->count == 0) {
    print_indent(indent, out);
    fprintf(out, "[]\n");
    return;
  }
  for (size_t i = 0; i < L->count; ++i) {
    ast_print_node(L->items[i], indent, out);
  }
}

static const char *node_name(NodeType t) {
  switch (t) {
  case NODE_UNKNOWN:
    return "UNKNOWN";
  case NODE_PROGRAM:
    return "PROGRAM";
  case NODE_PACKAGE_DECL:
    return "PACKAGE_DECL";
  case NODE_DECLARATION_LIST:
    return "DECLARATION_LIST";
  case NODE_CONST_DECL:
    return "CONST_DECL";
  case NODE_VAR_DECL:
    return "VAR_DECL";
  case NODE_IDENTIFIER:
    return "IDENTIFIER";
  case NODE_RAW_IDENTIFIER:
    return "RAW_IDENTIFIER";
  case NODE_PATH:
    return "PATH";
  case NODE_IDENTIFIER_EXPR:
    return "IDENTIFIER_EXPR";
  case NODE_INTEGER_LITERAL:
    return "INTEGER_LITERAL";
  case NODE_STRING_LITERAL:
    return "STRING_LITERAL";
  case NODE_RAW_STRING_LITERAL:
    return "RAW_STRING_LITERAL";
  case NODE_CHAR_LITERAL:
    return "CHAR_LITERAL";
  case NODE_FLOAT_LITERAL:
    return "FLOAT_LITERAL";
  case NODE_IMAGINARY_LITERAL:
    return "IMAGINARY_LITERAL";
  case NODE_BYTE_LITERAL:
    return "BYTE_LITERAL";
  case NODE_BYTE_STRING_LITERAL:
    return "BYTE_STRING_LITERAL";
  case NODE_RAW_BYTE_STRING_LITERAL:
    return "RAW_BYTE_STRING_LITERAL";
  case NODE_BOOL_LITERAL:
    return "BOOL_LITERAL";
  case NODE_ATTRIBUTE:
    return "ATTRIBUTE";
  case NODE_ATTR_LIST:
    return "ATTR_LIST";
  case NODE_ATTR_APPLY:
    return "ATTR_APPLY";
  case NODE_STATEMENT_LIST:
    return "STATEMENT_LIST";
  case NODE_BLOCK_EXPRESSION:
    return "BLOCK_EXPRESSION";
  case NODE_INSERT_STMT:
    return "INSERT_STMT";
  case NODE_DEFER_STMT:
    return "DEFER_STMT";
  case NODE_ERRDEFER_STMT:
    return "ERRDEFER_STMT";
  case NODE_CONTINUE:
    return "CONTINUE";
  case NODE_BREAK:
    return "BREAK";
  case NODE_RETURN:
    return "RETURN";
  case NODE_LABEL:
    return "LABEL";
  case NODE_NULL:
    return "NULL";
  case NODE_UNDEFINED:
    return "UNDEFINED";
  case NODE_UNREACHABLE_EXPR:
    return "UNREACHABLE_EXPR";
  case NODE_EXPRESSION_LIST:
    return "EXPRESSION_LIST";
  case NODE_ASSIGN_EXPR:
    return "ASSIGN_EXPR";
  case NODE_COMPOUND_ASSIGN_EXPR:
    return "COMPOUND_ASSIGN_EXPR";
  case NODE_BINARY_EXPR:
    return "BINARY_EXPR";
  case NODE_UNARY_EXPR:
    return "UNARY_EXPR";
  case NODE_FIELD_ACCESS:
    return "FIELD_ACCESS";
  case NODE_TUPLE_INDEX:
    return "TUPLE_INDEX";
  case NODE_AWAIT:
    return "AWAIT";
  case NODE_TYPE_CAST:
    return "TYPE_CAST";
  case NODE_CALL:
    return "CALL";
  case NODE_INDEX:
    return "INDEX";
  case NODE_DEREF:
    return "DEREF";
  case NODE_ERROR_PROP:
    return "ERROR_PROP";
  case NODE_GROUPED_EXPR:
    return "GROUPED_EXPR";
  case NODE_ARRAY_LITERAL:
    return "ARRAY_LITERAL";
  case NODE_TUPLE_LITERAL:
    return "TUPLE_LITERAL";
  case NODE_COLLECTION_BODY:
    return "COLLECTION_BODY";
  case NODE_MAP_ELEMENT:
    return "MAP_ELEMENT";
  case NODE_MAP_ELEMENT_LIST:
    return "MAP_ELEMENT_LIST";
  case NODE_ARRAY_REST_ELEMENT:
    return "ARRAY_REST_ELEMENT";
  case NODE_ARRAY_REST_ELEMENT_LIST:
    return "ARRAY_REST_ELEMENT_LIST";
  case NODE_TUPLE_HEAD_ELEMENT:
    return "TUPLE_HEAD_ELEMENT";
  case NODE_TUPLE_HEAD_ELEMENT_LIST:
    return "TUPLE_HEAD_ELEMENT_LIST";
  case NODE_STRUCT_EXPRESSION:
    return "STRUCT_EXPRESSION";
  case NODE_STRUCT_FIELD:
    return "STRUCT_FIELD";
  case NODE_STRUCT_FIELD_LIST:
    return "STRUCT_FIELD_LIST";
  case NODE_STRUCT_BASE:
    return "STRUCT_BASE";
  case NODE_ENUM_VARIANT_EXPRESSION:
    return "ENUM_VARIANT_EXPRESSION";
  case NODE_ENUM_VARIANT_FIELD:
    return "ENUM_VARIANT_FIELD";
  case NODE_ENUM_VARIANT_FIELD_LIST:
    return "ENUM_VARIANT_FIELD_LIST";
  case NODE_CLOSURE_EXPRESSION:
    return "CLOSURE_EXPRESSION";
  case NODE_CLOSURE_PARAMETERS:
    return "CLOSURE_PARAMETERS";
  case NODE_CLOSURE_PARAM:
    return "CLOSURE_PARAM";
  case NODE_CODE_EXPRESSION:
    return "CODE_EXPRESSION";
  case NODE_MLIR_EXPRESSION:
    return "MLIR_EXPRESSION";
  case NODE_ASM_EXPRESSION:
    return "ASM_EXPRESSION";
  case NODE_IMPORT_EXPRESSION:
    return "IMPORT_EXPRESSION";
  case NODE_ASYNC_EXPRESSION:
    return "ASYNC_EXPRESSION";
  case NODE_COMPTIME_EXPRESSION:
    return "COMPTIME_EXPRESSION";
  case NODE_IF_EXPRESSION:
    return "IF_EXPRESSION";
  case NODE_LOOP_EXPRESSION:
    return "LOOP_EXPRESSION";
  case NODE_MATCH_EXPRESSION:
    return "MATCH_EXPRESSION";
  case NODE_MATCH_ARM:
    return "MATCH_ARM";
  case NODE_MATCH_ARM_LIST:
    return "MATCH_ARM_LIST";
  case NODE_MATCH_GUARD:
    return "MATCH_GUARD";
  case NODE_CATCH_EXPR:
    return "CATCH_EXPR";
  case NODE_FUNCTION_EXPRESSION:
    return "FUNCTION_EXPRESSION";
  case NODE_PROCEDURE_EXPRESSION:
    return "PROCEDURE_EXPRESSION";
  case NODE_FUNCTION_QUALIFIERS:
    return "FUNCTION_QUALIFIERS";
  case NODE_ASYNC_QUALIFIER:
    return "ASYNC_QUALIFIER";
  case NODE_EXTERN_QUALIFIER:
    return "EXTERN_QUALIFIER";
  case NODE_ABI:
    return "ABI";
  case NODE_FUNCTION_PARAMETERS:
    return "FUNCTION_PARAMETERS";
  case NODE_FUNCTION_PARAM:
    return "FUNCTION_PARAM";
  case NODE_ELLIPSIS:
    return "ELLIPSIS";
  case NODE_COMPTIME_QUALIFIER:
    return "COMPTIME_QUALIFIER";
  case NODE_FUNCTION_PARAM_PATTERN:
    return "FUNCTION_PARAM_PATTERN";
  case NODE_EQ_EXPR:
    return "EQ_EXPR";
  case NODE_TYPE_ANNOTATION:
    return "TYPE_ANNOTATION";
  case NODE_PATTERN_WILDCARD:
    return "PATTERN_WILDCARD";
  case NODE_PATTERN_LITERAL:
    return "PATTERN_LITERAL";
  case NODE_PATTERN_IDENTIFIER:
    return "PATTERN_IDENTIFIER";
  case NODE_PATTERN_REST:
    return "PATTERN_REST";
  case NODE_PATTERN_RANGE:
    return "PATTERN_RANGE";
  case NODE_PATTERN_STRUCT:
    return "PATTERN_STRUCT";
  case NODE_PATTERN_STRUCT_FIELD:
    return "PATTERN_STRUCT_FIELD";
  case NODE_PATTERN_STRUCT_FIELD_LIST:
    return "PATTERN_STRUCT_FIELD_LIST";
  case NODE_PATTERN_TUPLE_STRUCT:
    return "PATTERN_TUPLE_STRUCT";
  case NODE_PATTERN_TUPLE:
    return "PATTERN_TUPLE";
  case NODE_PATTERN_GROUPED:
    return "PATTERN_GROUPED";
  case NODE_PATTERN_SLICE:
    return "PATTERN_SLICE";
  case NODE_PATTERN_PATH:
    return "PATTERN_PATH";
  case NODE_TYPE_PAREN:
    return "TYPE_PAREN";
  case NODE_TYPE_PATH:
    return "TYPE_PATH";
  case NODE_TYPE_TUPLE:
    return "TYPE_TUPLE";
  case NODE_TYPE_NORETURN:
    return "TYPE_NORETURN";
  case NODE_TYPE_RAW_POINTER:
    return "TYPE_RAW_POINTER";
  case NODE_TYPE_ARRAY:
    return "TYPE_ARRAY";
  case NODE_TYPE_DYNAMIC_ARRAY:
    return "TYPE_DYNAMIC_ARRAY";
  case NODE_TYPE_SLICE:
    return "TYPE_SLICE";
  case NODE_TYPE_MAP:
    return "TYPE_MAP";
  case NODE_TYPE_OPTIONAL:
    return "TYPE_OPTIONAL";
  case NODE_TYPE_ERROR:
    return "TYPE_ERROR";
  case NODE_TYPE_SIMD:
    return "TYPE_SIMD";
  case NODE_TYPE_COMPLEX:
    return "TYPE_COMPLEX";
  case NODE_TYPE_TENSOR:
    return "TYPE_TENSOR";
  case NODE_TYPE_INFERRED:
    return "TYPE_INFERRED";
  case NODE_TYPE_STRUCT:
    return "TYPE_STRUCT";
  case NODE_TYPE_ENUM:
    return "TYPE_ENUM";
  case NODE_TYPE_VARIANT:
    return "TYPE_VARIANT";
  case NODE_TYPE_UNION:
    return "TYPE_UNION";
  case NODE_TYPE_BARE_FUNCTION:
    return "TYPE_BARE_FUNCTION";
  case NODE_TYPE_STRUCT_FIELD:
    return "TYPE_STRUCT_FIELD";
  case NODE_TYPE_STRUCT_FIELD_LIST:
    return "TYPE_STRUCT_FIELD_LIST";
  case NODE_TYPE_ENUM_ITEM:
    return "TYPE_ENUM_ITEM";
  case NODE_TYPE_ENUM_ITEM_LIST:
    return "TYPE_ENUM_ITEM_LIST";
  case NODE_TYPE_VARIANT_ITEM:
    return "TYPE_VARIANT_ITEM";
  case NODE_TYPE_VARIANT_ITEM_LIST:
    return "TYPE_VARIANT_ITEM_LIST";
  case NODE_TYPE_MAYBE_NAMED_PARAM:
    return "TYPE_MAYBE_NAMED_PARAM";
  case NODE_TYPE_MAYBE_NAMED_PARAM_LIST:
    return "TYPE_MAYBE_NAMED_PARAM_LIST";
  /* Custom nodes you added in your patch: */
  case NODE_MAP_TAIL:
    return "MAP_TAIL";
  case NODE_PATTERN_STRUCT_ELEMS:
    return "PATTERN_STRUCT_ELEMS";
  }
  return "(unknown node)";
}

static void print_string_or_null(const char *s, FILE *out) {
  if (!s) {
    fprintf(out, "null");
    return;
  }
  fputc('"', out);
  for (const char *p = s; *p; ++p) {
    if (*p == '\\' || *p == '"') {
      fputc('\\', out);
      fputc(*p, out);
    } else if (*p == '\n') {
      fputs("\\n", out);
    } else if (*p == '\t') {
      fputs("\\t", out);
    } else {
      fputc(*p, out);
    }
  }
  fputc('"', out);
}

static void print_path(const AstNode *p, int indent, FILE *out) {
  print_indent(indent, out);
  fprintf(out, "PATH");
  print_loc(p->loc, out);
  fputc('\n', out);
  const NodeList *L = &p->data.path.segments;
  for (size_t i = 0; i < L->count; ++i) {
    const AstNode *seg = L->items[i];
    print_indent(indent + 2, out);
    if (seg->type == NODE_IDENTIFIER || seg->type == NODE_RAW_IDENTIFIER) {
      fprintf(out, "SEG: ");
      print_string_or_null(seg->data.identifier.name, out);
      fputc('\n', out);
    } else {
      ast_print_node(seg, indent + 2, out);
    }
  }
}

static void ast_print_node(const AstNode *n, int indent, FILE *out) {
  if (!n) {
    print_indent(indent, out);
    fprintf(out, "<null>\n");
    return;
  }
  /* Header */
  print_indent(indent, out);
  fprintf(out, "%s", node_name(n->type));
  print_loc(n->loc, out);

  /* Lightweight inline summaries for common leaf data */
  switch (n->type) {
  case NODE_IDENTIFIER:
  case NODE_RAW_IDENTIFIER:
    fprintf(out, " ");
    print_string_or_null(n->data.identifier.name, out);
    fputc('\n', out);
    return;
  case NODE_IDENTIFIER_EXPR:
    fprintf(out, " name=");
    print_string_or_null(n->data.identifierExpr.name, out);
    fputc('\n', out);
    return;
  case NODE_INTEGER_LITERAL:
  case NODE_STRING_LITERAL:
  case NODE_RAW_STRING_LITERAL:
  case NODE_CHAR_LITERAL:
  case NODE_FLOAT_LITERAL:
  case NODE_IMAGINARY_LITERAL:
  case NODE_BYTE_LITERAL:
  case NODE_BYTE_STRING_LITERAL:
  case NODE_RAW_BYTE_STRING_LITERAL:
  case NODE_BOOL_LITERAL:
    fprintf(out, " value=");
    print_string_or_null(n->data.literal.value, out);
    fputc('\n', out);
    return;
  case NODE_ABI:
    fprintf(out, " abi=");
    print_string_or_null(n->data.abi.value, out);
    fputc('\n', out);
    return;
  case NODE_ASM_EXPRESSION:
    fprintf(out, " text=");
    print_string_or_null(n->data.asmExpr.text, out);
    fputc('\n', out);
    return;
  default:
    break;
  }
  fputc('\n', out);

  /* Body */
  switch (n->type) {
  case NODE_PROGRAM:
    print_indent(indent + 2, out);
    fprintf(out, "packageDecl:\n");
    ast_print_node(n->data.program.packageDecl, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "decls:\n");
    ast_print_node(n->data.program.decls, indent + 4, out);
    break;

  case NODE_DECLARATION_LIST:
    print_list(&n->data.declList, indent + 2, out);
    break;

  case NODE_CONST_DECL:
    print_indent(indent + 2, out);
    fprintf(out, "pattern:\n");
    ast_print_node(n->data.constDecl.pattern, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "type:\n");
    ast_print_node(n->data.constDecl.type, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "expr:\n");
    ast_print_node(n->data.constDecl.expr, indent + 4, out);
    break;

  case NODE_VAR_DECL:
    print_indent(indent + 2, out);
    fprintf(out, "pattern:\n");
    ast_print_node(n->data.varDecl.pattern, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "type:\n");
    ast_print_node(n->data.varDecl.type, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "expr:\n");
    ast_print_node(n->data.varDecl.expr, indent + 4, out);
    break;

  case NODE_PATH:
    print_path(n, indent, out);
    break;

  case NODE_ATTRIBUTE:
    print_indent(indent + 2, out);
    fprintf(out, "key:\n");
    ast_print_node(n->data.attribute.key, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "value:\n");
    ast_print_node(n->data.attribute.value, indent + 4, out);
    break;
  case NODE_ATTR_LIST:
    print_list(&n->data.attrList.list, indent + 2, out);
    break;
  case NODE_ATTR_APPLY:
    print_indent(indent + 2, out);
    fprintf(out, "attrs:\n");
    ast_print_node(n->data.attrApply.attrs, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "target:\n");
    ast_print_node(n->data.attrApply.target, indent + 4, out);
    break;

  case NODE_STATEMENT_LIST:
    print_list(&n->data.statementList.list, indent + 2, out);
    break;
  case NODE_BLOCK_EXPRESSION:
    print_indent(indent + 2, out);
    fprintf(out, "attr:\n");
    ast_print_node(n->data.blockExpression.attr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "statements:\n");
    ast_print_node(n->data.blockExpression.statements, indent + 4, out);
    break;

  case NODE_INSERT_STMT:
  case NODE_DEFER_STMT:
  case NODE_ERRDEFER_STMT:
    print_indent(indent + 2, out);
    fprintf(out, "expr:\n");
    ast_print_node(n->data.statement.expr, indent + 4, out);
    break;

  case NODE_LABEL:
    print_indent(indent + 2, out);
    fprintf(out, "name=");
    print_string_or_null(n->data.label.name, out);
    fputc('\n', out);
    break;

  case NODE_CONTINUE:
    print_indent(indent + 2, out);
    fprintf(out, "label:\n");
    ast_print_node(n->data.cont.label, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "expr:\n");
    ast_print_node(n->data.cont.expr, indent + 4, out);
    break;
  case NODE_BREAK:
    print_indent(indent + 2, out);
    fprintf(out, "label:\n");
    ast_print_node(n->data.brk.label, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "expr:\n");
    ast_print_node(n->data.brk.expr, indent + 4, out);
    break;
  case NODE_RETURN:
    print_indent(indent + 2, out);
    fprintf(out, "expr:\n");
    ast_print_node(n->data.ret.expr, indent + 4, out);
    break;

  case NODE_EXPRESSION_LIST:
    print_list(&n->data.exprList.list, indent + 2, out);
    break;

  case NODE_ASSIGN_EXPR:
    print_indent(indent + 2, out);
    fprintf(out, "lhs:\n");
    ast_print_node(n->data.assignExpr.lhs, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "rhs:\n");
    ast_print_node(n->data.assignExpr.rhs, indent + 4, out);
    break;

  case NODE_COMPOUND_ASSIGN_EXPR:
    print_indent(indent + 2, out);
    fprintf(out, "op=%s\n", op_name(n->data.compoundAssignExpr.op));
    print_indent(indent + 2, out);
    fprintf(out, "lhs:\n");
    ast_print_node(n->data.compoundAssignExpr.lhs, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "rhs:\n");
    ast_print_node(n->data.compoundAssignExpr.rhs, indent + 4, out);
    break;

  case NODE_BINARY_EXPR:
    print_indent(indent + 2, out);
    fprintf(out, "op=%s\n", op_name(n->data.binaryExpr.op));
    print_indent(indent + 2, out);
    fprintf(out, "lhs:\n");
    ast_print_node(n->data.binaryExpr.lhs, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "rhs:\n");
    ast_print_node(n->data.binaryExpr.rhs, indent + 4, out);
    break;

  case NODE_UNARY_EXPR:
    print_indent(indent + 2, out);
    fprintf(out, "op=%s\n", op_name(n->data.unaryExpr.op));
    print_indent(indent + 2, out);
    fprintf(out, "operand:\n");
    ast_print_node(n->data.unaryExpr.operand, indent + 4, out);
    break;

  case NODE_FIELD_ACCESS:
    print_indent(indent + 2, out);
    fprintf(out, "target:\n");
    ast_print_node(n->data.fieldAccess.target, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "field:\n");
    ast_print_node(n->data.fieldAccess.field, indent + 4, out);
    break;

  case NODE_TUPLE_INDEX:
    print_indent(indent + 2, out);
    fprintf(out, "target:\n");
    ast_print_node(n->data.tupleIndex.target, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "index:\n");
    ast_print_node(n->data.tupleIndex.index, indent + 4, out);
    break;

  case NODE_AWAIT:
  case NODE_DEREF:
  case NODE_ERROR_PROP:
    print_indent(indent + 2, out);
    fprintf(out, "target:\n");
    ast_print_node(n->data.postfix.target, indent + 4, out);
    break;

  case NODE_TYPE_CAST:
    print_indent(indent + 2, out);
    fprintf(out, "target:\n");
    ast_print_node(n->data.typeCast.target, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "type:\n");
    ast_print_node(n->data.typeCast.type, indent + 4, out);
    break;

  case NODE_CALL:
    print_indent(indent + 2, out);
    fprintf(out, "target:\n");
    ast_print_node(n->data.call.target, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "params:\n");
    ast_print_node(n->data.call.params, indent + 4, out);
    break;

  case NODE_INDEX:
    print_indent(indent + 2, out);
    fprintf(out, "target:\n");
    ast_print_node(n->data.index.target, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "indexExpr:\n");
    ast_print_node(n->data.index.indexExpr, indent + 4, out);
    break;

  case NODE_GROUPED_EXPR:
    print_indent(indent + 2, out);
    fprintf(out, "attr:\n");
    ast_print_node(n->data.groupedExpr.attr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "expr:\n");
    ast_print_node(n->data.groupedExpr.expr, indent + 4, out);
    break;

  case NODE_ARRAY_LITERAL:
    print_indent(indent + 2, out);
    fprintf(out, "attr:\n");
    ast_print_node(n->data.arrayLiteral.attr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "body:\n");
    ast_print_node(n->data.arrayLiteral.body, indent + 4, out);
    break;

  case NODE_TUPLE_LITERAL:
    print_indent(indent + 2, out);
    fprintf(out, "attr:\n");
    ast_print_node(n->data.tupleLiteral.attr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "elements:\n");
    ast_print_node(n->data.tupleLiteral.elements, indent + 4, out);
    break;

  case NODE_COLLECTION_BODY:
    print_indent(indent + 2, out);
    fprintf(out, "head:\n");
    ast_print_node(n->data.collectionBody.expression, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "tail:\n");
    ast_print_node(n->data.collectionBody.tail, indent + 4, out);
    break;

  case NODE_MAP_TAIL:
    print_indent(indent + 2, out);
    fprintf(out, "first_value:\n");
    ast_print_node(n->data.mapTail.first_value, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "rest:\n");
    ast_print_node(n->data.mapTail.rest, indent + 4, out);
    break;

  case NODE_MAP_ELEMENT:
    print_indent(indent + 2, out);
    fprintf(out, "key:\n");
    ast_print_node(n->data.mapElement.key, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "value:\n");
    ast_print_node(n->data.mapElement.value, indent + 4, out);
    break;

  case NODE_MAP_ELEMENT_LIST:
    print_list(&n->data.mapElementList.list, indent + 2, out);
    break;
  case NODE_ARRAY_REST_ELEMENT:
    print_indent(indent + 2, out);
    fprintf(out, "expr:\n");
    ast_print_node(n->data.arrayRestElement.expr, indent + 4, out);
    break;
  case NODE_ARRAY_REST_ELEMENT_LIST:
    print_list(&n->data.arrayRestElementList.list, indent + 2, out);
    break;
  case NODE_TUPLE_HEAD_ELEMENT:
    print_indent(indent + 2, out);
    fprintf(out, "expr:\n");
    ast_print_node(n->data.tupleHeadElement.expr, indent + 4, out);
    break;
  case NODE_TUPLE_HEAD_ELEMENT_LIST:
    print_list(&n->data.tupleHeadElementList.list, indent + 2, out);
    break;

  case NODE_STRUCT_FIELD:
    print_indent(indent + 2, out);
    fprintf(out, "attr:\n");
    ast_print_node(n->data.structField.attr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "key:\n");
    ast_print_node(n->data.structField.key, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "value:\n");
    ast_print_node(n->data.structField.value, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "key_is_index=%d\n", n->data.structField.key_is_index);
    break;
  case NODE_STRUCT_FIELD_LIST:
    print_list(&n->data.structFieldList.list, indent + 2, out);
    break;
  case NODE_STRUCT_BASE:
    print_indent(indent + 2, out);
    fprintf(out, "expr:\n");
    ast_print_node(n->data.structBase.expr, indent + 4, out);
    break;
  case NODE_STRUCT_EXPRESSION:
    print_indent(indent + 2, out);
    fprintf(out, "path:\n");
    ast_print_node(n->data.structExpr.path, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "attr:\n");
    ast_print_node(n->data.structExpr.attr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "fields:\n");
    ast_print_node(n->data.structExpr.fields, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "base:\n");
    ast_print_node(n->data.structExpr.base, indent + 4, out);
    break;

  case NODE_ENUM_VARIANT_FIELD:
    print_indent(indent + 2, out);
    fprintf(out, "key:\n");
    ast_print_node(n->data.enumVariantField.key, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "value:\n");
    ast_print_node(n->data.enumVariantField.value, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "key_is_index=%d\n", n->data.enumVariantField.key_is_index);
    break;
  case NODE_ENUM_VARIANT_FIELD_LIST:
    print_list(&n->data.enumVariantFieldList.list, indent + 2, out);
    break;
  case NODE_ENUM_VARIANT_EXPRESSION:
    print_indent(indent + 2, out);
    fprintf(out, "path:\n");
    ast_print_node(n->data.enumVariantExpr.path, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "fields:\n");
    ast_print_node(n->data.enumVariantExpr.fields, indent + 4, out);
    break;

  case NODE_CLOSURE_PARAM:
    print_indent(indent + 2, out);
    fprintf(out, "attr:\n");
    ast_print_node(n->data.closureParam.attr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "pattern:\n");
    ast_print_node(n->data.closureParam.pattern, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "typeAnn:\n");
    ast_print_node(n->data.closureParam.typeAnn, indent + 4, out);
    break;
  case NODE_CLOSURE_PARAMETERS:
    print_list(&n->data.closureParams.list, indent + 2, out);
    break;
  case NODE_CLOSURE_EXPRESSION:
    print_indent(indent + 2, out);
    fprintf(out, "params:\n");
    ast_print_node(n->data.closureExpr.params, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "ret_type:\n");
    ast_print_node(n->data.closureExpr.ret_type, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "body:\n");
    ast_print_node(n->data.closureExpr.body, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "body_is_block=%d\n", n->data.closureExpr.body_is_block);
    break;

  case NODE_CODE_EXPRESSION:
    print_indent(indent + 2, out);
    fprintf(out, "statements:\n");
    ast_print_node(n->data.codeExpr.statements, indent + 4, out);
    break;
  case NODE_MLIR_EXPRESSION:
    print_indent(indent + 2, out);
    fprintf(out, "head:\n");
    ast_print_node(n->data.mlirExpr.head, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "body:\n");
    ast_print_node(n->data.mlirExpr.body, indent + 4, out);
    break;
  case NODE_IMPORT_EXPRESSION:
    print_indent(indent + 2, out);
    fprintf(out, "path:\n");
    ast_print_node(n->data.importExpr.path, indent + 4, out);
    break;
  case NODE_ASYNC_EXPRESSION:
    print_indent(indent + 2, out);
    fprintf(out, "expr:\n");
    ast_print_node(n->data.asyncExpr.expr, indent + 4, out);
    break;
  case NODE_COMPTIME_EXPRESSION:
    print_indent(indent + 2, out);
    fprintf(out, "expr:\n");
    ast_print_node(n->data.comptimeExpr.expr, indent + 4, out);
    break;

  case NODE_IF_EXPRESSION:
    print_indent(indent + 2, out);
    fprintf(out, "cond:\n");
    ast_print_node(n->data.ifExpr.cond, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "then:\n");
    ast_print_node(n->data.ifExpr.thenBr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "else:\n");
    ast_print_node(n->data.ifExpr.elseBr, indent + 4, out);
    break;

  case NODE_LOOP_EXPRESSION:
    print_indent(indent + 2, out);
    fprintf(out, "kind=%d\n", n->data.loopExpr.kind);
    print_indent(indent + 2, out);
    fprintf(out, "label:\n");
    ast_print_node(n->data.loopExpr.label, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "cond:\n");
    ast_print_node(n->data.loopExpr.cond, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "pattern:\n");
    ast_print_node(n->data.loopExpr.pattern, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "iter_expr:\n");
    ast_print_node(n->data.loopExpr.iter_expr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "body:\n");
    ast_print_node(n->data.loopExpr.body, indent + 4, out);
    break;

  case NODE_MATCH_EXPRESSION:
    print_indent(indent + 2, out);
    fprintf(out, "expr:\n");
    ast_print_node(n->data.matchExpr.expr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "attr:\n");
    ast_print_node(n->data.matchExpr.attr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "arms:\n");
    ast_print_node(n->data.matchExpr.arms, indent + 4, out);
    break;
  case NODE_MATCH_ARM:
    print_indent(indent + 2, out);
    fprintf(out, "attr:\n");
    ast_print_node(n->data.matchArm.attr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "head:\n");
    ast_print_node(n->data.matchArm.head, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "rhs:\n");
    ast_print_node(n->data.matchArm.rhs, indent + 4, out);
    break;
  case NODE_MATCH_ARM_LIST:
    print_list(&n->data.matchArmList.list, indent + 2, out);
    break;
  case NODE_MATCH_GUARD:
    print_indent(indent + 2, out);
    fprintf(out, "expr:\n");
    ast_print_node(n->data.matchGuard.expr, indent + 4, out);
    break;

  case NODE_CATCH_EXPR:
    print_indent(indent + 2, out);
    fprintf(out, "expr:\n");
    ast_print_node(n->data.catchExpr.expr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "binder:\n");
    ast_print_node(n->data.catchExpr.binder, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "handler:\n");
    ast_print_node(n->data.catchExpr.handler, indent + 4, out);
    break;

  case NODE_FUNCTION_EXPRESSION:
    print_indent(indent + 2, out);
    fprintf(out, "qualifiers:\n");
    ast_print_node(n->data.funcExpr.qualifiers, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "params:\n");
    ast_print_node(n->data.funcExpr.params, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "ret_type:\n");
    ast_print_node(n->data.funcExpr.ret_type, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "body:\n");
    ast_print_node(n->data.funcExpr.body, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "body_is_asm=%d\n", n->data.funcExpr.body_is_asm);
    break;
  case NODE_PROCEDURE_EXPRESSION:
    print_indent(indent + 2, out);
    fprintf(out, "qualifiers:\n");
    ast_print_node(n->data.procExpr.qualifiers, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "params:\n");
    ast_print_node(n->data.procExpr.params, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "ret_type:\n");
    ast_print_node(n->data.procExpr.ret_type, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "body:\n");
    ast_print_node(n->data.procExpr.body, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "body_is_asm=%d\n", n->data.procExpr.body_is_asm);
    break;
  case NODE_FUNCTION_QUALIFIERS:
    print_indent(indent + 2, out);
    fprintf(out, "async:\n");
    ast_print_node(n->data.funcQuals.async_q, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "extern:\n");
    ast_print_node(n->data.funcQuals.extern_q, indent + 4, out);
    break;
  case NODE_EXTERN_QUALIFIER:
    print_indent(indent + 2, out);
    fprintf(out, "abi:\n");
    ast_print_node(n->data.externQual.abi, indent + 4, out);
    break;

  case NODE_FUNCTION_PARAMETERS:
    print_list(&n->data.funcParams.list, indent + 2, out);
    break;
  case NODE_FUNCTION_PARAM:
    print_indent(indent + 2, out);
    fprintf(out, "attr:\n");
    ast_print_node(n->data.funcParam.attr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "comptime:\n");
    ast_print_node(n->data.funcParam.comptime, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "param_type:\n");
    ast_print_node(n->data.funcParam.param_type, indent + 4, out);
    break;
  case NODE_FUNCTION_PARAM_PATTERN:
    print_indent(indent + 2, out);
    fprintf(out, "pattern:\n");
    ast_print_node(n->data.funcParamPattern.pattern, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "type:\n");
    ast_print_node(n->data.funcParamPattern.type, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "default_eq:\n");
    ast_print_node(n->data.funcParamPattern.default_eq, indent + 4, out);
    break;
  case NODE_EQ_EXPR:
    print_indent(indent + 2, out);
    fprintf(out, "expr:\n");
    ast_print_node(n->data.eqExpr.expr, indent + 4, out);
    break;
  case NODE_TYPE_ANNOTATION:
    print_indent(indent + 2, out);
    fprintf(out, "type:\n");
    ast_print_node(n->data.typeAnn.type, indent + 4, out);
    break;

  case NODE_PATTERN_LITERAL:
    print_indent(indent + 2, out);
    fprintf(out, "literal:\n");
    ast_print_node(n->data.patLiteral.literal, indent + 4, out);
    break;
  case NODE_PATTERN_IDENTIFIER:
    print_indent(indent + 2, out);
    fprintf(out, "name:\n");
    ast_print_node(n->data.patIdent.name, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "at:\n");
    ast_print_node(n->data.patIdent.at, indent + 4, out);
    break;
  case NODE_PATTERN_RANGE:
    print_indent(indent + 2, out);
    fprintf(out, "kind=%d\n", n->data.patRange.kind);
    print_indent(indent + 2, out);
    fprintf(out, "lhs:\n");
    ast_print_node(n->data.patRange.lhs, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "rhs:\n");
    ast_print_node(n->data.patRange.rhs, indent + 4, out);
    break;
  case NODE_PATTERN_STRUCT_FIELD:
    print_indent(indent + 2, out);
    fprintf(out, "attr:\n");
    ast_print_node(n->data.patStructField.attr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "key:\n");
    ast_print_node(n->data.patStructField.key, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "pat:\n");
    ast_print_node(n->data.patStructField.pat, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "key_is_index=%d\n", n->data.patStructField.key_is_index);
    break;
  case NODE_PATTERN_STRUCT_FIELD_LIST:
    print_list(&n->data.patStructFieldList.list, indent + 2, out);
    break;
  case NODE_PATTERN_STRUCT:
    print_indent(indent + 2, out);
    fprintf(out, "path:\n");
    ast_print_node(n->data.patStruct.path, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "fields:\n");
    ast_print_node(n->data.patStruct.fields, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "has_etc=%d\n", n->data.patStruct.has_etc);
    break;
  case NODE_PATTERN_TUPLE_STRUCT:
    print_indent(indent + 2, out);
    fprintf(out, "path:\n");
    ast_print_node(n->data.patTupleStruct.path, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "items:\n");
    ast_print_node(n->data.patTupleStruct.items, indent + 4, out);
    break;
  case NODE_PATTERN_TUPLE:
    print_indent(indent + 2, out);
    fprintf(out, "items:\n");
    ast_print_node(n->data.patTuple.items, indent + 4, out);
    break;
  case NODE_PATTERN_GROUPED:
    print_indent(indent + 2, out);
    fprintf(out, "pat:\n");
    ast_print_node(n->data.patGrouped.pat, indent + 4, out);
    break;
  case NODE_PATTERN_SLICE:
    print_indent(indent + 2, out);
    fprintf(out, "items:\n");
    ast_print_node(n->data.patSlice.items, indent + 4, out);
    break;
  case NODE_PATTERN_PATH:
    print_indent(indent + 2, out);
    fprintf(out, "path:\n");
    ast_print_node(n->data.patPath.path, indent + 4, out);
    break;

  case NODE_TYPE_PAREN:
    print_indent(indent + 2, out);
    fprintf(out, "inner:\n");
    ast_print_node(n->data.tParen.inner, indent + 4, out);
    break;
  case NODE_TYPE_PATH:
    print_indent(indent + 2, out);
    fprintf(out, "path:\n");
    ast_print_node(n->data.tPath.path, indent + 4, out);
    break;
  case NODE_TYPE_TUPLE:
    print_list(&n->data.tTuple.list, indent + 2, out);
    break;
  case NODE_TYPE_RAW_POINTER:
    print_indent(indent + 2, out);
    fprintf(out, "is_const=%d\n", n->data.tRawPtr.is_const);
    print_indent(indent + 2, out);
    fprintf(out, "pointee:\n");
    ast_print_node(n->data.tRawPtr.pointee, indent + 4, out);
    break;
  case NODE_TYPE_ARRAY:
    print_indent(indent + 2, out);
    fprintf(out, "len:\n");
    ast_print_node(n->data.tArray.len_expr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "elem:\n");
    ast_print_node(n->data.tArray.elem, indent + 4, out);
    break;
  case NODE_TYPE_DYNAMIC_ARRAY:
    print_indent(indent + 2, out);
    fprintf(out, "elem:\n");
    ast_print_node(n->data.tDynArray.elem, indent + 4, out);
    break;
  case NODE_TYPE_SLICE:
    print_indent(indent + 2, out);
    fprintf(out, "elem:\n");
    ast_print_node(n->data.tSlice.elem, indent + 4, out);
    break;
  case NODE_TYPE_MAP:
    print_indent(indent + 2, out);
    fprintf(out, "key:\n");
    ast_print_node(n->data.tMap.key, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "value:\n");
    ast_print_node(n->data.tMap.value, indent + 4, out);
    break;
  case NODE_TYPE_OPTIONAL:
    print_indent(indent + 2, out);
    fprintf(out, "base:\n");
    ast_print_node(n->data.tOpt.base, indent + 4, out);
    break;
  case NODE_TYPE_ERROR:
    print_indent(indent + 2, out);
    fprintf(out, "variants:\n");
    ast_print_node(n->data.tError.variants, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "decls:\n");
    ast_print_node(n->data.tError.decls, indent + 4, out);
    break;
  case NODE_TYPE_SIMD:
    print_indent(indent + 2, out);
    fprintf(out, "lanes:\n");
    ast_print_node(n->data.tSimd.lanes, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "elem:\n");
    ast_print_node(n->data.tSimd.elem, indent + 4, out);
    break;
  case NODE_TYPE_COMPLEX:
    print_indent(indent + 2, out);
    fprintf(out, "elem:\n");
    ast_print_node(n->data.tComplex.elem, indent + 4, out);
    break;
  case NODE_TYPE_TENSOR:
    print_indent(indent + 2, out);
    fprintf(out, "dims (%zu):\n", n->data.tTensor.dims.count);
    print_list(&n->data.tTensor.dims, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "elem:\n");
    ast_print_node(n->data.tTensor.elem, indent + 4, out);
    break;
  case NODE_TYPE_STRUCT_FIELD:
    print_indent(indent + 2, out);
    fprintf(out, "attr:\n");
    ast_print_node(n->data.tStructField.attr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "is_pub=%d\n", n->data.tStructField.is_pub);
    print_indent(indent + 2, out);
    fprintf(out, "name:\n");
    ast_print_node(n->data.tStructField.name, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "type:\n");
    ast_print_node(n->data.tStructField.type, indent + 4, out);
    break;
  case NODE_TYPE_STRUCT_FIELD_LIST:
    print_list(&n->data.tStructFieldList.list, indent + 2, out);
    break;
  case NODE_TYPE_STRUCT:
    print_indent(indent + 2, out);
    fprintf(out, "fields:\n");
    ast_print_node(n->data.tStruct.fields, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "decls:\n");
    ast_print_node(n->data.tStruct.decls, indent + 4, out);
    break;
  case NODE_TYPE_ENUM_ITEM:
    print_indent(indent + 2, out);
    fprintf(out, "attr:\n");
    ast_print_node(n->data.tEnumItem.attr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "is_pub=%d\n", n->data.tEnumItem.is_pub);
    print_indent(indent + 2, out);
    fprintf(out, "name:\n");
    ast_print_node(n->data.tEnumItem.name, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "discriminant:\n");
    ast_print_node(n->data.tEnumItem.discriminant, indent + 4, out);
    break;
  case NODE_TYPE_ENUM_ITEM_LIST:
    print_list(&n->data.tEnumItemList.list, indent + 2, out);
    break;
  case NODE_TYPE_ENUM:
    print_indent(indent + 2, out);
    fprintf(out, "underlying:\n");
    ast_print_node(n->data.tEnum.underlying, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "items:\n");
    ast_print_node(n->data.tEnum.items, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "decls:\n");
    ast_print_node(n->data.tEnum.decls, indent + 4, out);
    break;
  case NODE_TYPE_VARIANT_ITEM:
    print_indent(indent + 2, out);
    fprintf(out, "attr:\n");
    ast_print_node(n->data.tVarItem.attr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "is_pub=%d\n", n->data.tVarItem.is_pub);
    print_indent(indent + 2, out);
    fprintf(out, "name:\n");
    ast_print_node(n->data.tVarItem.name, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "body:\n");
    ast_print_node(n->data.tVarItem.body, indent + 4, out);
    break;
  case NODE_TYPE_VARIANT_ITEM_LIST:
    print_list(&n->data.tVarItemList.list, indent + 2, out);
    break;
  case NODE_TYPE_VARIANT:
    print_indent(indent + 2, out);
    fprintf(out, "items:\n");
    ast_print_node(n->data.tVariant.items, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "decls:\n");
    ast_print_node(n->data.tVariant.decls, indent + 4, out);
    break;
  case NODE_TYPE_UNION:
    print_indent(indent + 2, out);
    fprintf(out, "fields:\n");
    ast_print_node(n->data.tUnion.fields, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "decls:\n");
    ast_print_node(n->data.tUnion.decls, indent + 4, out);
    break;

  case NODE_TYPE_MAYBE_NAMED_PARAM:
    print_indent(indent + 2, out);
    fprintf(out, "attr:\n");
    ast_print_node(n->data.tMaybeNamedParam.attr, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "name:\n");
    ast_print_node(n->data.tMaybeNamedParam.name, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "is_underscore=%d\n", n->data.tMaybeNamedParam.is_underscore);
    print_indent(indent + 2, out);
    fprintf(out, "type:\n");
    ast_print_node(n->data.tMaybeNamedParam.type, indent + 4, out);
    break;
  case NODE_TYPE_MAYBE_NAMED_PARAM_LIST:
    print_list(&n->data.tMaybeNamedParamList.list, indent + 2, out);
    break;
  case NODE_TYPE_BARE_FUNCTION:
    print_indent(indent + 2, out);
    fprintf(out, "extern_q:\n");
    ast_print_node(n->data.tBareFn.extern_q, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "params:\n");
    ast_print_node(n->data.tBareFn.params, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "ret_type:\n");
    ast_print_node(n->data.tBareFn.ret_type, indent + 4, out);
    break;

  case NODE_PATTERN_STRUCT_ELEMS:
    print_indent(indent + 2, out);
    fprintf(out, "fields:\n");
    ast_print_node(n->data.patStructElems.fields, indent + 4, out);
    print_indent(indent + 2, out);
    fprintf(out, "has_etc=%d\n", n->data.patStructElems.has_etc);
    break;

  default:
    /* Nodes like NULL/UNDEFINED/etc have no children */
    break;
  }
}

void ast_print(const AstNode *root, FILE *out) { ast_print_node(root, 0, out); }

/* Optional: minimal CLI for testing if built standalone.
 * Compile with: gcc -DAST_PRINTER_MAIN -o ast_printer ast_printer.c ast.c
 * (You still need a way to build an AST; this is mostly for unit tests.)
 */
#ifdef AST_PRINTER_MAIN
int main(void) {
  fprintf(stdout,
          "ast_printer compiled. Link and call ast_print(root, stdout).\n");
  return 0;
}
#endif
