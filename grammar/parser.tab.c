/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison implementation for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2021 Free Software Foundation,
   Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output, and Bison version.  */
#define YYBISON 30802

/* Bison version string.  */
#define YYBISON_VERSION "3.8.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1




/* First part of user prologue.  */
#line 1 "parser.y"

  #include <stdio.h>
  #include <stdlib.h>
  #include <string.h>
  #include "ast.h"

  #define ZL ((SourceLocation){0,0,0,0})

  void yyerror(const char* s);
  int yylex(void);

  AstNode *ast_root = NULL;

#line 85 "parser.tab.c"

# ifndef YY_CAST
#  ifdef __cplusplus
#   define YY_CAST(Type, Val) static_cast<Type> (Val)
#   define YY_REINTERPRET_CAST(Type, Val) reinterpret_cast<Type> (Val)
#  else
#   define YY_CAST(Type, Val) ((Type) (Val))
#   define YY_REINTERPRET_CAST(Type, Val) ((Type) (Val))
#  endif
# endif
# ifndef YY_NULLPTR
#  if defined __cplusplus
#   if 201103L <= __cplusplus
#    define YY_NULLPTR nullptr
#   else
#    define YY_NULLPTR 0
#   endif
#  else
#   define YY_NULLPTR ((void*)0)
#  endif
# endif

#include "parser.tab.h"
/* Symbol kind.  */
enum yysymbol_kind_t
{
  YYSYMBOL_YYEMPTY = -2,
  YYSYMBOL_YYEOF = 0,                      /* "end of file"  */
  YYSYMBOL_YYerror = 1,                    /* error  */
  YYSYMBOL_YYUNDEF = 2,                    /* "invalid token"  */
  YYSYMBOL_ALIGN = 3,                      /* ALIGN  */
  YYSYMBOL_AND = 4,                        /* AND  */
  YYSYMBOL_ANY = 5,                        /* ANY  */
  YYSYMBOL_AS = 6,                         /* AS  */
  YYSYMBOL_ASM = 7,                        /* ASM  */
  YYSYMBOL_ASYNC = 8,                      /* ASYNC  */
  YYSYMBOL_AWAIT = 9,                      /* AWAIT  */
  YYSYMBOL_BREAK = 10,                     /* BREAK  */
  YYSYMBOL_CATCH = 11,                     /* CATCH  */
  YYSYMBOL_COMPTIME = 12,                  /* COMPTIME  */
  YYSYMBOL_CODE = 13,                      /* CODE  */
  YYSYMBOL_COMPLEX = 14,                   /* COMPLEX  */
  YYSYMBOL_CONST = 15,                     /* CONST  */
  YYSYMBOL_CONTINUE = 16,                  /* CONTINUE  */
  YYSYMBOL_DYN = 17,                       /* DYN  */
  YYSYMBOL_DEFER = 18,                     /* DEFER  */
  YYSYMBOL_ELSE = 19,                      /* ELSE  */
  YYSYMBOL_ENUM = 20,                      /* ENUM  */
  YYSYMBOL_ERRDEFER = 21,                  /* ERRDEFER  */
  YYSYMBOL_ERROR = 22,                     /* ERROR  */
  YYSYMBOL_EXPORT = 23,                    /* EXPORT  */
  YYSYMBOL_EXTERN = 24,                    /* EXTERN  */
  YYSYMBOL_FALSE = 25,                     /* FALSE  */
  YYSYMBOL_FN = 26,                        /* FN  */
  YYSYMBOL_FOR = 27,                       /* FOR  */
  YYSYMBOL_IF = 28,                        /* IF  */
  YYSYMBOL_IN = 29,                        /* IN  */
  YYSYMBOL_IS = 30,                        /* IS  */
  YYSYMBOL_INSERT = 31,                    /* INSERT  */
  YYSYMBOL_IMPORT = 32,                    /* IMPORT  */
  YYSYMBOL_MATCH = 33,                     /* MATCH  */
  YYSYMBOL_MLIR = 34,                      /* MLIR  */
  YYSYMBOL_NORETURN = 35,                  /* NORETURN  */
  YYSYMBOL_NULL_KW = 36,                   /* NULL_KW  */
  YYSYMBOL_OPAQUE = 37,                    /* OPAQUE  */
  YYSYMBOL_OR = 38,                        /* OR  */
  YYSYMBOL_ORELSE = 39,                    /* ORELSE  */
  YYSYMBOL_PACKAGE = 40,                   /* PACKAGE  */
  YYSYMBOL_PROC = 41,                      /* PROC  */
  YYSYMBOL_PUB = 42,                       /* PUB  */
  YYSYMBOL_RETURN = 43,                    /* RETURN  */
  YYSYMBOL_LINKSECTION = 44,               /* LINKSECTION  */
  YYSYMBOL_SIMD = 45,                      /* SIMD  */
  YYSYMBOL_STRUCT = 46,                    /* STRUCT  */
  YYSYMBOL_THREADLOCAL = 47,               /* THREADLOCAL  */
  YYSYMBOL_TENSOR = 48,                    /* TENSOR  */
  YYSYMBOL_TEST = 49,                      /* TEST  */
  YYSYMBOL_TRUE = 50,                      /* TRUE  */
  YYSYMBOL_TYPE = 51,                      /* TYPE  */
  YYSYMBOL_TYPEOF = 52,                    /* TYPEOF  */
  YYSYMBOL_UNION = 53,                     /* UNION  */
  YYSYMBOL_UNDEFINED = 54,                 /* UNDEFINED  */
  YYSYMBOL_UNREACHABLE = 55,               /* UNREACHABLE  */
  YYSYMBOL_VARIANT = 56,                   /* VARIANT  */
  YYSYMBOL_WHILE = 57,                     /* WHILE  */
  YYSYMBOL_PLUS = 58,                      /* PLUS  */
  YYSYMBOL_MINUS = 59,                     /* MINUS  */
  YYSYMBOL_STAR = 60,                      /* STAR  */
  YYSYMBOL_SLASH = 61,                     /* SLASH  */
  YYSYMBOL_PERCENT = 62,                   /* PERCENT  */
  YYSYMBOL_CARET = 63,                     /* CARET  */
  YYSYMBOL_BANG = 64,                      /* BANG  */
  YYSYMBOL_B_AND = 65,                     /* B_AND  */
  YYSYMBOL_B_OR = 66,                      /* B_OR  */
  YYSYMBOL_SHL = 67,                       /* SHL  */
  YYSYMBOL_SHR = 68,                       /* SHR  */
  YYSYMBOL_PLUSEQ = 69,                    /* PLUSEQ  */
  YYSYMBOL_MINUSEQ = 70,                   /* MINUSEQ  */
  YYSYMBOL_RARROW = 71,                    /* RARROW  */
  YYSYMBOL_STAREQ = 72,                    /* STAREQ  */
  YYSYMBOL_SLASHEQ = 73,                   /* SLASHEQ  */
  YYSYMBOL_PERCENTEQ = 74,                 /* PERCENTEQ  */
  YYSYMBOL_CARETEQ = 75,                   /* CARETEQ  */
  YYSYMBOL_ANDEQ = 76,                     /* ANDEQ  */
  YYSYMBOL_OREQ = 77,                      /* OREQ  */
  YYSYMBOL_SHLEQ = 78,                     /* SHLEQ  */
  YYSYMBOL_SHREQ = 79,                     /* SHREQ  */
  YYSYMBOL_SHLPIPE = 80,                   /* SHLPIPE  */
  YYSYMBOL_SHLPIPEEQ = 81,                 /* SHLPIPEEQ  */
  YYSYMBOL_PLUSPIPE = 82,                  /* PLUSPIPE  */
  YYSYMBOL_PLUSPIPEEQ = 83,                /* PLUSPIPEEQ  */
  YYSYMBOL_MINUSPIPE = 84,                 /* MINUSPIPE  */
  YYSYMBOL_MINUSPIPEEQ = 85,               /* MINUSPIPEEQ  */
  YYSYMBOL_STARPIPE = 86,                  /* STARPIPE  */
  YYSYMBOL_STARPIPEEQ = 87,                /* STARPIPEEQ  */
  YYSYMBOL_PIPEPIPE = 88,                  /* PIPEPIPE  */
  YYSYMBOL_PLUSPERCENT = 89,               /* PLUSPERCENT  */
  YYSYMBOL_PLUSPERCENTEQ = 90,             /* PLUSPERCENTEQ  */
  YYSYMBOL_MINUSPERCENT = 91,              /* MINUSPERCENT  */
  YYSYMBOL_MINUSPERCENTEQ = 92,            /* MINUSPERCENTEQ  */
  YYSYMBOL_STARPERCENT = 93,               /* STARPERCENT  */
  YYSYMBOL_STARPERCENTEQ = 94,             /* STARPERCENTEQ  */
  YYSYMBOL_EQ = 95,                        /* EQ  */
  YYSYMBOL_EQEQ = 96,                      /* EQEQ  */
  YYSYMBOL_NE = 97,                        /* NE  */
  YYSYMBOL_GT = 98,                        /* GT  */
  YYSYMBOL_LT = 99,                        /* LT  */
  YYSYMBOL_GE = 100,                       /* GE  */
  YYSYMBOL_LE = 101,                       /* LE  */
  YYSYMBOL_AT = 102,                       /* AT  */
  YYSYMBOL_UNDERSCORE = 103,               /* UNDERSCORE  */
  YYSYMBOL_DOT = 104,                      /* DOT  */
  YYSYMBOL_DOTDOT = 105,                   /* DOTDOT  */
  YYSYMBOL_DOTSTAR = 106,                  /* DOTSTAR  */
  YYSYMBOL_DOTDOTDOT = 107,                /* DOTDOTDOT  */
  YYSYMBOL_DOTDOTEQ = 108,                 /* DOTDOTEQ  */
  YYSYMBOL_DOTLPAREN = 109,                /* DOTLPAREN  */
  YYSYMBOL_DOTLSQUAREBRACKET = 110,        /* DOTLSQUAREBRACKET  */
  YYSYMBOL_DOTLCURLYBRACE = 111,           /* DOTLCURLYBRACE  */
  YYSYMBOL_COMMA = 112,                    /* COMMA  */
  YYSYMBOL_SEMI = 113,                     /* SEMI  */
  YYSYMBOL_COLON = 114,                    /* COLON  */
  YYSYMBOL_COLONCOLON = 115,               /* COLONCOLON  */
  YYSYMBOL_COLONEQ = 116,                  /* COLONEQ  */
  YYSYMBOL_FATARROW = 117,                 /* FATARROW  */
  YYSYMBOL_QUESTION = 118,                 /* QUESTION  */
  YYSYMBOL_LCURLYBRACE = 119,              /* LCURLYBRACE  */
  YYSYMBOL_RCURLYBRACE = 120,              /* RCURLYBRACE  */
  YYSYMBOL_LSQUAREBRACKET = 121,           /* LSQUAREBRACKET  */
  YYSYMBOL_RSQUAREBRACKET = 122,           /* RSQUAREBRACKET  */
  YYSYMBOL_LPAREN = 123,                   /* LPAREN  */
  YYSYMBOL_RPAREN = 124,                   /* RPAREN  */
  YYSYMBOL_POUND = 125,                    /* POUND  */
  YYSYMBOL_EOS = 126,                      /* EOS  */
  YYSYMBOL_RAW_ASM_BLOCK = 127,            /* RAW_ASM_BLOCK  */
  YYSYMBOL_NON_KEYWORD_IDENTIFIER = 128,   /* NON_KEYWORD_IDENTIFIER  */
  YYSYMBOL_RAW_IDENTIFIER = 129,           /* RAW_IDENTIFIER  */
  YYSYMBOL_CHAR_LITERAL = 130,             /* CHAR_LITERAL  */
  YYSYMBOL_STRING_LITERAL = 131,           /* STRING_LITERAL  */
  YYSYMBOL_RAW_STRING_LITERAL = 132,       /* RAW_STRING_LITERAL  */
  YYSYMBOL_BYTE_LITERAL = 133,             /* BYTE_LITERAL  */
  YYSYMBOL_BYTE_STRING_LITERAL = 134,      /* BYTE_STRING_LITERAL  */
  YYSYMBOL_RAW_BYTE_STRING_LITERAL = 135,  /* RAW_BYTE_STRING_LITERAL  */
  YYSYMBOL_INTEGER_LITERAL = 136,          /* INTEGER_LITERAL  */
  YYSYMBOL_FLOAT_LITERAL = 137,            /* FLOAT_LITERAL  */
  YYSYMBOL_IMAGINARY_LITERAL = 138,        /* IMAGINARY_LITERAL  */
  YYSYMBOL_UREF = 139,                     /* UREF  */
  YYSYMBOL_UMINUS_UBANG = 140,             /* UMINUS_UBANG  */
  YYSYMBOL_YYACCEPT = 141,                 /* $accept  */
  YYSYMBOL_program = 142,                  /* program  */
  YYSYMBOL_packageDecl_opt = 143,          /* packageDecl_opt  */
  YYSYMBOL_packageDecl = 144,              /* packageDecl  */
  YYSYMBOL_declarations_opt = 145,         /* declarations_opt  */
  YYSYMBOL_declaration = 146,              /* declaration  */
  YYSYMBOL_identifier = 147,               /* identifier  */
  YYSYMBOL_constDecl = 148,                /* constDecl  */
  YYSYMBOL_varDecl = 149,                  /* varDecl  */
  YYSYMBOL_type_opt = 150,                 /* type_opt  */
  YYSYMBOL_statement = 151,                /* statement  */
  YYSYMBOL_expressionStatement = 152,      /* expressionStatement  */
  YYSYMBOL_EOS_opt = 153,                  /* EOS_opt  */
  YYSYMBOL_insertStatement = 154,          /* insertStatement  */
  YYSYMBOL_deferStatement = 155,           /* deferStatement  */
  YYSYMBOL_errdeferStatement = 156,        /* errdeferStatement  */
  YYSYMBOL_attribute = 157,                /* attribute  */
  YYSYMBOL_attrs_opt = 158,                /* attrs_opt  */
  YYSYMBOL_attr = 159,                     /* attr  */
  YYSYMBOL_expression = 160,               /* expression  */
  YYSYMBOL_assign_expr = 161,              /* assign_expr  */
  YYSYMBOL_compoundAssignOperator = 162,   /* compoundAssignOperator  */
  YYSYMBOL_catch_expr = 163,               /* catch_expr  */
  YYSYMBOL_catchBinder_opt = 164,          /* catchBinder_opt  */
  YYSYMBOL_orelse_expr = 165,              /* orelse_expr  */
  YYSYMBOL_range_expr = 166,               /* range_expr  */
  YYSYMBOL_or_expr = 167,                  /* or_expr  */
  YYSYMBOL_and_expr = 168,                 /* and_expr  */
  YYSYMBOL_comparisonOperator = 169,       /* comparisonOperator  */
  YYSYMBOL_cmp_expr = 170,                 /* cmp_expr  */
  YYSYMBOL_bitor_expr = 171,               /* bitor_expr  */
  YYSYMBOL_xor_expr = 172,                 /* xor_expr  */
  YYSYMBOL_bitand_expr = 173,              /* bitand_expr  */
  YYSYMBOL_shift_expr = 174,               /* shift_expr  */
  YYSYMBOL_add_expr = 175,                 /* add_expr  */
  YYSYMBOL_mul_expr = 176,                 /* mul_expr  */
  YYSYMBOL_unary_expr = 177,               /* unary_expr  */
  YYSYMBOL_postfix_expr = 178,             /* postfix_expr  */
  YYSYMBOL_primary_expr = 179,             /* primary_expr  */
  YYSYMBOL_attribute_opt = 180,            /* attribute_opt  */
  YYSYMBOL_collectionBody_opt = 181,       /* collectionBody_opt  */
  YYSYMBOL_tupleElements_opt = 182,        /* tupleElements_opt  */
  YYSYMBOL_expression_opt = 183,           /* expression_opt  */
  YYSYMBOL_label_opt = 184,                /* label_opt  */
  YYSYMBOL_callParams_opt = 185,           /* callParams_opt  */
  YYSYMBOL_attr_block_expr = 186,          /* attr_block_expr  */
  YYSYMBOL_attribute_opt_list = 187,       /* attribute_opt_list  */
  YYSYMBOL_blocklike_expr = 188,           /* blocklike_expr  */
  YYSYMBOL_label = 189,                    /* label  */
  YYSYMBOL_nullExpression = 190,           /* nullExpression  */
  YYSYMBOL_undefinedExpression = 191,      /* undefinedExpression  */
  YYSYMBOL_functionExpression = 192,       /* functionExpression  */
  YYSYMBOL_procedureExpression = 193,      /* procedureExpression  */
  YYSYMBOL_functionQualifiers = 194,       /* functionQualifiers  */
  YYSYMBOL_ASYNC_opt = 195,                /* ASYNC_opt  */
  YYSYMBOL_extern_opt = 196,               /* extern_opt  */
  YYSYMBOL_abi_opt = 197,                  /* abi_opt  */
  YYSYMBOL_functionParameters_opt = 198,   /* functionParameters_opt  */
  YYSYMBOL_functionParameters = 199,       /* functionParameters  */
  YYSYMBOL_functionParam_list = 200,       /* functionParam_list  */
  YYSYMBOL_functionParam = 201,            /* functionParam  */
  YYSYMBOL_COMPTIME_opt = 202,             /* COMPTIME_opt  */
  YYSYMBOL_functionParamPattern = 203,     /* functionParamPattern  */
  YYSYMBOL_eqExpr_opt = 204,               /* eqExpr_opt  */
  YYSYMBOL_literalExpression = 205,        /* literalExpression  */
  YYSYMBOL_blockExpression = 206,          /* blockExpression  */
  YYSYMBOL_statements_opt = 207,           /* statements_opt  */
  YYSYMBOL_statements = 208,               /* statements  */
  YYSYMBOL_statement_plus = 209,           /* statement_plus  */
  YYSYMBOL_collectionBody = 210,           /* collectionBody  */
  YYSYMBOL_collectionTail_opt = 211,       /* collectionTail_opt  */
  YYSYMBOL_restOfMap = 212,                /* restOfMap  */
  YYSYMBOL_mapElement_seq_opt = 213,       /* mapElement_seq_opt  */
  YYSYMBOL_mapElement_seq = 214,           /* mapElement_seq  */
  YYSYMBOL_mapElement = 215,               /* mapElement  */
  YYSYMBOL_restOfArray = 216,              /* restOfArray  */
  YYSYMBOL_restArr_seq = 217,              /* restArr_seq  */
  YYSYMBOL_tupleElements = 218,            /* tupleElements  */
  YYSYMBOL_tuple_head = 219,               /* tuple_head  */
  YYSYMBOL_tupleIndex = 220,               /* tupleIndex  */
  YYSYMBOL_structExpression = 221,         /* structExpression  */
  YYSYMBOL_structExprStruct = 222,         /* structExprStruct  */
  YYSYMBOL_structStructTail_opt = 223,     /* structStructTail_opt  */
  YYSYMBOL_structExprFields = 224,         /* structExprFields  */
  YYSYMBOL_structExprFieldsTail_opt = 225, /* structExprFieldsTail_opt  */
  YYSYMBOL_structExprField_list = 226,     /* structExprField_list  */
  YYSYMBOL_structExprField = 227,          /* structExprField  */
  YYSYMBOL_structBase = 228,               /* structBase  */
  YYSYMBOL_enumerationVariantExpression = 229, /* enumerationVariantExpression  */
  YYSYMBOL_enumExprStruct = 230,           /* enumExprStruct  */
  YYSYMBOL_enumExprField_list = 231,       /* enumExprField_list  */
  YYSYMBOL_enumExprField = 232,            /* enumExprField  */
  YYSYMBOL_callParams = 233,               /* callParams  */
  YYSYMBOL_closureExpression = 234,        /* closureExpression  */
  YYSYMBOL_closureParameters_opt = 235,    /* closureParameters_opt  */
  YYSYMBOL_closureParameters = 236,        /* closureParameters  */
  YYSYMBOL_closureParam_list = 237,        /* closureParam_list  */
  YYSYMBOL_closureParam = 238,             /* closureParam  */
  YYSYMBOL_typeAnn_opt = 239,              /* typeAnn_opt  */
  YYSYMBOL_loopExpression = 240,           /* loopExpression  */
  YYSYMBOL_loopLabel_opt = 241,            /* loopLabel_opt  */
  YYSYMBOL_loopBody = 242,                 /* loopBody  */
  YYSYMBOL_infiniteLoopExpression = 243,   /* infiniteLoopExpression  */
  YYSYMBOL_predicateLoopExpression = 244,  /* predicateLoopExpression  */
  YYSYMBOL_predicatePatternLoopExpression = 245, /* predicatePatternLoopExpression  */
  YYSYMBOL_iteratorLoopExpression = 246,   /* iteratorLoopExpression  */
  YYSYMBOL_loopLabel = 247,                /* loopLabel  */
  YYSYMBOL_codeExpression = 248,           /* codeExpression  */
  YYSYMBOL_mlirExpression = 249,           /* mlirExpression  */
  YYSYMBOL_mlirHead_opt = 250,             /* mlirHead_opt  */
  YYSYMBOL_mlirBody_opt = 251,             /* mlirBody_opt  */
  YYSYMBOL_asmExpression = 252,            /* asmExpression  */
  YYSYMBOL_importExpression = 253,         /* importExpression  */
  YYSYMBOL_ifExpression = 254,             /* ifExpression  */
  YYSYMBOL_elseTail_opt = 255,             /* elseTail_opt  */
  YYSYMBOL_matchExpression = 256,          /* matchExpression  */
  YYSYMBOL_matchArms_opt = 257,            /* matchArms_opt  */
  YYSYMBOL_matchArms = 258,                /* matchArms  */
  YYSYMBOL_matchRHS = 259,                 /* matchRHS  */
  YYSYMBOL_matchArm = 260,                 /* matchArm  */
  YYSYMBOL_matchArmGuard_opt = 261,        /* matchArmGuard_opt  */
  YYSYMBOL_pattern = 262,                  /* pattern  */
  YYSYMBOL_patternAltTail_opt = 263,       /* patternAltTail_opt  */
  YYSYMBOL_patternNoTopAlt = 264,          /* patternNoTopAlt  */
  YYSYMBOL_patternWithoutRange = 265,      /* patternWithoutRange  */
  YYSYMBOL_literalPattern = 266,           /* literalPattern  */
  YYSYMBOL_MINUS_opt = 267,                /* MINUS_opt  */
  YYSYMBOL_identifierPattern = 268,        /* identifierPattern  */
  YYSYMBOL_atTail_opt = 269,               /* atTail_opt  */
  YYSYMBOL_wildcardPattern = 270,          /* wildcardPattern  */
  YYSYMBOL_restPattern = 271,              /* restPattern  */
  YYSYMBOL_rangePattern = 272,             /* rangePattern  */
  YYSYMBOL_rangePatternBound = 273,        /* rangePatternBound  */
  YYSYMBOL_structPattern = 274,            /* structPattern  */
  YYSYMBOL_structPatternElements_opt = 275, /* structPatternElements_opt  */
  YYSYMBOL_structPatternElements = 276,    /* structPatternElements  */
  YYSYMBOL_structPatEtcTail_opt = 277,     /* structPatEtcTail_opt  */
  YYSYMBOL_structPatternEtCetera_opt = 278, /* structPatternEtCetera_opt  */
  YYSYMBOL_structPatternFields = 279,      /* structPatternFields  */
  YYSYMBOL_structPatternField_list = 280,  /* structPatternField_list  */
  YYSYMBOL_structPatternField = 281,       /* structPatternField  */
  YYSYMBOL_structPatternEtCetera = 282,    /* structPatternEtCetera  */
  YYSYMBOL_tupleStructPattern = 283,       /* tupleStructPattern  */
  YYSYMBOL_tupleStructItems_opt = 284,     /* tupleStructItems_opt  */
  YYSYMBOL_tupleStructItems = 285,         /* tupleStructItems  */
  YYSYMBOL_tuplePattern = 286,             /* tuplePattern  */
  YYSYMBOL_tuplePatternItems_opt = 287,    /* tuplePatternItems_opt  */
  YYSYMBOL_tuplePatList = 288,             /* tuplePatList  */
  YYSYMBOL_tuplePatternItems = 289,        /* tuplePatternItems  */
  YYSYMBOL_groupedPattern = 290,           /* groupedPattern  */
  YYSYMBOL_patternNoTopAlt_noRest = 291,   /* patternNoTopAlt_noRest  */
  YYSYMBOL_patternWithoutRange_noRest = 292, /* patternWithoutRange_noRest  */
  YYSYMBOL_slicePattern = 293,             /* slicePattern  */
  YYSYMBOL_slicePatternItems_opt = 294,    /* slicePatternItems_opt  */
  YYSYMBOL_slicePatternItems = 295,        /* slicePatternItems  */
  YYSYMBOL_pathPattern = 296,              /* pathPattern  */
  YYSYMBOL_type_ = 297,                    /* type_  */
  YYSYMBOL_typeAtom = 298,                 /* typeAtom  */
  YYSYMBOL_type_exprable = 299,            /* type_exprable  */
  YYSYMBOL_typeLiteralExpr = 300,          /* typeLiteralExpr  */
  YYSYMBOL_parenthesizedType = 301,        /* parenthesizedType  */
  YYSYMBOL_noreturnType = 302,             /* noreturnType  */
  YYSYMBOL_tupleType = 303,                /* tupleType  */
  YYSYMBOL_tupleTypeTail_opt = 304,        /* tupleTypeTail_opt  */
  YYSYMBOL_arrayType = 305,                /* arrayType  */
  YYSYMBOL_dynamicArrayType = 306,         /* dynamicArrayType  */
  YYSYMBOL_sliceType = 307,                /* sliceType  */
  YYSYMBOL_mapType = 308,                  /* mapType  */
  YYSYMBOL_optionalType = 309,             /* optionalType  */
  YYSYMBOL_errorType = 310,                /* errorType  */
  YYSYMBOL_structType = 311,               /* structType  */
  YYSYMBOL_structTypeTail_opt = 312,       /* structTypeTail_opt  */
  YYSYMBOL_structFields_opt = 313,         /* structFields_opt  */
  YYSYMBOL_structFields = 314,             /* structFields  */
  YYSYMBOL_structField_list = 315,         /* structField_list  */
  YYSYMBOL_structField = 316,              /* structField  */
  YYSYMBOL_PUB_opt = 317,                  /* PUB_opt  */
  YYSYMBOL_enumType = 318,                 /* enumType  */
  YYSYMBOL_parenthesizedType_opt = 319,    /* parenthesizedType_opt  */
  YYSYMBOL_enumItems_opt = 320,            /* enumItems_opt  */
  YYSYMBOL_enumItems = 321,                /* enumItems  */
  YYSYMBOL_enumItem_list = 322,            /* enumItem_list  */
  YYSYMBOL_enumItem = 323,                 /* enumItem  */
  YYSYMBOL_enumItemTail_opt = 324,         /* enumItemTail_opt  */
  YYSYMBOL_variantType = 325,              /* variantType  */
  YYSYMBOL_variantItems_opt = 326,         /* variantItems_opt  */
  YYSYMBOL_variantItems = 327,             /* variantItems  */
  YYSYMBOL_variantItem_list = 328,         /* variantItem_list  */
  YYSYMBOL_variantItem = 329,              /* variantItem  */
  YYSYMBOL_variantBody_opt = 330,          /* variantBody_opt  */
  YYSYMBOL_enumItemTuple = 331,            /* enumItemTuple  */
  YYSYMBOL_enumItemStruct = 332,           /* enumItemStruct  */
  YYSYMBOL_enumItemDiscriminant = 333,     /* enumItemDiscriminant  */
  YYSYMBOL_tupleFields_opt = 334,          /* tupleFields_opt  */
  YYSYMBOL_tupleFields = 335,              /* tupleFields  */
  YYSYMBOL_tupleField_list = 336,          /* tupleField_list  */
  YYSYMBOL_tupleField = 337,               /* tupleField  */
  YYSYMBOL_unionType = 338,                /* unionType  */
  YYSYMBOL_simdType = 339,                 /* simdType  */
  YYSYMBOL_complexType = 340,              /* complexType  */
  YYSYMBOL_tensorType = 341,               /* tensorType  */
  YYSYMBOL_tensorDims = 342,               /* tensorDims  */
  YYSYMBOL_rawPointerType = 343,           /* rawPointerType  */
  YYSYMBOL_CONST_opt = 344,                /* CONST_opt  */
  YYSYMBOL_bareFunctionType = 345,         /* bareFunctionType  */
  YYSYMBOL_functionTypeQualifiers = 346,   /* functionTypeQualifiers  */
  YYSYMBOL_abi = 347,                      /* abi  */
  YYSYMBOL_functionParametersMaybeNamedVariadic_opt = 348, /* functionParametersMaybeNamedVariadic_opt  */
  YYSYMBOL_functionParametersMaybeNamedVariadic = 349, /* functionParametersMaybeNamedVariadic  */
  YYSYMBOL_maybeNamedFunctionParameters = 350, /* maybeNamedFunctionParameters  */
  YYSYMBOL_maybeNamedParam_list = 351,     /* maybeNamedParam_list  */
  YYSYMBOL_maybeNamedParam = 352,          /* maybeNamedParam  */
  YYSYMBOL_maybeName_opt = 353,            /* maybeName_opt  */
  YYSYMBOL_maybeNamedFunctionParametersVariadic = 354, /* maybeNamedFunctionParametersVariadic  */
  YYSYMBOL_inferredType = 355,             /* inferredType  */
  YYSYMBOL_path = 356,                     /* path  */
  YYSYMBOL_path_ndot = 357,                /* path_ndot  */
  YYSYMBOL_expression_list = 358,          /* expression_list  */
  YYSYMBOL_pattern_list = 359,             /* pattern_list  */
  YYSYMBOL_type_list = 360,                /* type_list  */
  YYSYMBOL_COMMA_opt = 361                 /* COMMA_opt  */
};
typedef enum yysymbol_kind_t yysymbol_kind_t;




#ifdef short
# undef short
#endif

/* On compilers that do not define __PTRDIFF_MAX__ etc., make sure
   <limits.h> and (if available) <stdint.h> are included
   so that the code can choose integer types of a good width.  */

#ifndef __PTRDIFF_MAX__
# include <limits.h> /* INFRINGES ON USER NAME SPACE */
# if defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stdint.h> /* INFRINGES ON USER NAME SPACE */
#  define YY_STDINT_H
# endif
#endif

/* Narrow types that promote to a signed type and that can represent a
   signed or unsigned integer of at least N bits.  In tables they can
   save space and decrease cache pressure.  Promoting to a signed type
   helps avoid bugs in integer arithmetic.  */

#ifdef __INT_LEAST8_MAX__
typedef __INT_LEAST8_TYPE__ yytype_int8;
#elif defined YY_STDINT_H
typedef int_least8_t yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef __INT_LEAST16_MAX__
typedef __INT_LEAST16_TYPE__ yytype_int16;
#elif defined YY_STDINT_H
typedef int_least16_t yytype_int16;
#else
typedef short yytype_int16;
#endif

/* Work around bug in HP-UX 11.23, which defines these macros
   incorrectly for preprocessor constants.  This workaround can likely
   be removed in 2023, as HPE has promised support for HP-UX 11.23
   (aka HP-UX 11i v2) only through the end of 2022; see Table 2 of
   <https://h20195.www2.hpe.com/V2/getpdf.aspx/4AA4-7673ENW.pdf>.  */
#ifdef __hpux
# undef UINT_LEAST8_MAX
# undef UINT_LEAST16_MAX
# define UINT_LEAST8_MAX 255
# define UINT_LEAST16_MAX 65535
#endif

#if defined __UINT_LEAST8_MAX__ && __UINT_LEAST8_MAX__ <= __INT_MAX__
typedef __UINT_LEAST8_TYPE__ yytype_uint8;
#elif (!defined __UINT_LEAST8_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST8_MAX <= INT_MAX)
typedef uint_least8_t yytype_uint8;
#elif !defined __UINT_LEAST8_MAX__ && UCHAR_MAX <= INT_MAX
typedef unsigned char yytype_uint8;
#else
typedef short yytype_uint8;
#endif

#if defined __UINT_LEAST16_MAX__ && __UINT_LEAST16_MAX__ <= __INT_MAX__
typedef __UINT_LEAST16_TYPE__ yytype_uint16;
#elif (!defined __UINT_LEAST16_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST16_MAX <= INT_MAX)
typedef uint_least16_t yytype_uint16;
#elif !defined __UINT_LEAST16_MAX__ && USHRT_MAX <= INT_MAX
typedef unsigned short yytype_uint16;
#else
typedef int yytype_uint16;
#endif

#ifndef YYPTRDIFF_T
# if defined __PTRDIFF_TYPE__ && defined __PTRDIFF_MAX__
#  define YYPTRDIFF_T __PTRDIFF_TYPE__
#  define YYPTRDIFF_MAXIMUM __PTRDIFF_MAX__
# elif defined PTRDIFF_MAX
#  ifndef ptrdiff_t
#   include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  endif
#  define YYPTRDIFF_T ptrdiff_t
#  define YYPTRDIFF_MAXIMUM PTRDIFF_MAX
# else
#  define YYPTRDIFF_T long
#  define YYPTRDIFF_MAXIMUM LONG_MAX
# endif
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned
# endif
#endif

#define YYSIZE_MAXIMUM                                  \
  YY_CAST (YYPTRDIFF_T,                                 \
           (YYPTRDIFF_MAXIMUM < YY_CAST (YYSIZE_T, -1)  \
            ? YYPTRDIFF_MAXIMUM                         \
            : YY_CAST (YYSIZE_T, -1)))

#define YYSIZEOF(X) YY_CAST (YYPTRDIFF_T, sizeof (X))


/* Stored state numbers (used for stacks). */
typedef yytype_int16 yy_state_t;

/* State numbers in computations.  */
typedef int yy_state_fast_t;

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif


#ifndef YY_ATTRIBUTE_PURE
# if defined __GNUC__ && 2 < __GNUC__ + (96 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_PURE __attribute__ ((__pure__))
# else
#  define YY_ATTRIBUTE_PURE
# endif
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# if defined __GNUC__ && 2 < __GNUC__ + (7 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_UNUSED __attribute__ ((__unused__))
# else
#  define YY_ATTRIBUTE_UNUSED
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YY_USE(E) ((void) (E))
#else
# define YY_USE(E) /* empty */
#endif

/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
#if defined __GNUC__ && ! defined __ICC && 406 <= __GNUC__ * 100 + __GNUC_MINOR__
# if __GNUC__ * 100 + __GNUC_MINOR__ < 407
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")
# else
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")              \
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# endif
# define YY_IGNORE_MAYBE_UNINITIALIZED_END      \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif

#if defined __cplusplus && defined __GNUC__ && ! defined __ICC && 6 <= __GNUC__
# define YY_IGNORE_USELESS_CAST_BEGIN                          \
    _Pragma ("GCC diagnostic push")                            \
    _Pragma ("GCC diagnostic ignored \"-Wuseless-cast\"")
# define YY_IGNORE_USELESS_CAST_END            \
    _Pragma ("GCC diagnostic pop")
#endif
#ifndef YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_END
#endif


#define YY_ASSERT(E) ((void) (0 && (E)))

#if 1

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* 1 */

#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL \
             && defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yy_state_t yyss_alloc;
  YYSTYPE yyvs_alloc;
  YYLTYPE yyls_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (YYSIZEOF (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (YYSIZEOF (yy_state_t) + YYSIZEOF (YYSTYPE) \
             + YYSIZEOF (YYLTYPE)) \
      + 2 * YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYPTRDIFF_T yynewbytes;                                         \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * YYSIZEOF (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / YYSIZEOF (*yyptr);                        \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, YY_CAST (YYSIZE_T, (Count)) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYPTRDIFF_T yyi;                      \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  8
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   11441

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  141
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  221
/* YYNRULES -- Number of rules.  */
#define YYNRULES  515
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  1011

/* YYMAXUTOK -- Last valid token kind.  */
#define YYMAXUTOK   395


/* YYTRANSLATE(TOKEN-NUM) -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, with out-of-bounds checking.  */
#define YYTRANSLATE(YYX)                                \
  (0 <= (YYX) && (YYX) <= YYMAXUTOK                     \
   ? YY_CAST (yysymbol_kind_t, yytranslate[YYX])        \
   : YYSYMBOL_YYUNDEF)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      75,    76,    77,    78,    79,    80,    81,    82,    83,    84,
      85,    86,    87,    88,    89,    90,    91,    92,    93,    94,
      95,    96,    97,    98,    99,   100,   101,   102,   103,   104,
     105,   106,   107,   108,   109,   110,   111,   112,   113,   114,
     115,   116,   117,   118,   119,   120,   121,   122,   123,   124,
     125,   126,   127,   128,   129,   130,   131,   132,   133,   134,
     135,   136,   137,   138,   139,   140
};

#if YYDEBUG
/* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_int16 yyrline[] =
{
       0,   137,   137,   142,   143,   147,   152,   153,   157,   158,
     162,   163,   167,   169,   174,   176,   181,   182,   190,   191,
     192,   193,   194,   195,   199,   200,   204,   205,   209,   213,
     217,   222,   227,   228,   232,   233,   241,   245,   246,   247,
     248,   249,   250,   254,   255,   256,   257,   258,   259,   260,
     261,   262,   263,   264,   265,   266,   267,   268,   269,   270,
     274,   275,   279,   280,   284,   285,   289,   290,   291,   292,
     296,   297,   301,   302,   306,   307,   308,   309,   310,   311,
     315,   316,   320,   321,   325,   326,   330,   331,   335,   336,
     337,   338,   342,   343,   344,   345,   346,   347,   348,   352,
     353,   354,   355,   356,   357,   361,   362,   363,   364,   368,
     369,   370,   371,   372,   373,   374,   375,   376,   377,   379,
     381,   382,   387,   388,   389,   390,   392,   394,   395,   396,
     397,   398,   399,   400,   401,   402,   403,   404,   405,   409,
     410,   414,   415,   419,   420,   424,   425,   429,   430,   434,
     435,   440,   445,   446,   450,   451,   452,   453,   454,   455,
     456,   457,   458,   462,   466,   470,   478,   480,   486,   488,
     494,   498,   499,   503,   504,   508,   509,   513,   514,   518,
     522,   523,   527,   529,   531,   536,   537,   541,   543,   548,
     549,   557,   558,   559,   560,   561,   562,   563,   564,   565,
     566,   567,   571,   576,   577,   581,   582,   586,   587,   595,
     600,   601,   602,   606,   611,   612,   616,   617,   621,   629,
     630,   635,   636,   640,   649,   651,   656,   664,   668,   677,
     678,   679,   683,   688,   689,   690,   694,   695,   699,   701,
     703,   708,   712,   721,   723,   728,   729,   733,   734,   735,
     739,   747,   749,   751,   753,   758,   759,   763,   767,   768,
     772,   777,   778,   786,   791,   792,   796,   797,   798,   799,
     803,   808,   813,   818,   823,   838,   844,   849,   850,   851,
     855,   859,   863,   871,   876,   877,   878,   882,   887,   888,
     892,   894,   899,   903,   908,   909,   917,   922,   923,   927,
     928,   932,   933,   934,   935,   936,   937,   938,   939,   940,
     941,   945,   946,   947,   948,   949,   950,   951,   952,   953,
     955,   957,   962,   963,   967,   972,   973,   977,   981,   985,
     987,   989,   991,   996,   997,   998,  1000,  1002,  1007,  1025,
    1026,  1030,  1032,  1037,  1038,  1042,  1043,  1047,  1051,  1052,
    1056,  1058,  1060,  1065,  1069,  1074,  1075,  1079,  1083,  1088,
    1089,  1099,  1101,  1106,  1108,  1114,  1118,  1119,  1123,  1124,
    1125,  1126,  1127,  1128,  1129,  1130,  1131,  1135,  1140,  1141,
    1145,  1149,  1156,  1157,  1172,  1173,  1174,  1175,  1176,  1177,
    1178,  1179,  1180,  1181,  1182,  1183,  1184,  1185,  1186,  1187,
    1188,  1189,  1190,  1191,  1192,  1196,  1197,  1198,  1199,  1200,
    1201,  1202,  1203,  1204,  1205,  1206,  1207,  1208,  1209,  1210,
    1211,  1212,  1213,  1217,  1221,  1225,  1229,  1234,  1235,  1249,
    1254,  1259,  1264,  1269,  1273,  1278,  1283,  1284,  1289,  1290,
    1294,  1298,  1299,  1303,  1308,  1309,  1313,  1318,  1319,  1323,
    1324,  1328,  1332,  1333,  1337,  1342,  1343,  1347,  1352,  1353,
    1357,  1361,  1362,  1366,  1371,  1372,  1373,  1374,  1378,  1383,
    1388,  1392,  1393,  1397,  1401,  1402,  1406,  1411,  1416,  1421,
    1426,  1431,  1436,  1438,  1443,  1448,  1449,  1453,  1458,  1462,
    1463,  1467,  1468,  1472,  1473,  1477,  1481,  1482,  1486,  1491,
    1492,  1493,  1497,  1504,  1512,  1513,  1517,  1518,  1526,  1527,
    1531,  1532,  1536,  1537,  1541,  1542
};
#endif

/** Accessing symbol of state STATE.  */
#define YY_ACCESSING_SYMBOL(State) YY_CAST (yysymbol_kind_t, yystos[State])

#if 1
/* The user-facing name of the symbol whose (internal) number is
   YYSYMBOL.  No bounds checking.  */
static const char *yysymbol_name (yysymbol_kind_t yysymbol) YY_ATTRIBUTE_UNUSED;

/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "\"end of file\"", "error", "\"invalid token\"", "ALIGN", "AND", "ANY",
  "AS", "ASM", "ASYNC", "AWAIT", "BREAK", "CATCH", "COMPTIME", "CODE",
  "COMPLEX", "CONST", "CONTINUE", "DYN", "DEFER", "ELSE", "ENUM",
  "ERRDEFER", "ERROR", "EXPORT", "EXTERN", "FALSE", "FN", "FOR", "IF",
  "IN", "IS", "INSERT", "IMPORT", "MATCH", "MLIR", "NORETURN", "NULL_KW",
  "OPAQUE", "OR", "ORELSE", "PACKAGE", "PROC", "PUB", "RETURN",
  "LINKSECTION", "SIMD", "STRUCT", "THREADLOCAL", "TENSOR", "TEST", "TRUE",
  "TYPE", "TYPEOF", "UNION", "UNDEFINED", "UNREACHABLE", "VARIANT",
  "WHILE", "PLUS", "MINUS", "STAR", "SLASH", "PERCENT", "CARET", "BANG",
  "B_AND", "B_OR", "SHL", "SHR", "PLUSEQ", "MINUSEQ", "RARROW", "STAREQ",
  "SLASHEQ", "PERCENTEQ", "CARETEQ", "ANDEQ", "OREQ", "SHLEQ", "SHREQ",
  "SHLPIPE", "SHLPIPEEQ", "PLUSPIPE", "PLUSPIPEEQ", "MINUSPIPE",
  "MINUSPIPEEQ", "STARPIPE", "STARPIPEEQ", "PIPEPIPE", "PLUSPERCENT",
  "PLUSPERCENTEQ", "MINUSPERCENT", "MINUSPERCENTEQ", "STARPERCENT",
  "STARPERCENTEQ", "EQ", "EQEQ", "NE", "GT", "LT", "GE", "LE", "AT",
  "UNDERSCORE", "DOT", "DOTDOT", "DOTSTAR", "DOTDOTDOT", "DOTDOTEQ",
  "DOTLPAREN", "DOTLSQUAREBRACKET", "DOTLCURLYBRACE", "COMMA", "SEMI",
  "COLON", "COLONCOLON", "COLONEQ", "FATARROW", "QUESTION", "LCURLYBRACE",
  "RCURLYBRACE", "LSQUAREBRACKET", "RSQUAREBRACKET", "LPAREN", "RPAREN",
  "POUND", "EOS", "RAW_ASM_BLOCK", "NON_KEYWORD_IDENTIFIER",
  "RAW_IDENTIFIER", "CHAR_LITERAL", "STRING_LITERAL", "RAW_STRING_LITERAL",
  "BYTE_LITERAL", "BYTE_STRING_LITERAL", "RAW_BYTE_STRING_LITERAL",
  "INTEGER_LITERAL", "FLOAT_LITERAL", "IMAGINARY_LITERAL", "UREF",
  "UMINUS_UBANG", "$accept", "program", "packageDecl_opt", "packageDecl",
  "declarations_opt", "declaration", "identifier", "constDecl", "varDecl",
  "type_opt", "statement", "expressionStatement", "EOS_opt",
  "insertStatement", "deferStatement", "errdeferStatement", "attribute",
  "attrs_opt", "attr", "expression", "assign_expr",
  "compoundAssignOperator", "catch_expr", "catchBinder_opt", "orelse_expr",
  "range_expr", "or_expr", "and_expr", "comparisonOperator", "cmp_expr",
  "bitor_expr", "xor_expr", "bitand_expr", "shift_expr", "add_expr",
  "mul_expr", "unary_expr", "postfix_expr", "primary_expr",
  "attribute_opt", "collectionBody_opt", "tupleElements_opt",
  "expression_opt", "label_opt", "callParams_opt", "attr_block_expr",
  "attribute_opt_list", "blocklike_expr", "label", "nullExpression",
  "undefinedExpression", "functionExpression", "procedureExpression",
  "functionQualifiers", "ASYNC_opt", "extern_opt", "abi_opt",
  "functionParameters_opt", "functionParameters", "functionParam_list",
  "functionParam", "COMPTIME_opt", "functionParamPattern", "eqExpr_opt",
  "literalExpression", "blockExpression", "statements_opt", "statements",
  "statement_plus", "collectionBody", "collectionTail_opt", "restOfMap",
  "mapElement_seq_opt", "mapElement_seq", "mapElement", "restOfArray",
  "restArr_seq", "tupleElements", "tuple_head", "tupleIndex",
  "structExpression", "structExprStruct", "structStructTail_opt",
  "structExprFields", "structExprFieldsTail_opt", "structExprField_list",
  "structExprField", "structBase", "enumerationVariantExpression",
  "enumExprStruct", "enumExprField_list", "enumExprField", "callParams",
  "closureExpression", "closureParameters_opt", "closureParameters",
  "closureParam_list", "closureParam", "typeAnn_opt", "loopExpression",
  "loopLabel_opt", "loopBody", "infiniteLoopExpression",
  "predicateLoopExpression", "predicatePatternLoopExpression",
  "iteratorLoopExpression", "loopLabel", "codeExpression",
  "mlirExpression", "mlirHead_opt", "mlirBody_opt", "asmExpression",
  "importExpression", "ifExpression", "elseTail_opt", "matchExpression",
  "matchArms_opt", "matchArms", "matchRHS", "matchArm",
  "matchArmGuard_opt", "pattern", "patternAltTail_opt", "patternNoTopAlt",
  "patternWithoutRange", "literalPattern", "MINUS_opt",
  "identifierPattern", "atTail_opt", "wildcardPattern", "restPattern",
  "rangePattern", "rangePatternBound", "structPattern",
  "structPatternElements_opt", "structPatternElements",
  "structPatEtcTail_opt", "structPatternEtCetera_opt",
  "structPatternFields", "structPatternField_list", "structPatternField",
  "structPatternEtCetera", "tupleStructPattern", "tupleStructItems_opt",
  "tupleStructItems", "tuplePattern", "tuplePatternItems_opt",
  "tuplePatList", "tuplePatternItems", "groupedPattern",
  "patternNoTopAlt_noRest", "patternWithoutRange_noRest", "slicePattern",
  "slicePatternItems_opt", "slicePatternItems", "pathPattern", "type_",
  "typeAtom", "type_exprable", "typeLiteralExpr", "parenthesizedType",
  "noreturnType", "tupleType", "tupleTypeTail_opt", "arrayType",
  "dynamicArrayType", "sliceType", "mapType", "optionalType", "errorType",
  "structType", "structTypeTail_opt", "structFields_opt", "structFields",
  "structField_list", "structField", "PUB_opt", "enumType",
  "parenthesizedType_opt", "enumItems_opt", "enumItems", "enumItem_list",
  "enumItem", "enumItemTail_opt", "variantType", "variantItems_opt",
  "variantItems", "variantItem_list", "variantItem", "variantBody_opt",
  "enumItemTuple", "enumItemStruct", "enumItemDiscriminant",
  "tupleFields_opt", "tupleFields", "tupleField_list", "tupleField",
  "unionType", "simdType", "complexType", "tensorType", "tensorDims",
  "rawPointerType", "CONST_opt", "bareFunctionType",
  "functionTypeQualifiers", "abi",
  "functionParametersMaybeNamedVariadic_opt",
  "functionParametersMaybeNamedVariadic", "maybeNamedFunctionParameters",
  "maybeNamedParam_list", "maybeNamedParam", "maybeName_opt",
  "maybeNamedFunctionParametersVariadic", "inferredType", "path",
  "path_ndot", "expression_list", "pattern_list", "type_list", "COMMA_opt", YY_NULLPTR
};

static const char *
yysymbol_name (yysymbol_kind_t yysymbol)
{
  return yytname[yysymbol];
}
#endif

#define YYPACT_NINF (-844)

#define yypact_value_is_default(Yyn) \
  ((Yyn) == YYPACT_NINF)

#define YYTABLE_NINF (-516)

#define yytable_value_is_error(Yyn) \
  0

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
static const yytype_int16 yypact[] =
{
      18,   391,    51,  -844,  -844,  -844,  -844,   -22,  -844,    80,
    -844,  -844,  -844,  -844,  -844,    36,  1330,  1758,   369,  -844,
    -844,   423,  -844,  -844,  -844,  -844,    44,  -844,  -844,   537,
    -844,  -844,   421,  -844,  -844,  -844,  -844,   436,  -844,  -844,
    -844,  -844,  -844,   448,   -63,     5,  -844,  -844,    31,   500,
    -844,  -844,  -844,  -844,    -4,  -844,    48,  -844,   108,   117,
     161,   193,   199,   203,   223,   230,   328,    90,  -844,   343,
     351,  -844,   382,   348,  6436,   391,  -844,  3136,  9728,  9728,
     503,   515,    36,    91,   391,    56,  2749,   391,  -844,  -844,
     297,  -844,   781,  -844,  -844,  3915,  -844,  -844,  -844,  -844,
     142,   287,   342,   524,  -844,   372,   405,   403,  -844,   411,
     416,   499,  4308,  7852,  3971,  -844,   144,  -844,  -844,   475,
    -844,  -844,  -844,  -844,  -844,  -844,  -844,  -844,  -844,  -844,
    -844,  -844,  -844,  -844,  -844,  -844,  -844,  -844,   526,  -844,
     455,   454,   453,   454,  -844,   391,    -7,  -844,  7048,  -844,
    -844,  -844,  -844, 10800, 10800, 10800,   -41,  9862,  7048,   482,
     482,   482,  -844,  -844,  -844,  -844,  -844,  -844,  -844,  -844,
    -844,  -844,   310,   451,  -844,   583,   559,  -844,     9,   596,
     624,   538,   550,   580,   470,   396,   345,   867,   127,  -844,
    -844,    98,  -844,  -844,  -844,  -844,  -844,  -844,  -844,  -844,
    -844,  -844,  -844,  -844,  -844,  -844,  -844,  -844,  -844,  -844,
    -844,  -844,  -844,  -844,  -844,  -844,  -844,  -844,  -844,  -844,
    -844,  -844,  -844,   141,   533,  -844,  -844,  -844,   539,  -844,
     286,   546,  -844,   556,   557,  -844,  -844,   547,  -844,    48,
    -844,  6436,  -844,  -844,  4308,  4308,  -844,   561,   -31,  -844,
    -844,  -844,  -844,  9728,   -31,  -844,   540,   -31,   -31,  -844,
    4308,  -844,   573,   -30,  4308,  3527,   578,   569,    64,   132,
     170,   183,   185,   190,   192,   197,   211,   212,   214,   236,
     237,   239,   245,   248,   252,   141,   359,   577,  9728,  9728,
    4308,   579,   581,  7048,  -844,  7450,  7048,   455,  -844,  -844,
     592,  -844,  -844,  -844,  -844,  -844,  6436,   648,  -844,   603,
    -844,  -844,   611,  -844,  8254,  8388,  9728,  -844,   666,  2090,
   10800,  7048, 10800, 10800,  -844,  -844,  -844,  -844,  -844,  -844,
   10800, 10800, 10800, 10800, 10800, 10800, 10800, 10800, 10800, 10800,
   10800, 10800, 10800, 10800, 10800, 10800, 10800, 10800,  -844,  -844,
    -844,  -844,  -844,  -844,  -844,  -844,  -844,  -844,  -844,  -844,
    -844,  -844,  -844,  -844,  -844,  9728,  9728,  -844,    53,  -844,
    4308,  9728,  8522,   611,  8656,  9996,  9996,   482,   619,  -844,
    -844,  -844,  -844,   354,   712,  -844,  -844,    11,  -844,  -844,
    -844,   272,  -844,  -844,  -844,  -844,   623,   625,  -844,    72,
    -844,   482,  -844,  -844,  -844,   618,   622,   -31,   710,  -844,
    -844,   642,  -844,   647,   710,  -844,  -844,   649,  -844,  -844,
     653,  -844,  -844,  -844,  4308,  -844,  4308,  4308,  4308,  -844,
    -844,   640,   651,  -844,    27,  -844,  -844,  9728,  9728,   519,
    9728,   532, 10800,  7182,  7718,  1244,  -844,   549,   633,   655,
     660,   674,   686,   714,  -844,   474,  -844,  -844,  -844,  -844,
    -844,   652, 11315,   663,  -844,  7584,   293,  -844,  -844,   659,
    9862,    -3,  -844,  -844,   673,   667,  -844,  8790,   334,   670,
    -844,   672,   391,  2090,  -844,  -844,   596,  -844,   766,   624,
     538,   550,   580,   470,   396,   396,   396,   345,   345,   345,
     345,   345,   345,  -844,  -844,  -844,  -844,  -844,  -844,  -844,
    -844,  4308,  4308,  4308,  4308,  -844,  -844,   681,   687,  -844,
     684,  -844,   698,  -844,  -844,  -844,   611,   699,  7450,  -844,
     694,   696,  -844,  6436,  7986,  -844,  -844,  -844,  -844,  -844,
    -844,   709,   255,   711,   720,  -844,   -74,  6436,  6436,   719,
    -844,  -844,   445,  -844,  -844,   710,  -844,  -844,   721,  -844,
    -844,   391,  4325,   -31,  -844,  4308,   391,  4903,   -31,  -844,
    3288,  5128,  5218,  -844,  -844,   713,  -844,   724,  -844,  -844,
     152,   728,  -844,  -844,   733,  -844,  -844,   725,   729,   730,
     727,   732,   314,  4735,   293,  -844,  -844,  -844,  -844,  -844,
     652,  -844,   272,   734,  4308,  -844,  -844,   611,  -844,  -844,
    -844,   747,  -844,  9728, 10130,  9728,  -844,  -844,  -844,   748,
    -844,  -844,   795,   559,  -844,  -844,  -844,  -844,  -844,  -844,
    -844,  8924,  -844,   843,   482,   743,   114,   114,   835,  6436,
     611,  -844,  9728,  9728,   445,   746,  -844,   755,  -844,  -844,
    9728,   445,   752,  -844,   773,  -844,  -844,  -844,   391,  5612,
     -31,  -844,   290,  -844,  -844,   749,   760,  -844,  -844,  -844,
     751,  -844,  -844,  -844,  4137,  -844,   762,   763,  4308,  3136,
     200,  -844,  -844,  -844,  -844, 11115,   -63,   253,  -844,  -844,
    -844,  -844,  -844,  9058,  -844,  9192,  -844,  -844,  -844,     8,
    -844,   274,  -844,   868,   757,  -844,   770,  -844,   761,  9996,
     771,  -844,  -844,  -844,   775,   777,  -844,   395,  -844,  -844,
    -844,  -844,  -844,   136,   797,  -844,  -844,  9728,   300,   254,
    -844,  -844,  -844,  -844,  -844,  4308,  -844,  -844,  -844,  -844,
    -844,  -844,   414,  -844,  9326,   779,  -844,   782,  -844,  -844,
    -844,  -844,  6436,   776,  -844,   780,  -844, 11237,  3136,   200,
    -844,  3136,   611,  9996,  9728,  9728,  -844,  -844,  -844,  -844,
    -844,  -844,   778,   710,   784,  -844,   788,  -844,  -844,  -844,
    9728,  9192,  -844,   878,  -844,  9728,  -844,  -844,   803,  -844,
     292,  -844,   367,  -844,   611,  -844,  -844,  -844,  4308,  -844,
     200,  -844,  -844,  -844,  9728,  -844,  -844,   809,  4479,  -844,
    -844,  -844,  -844,  -844,  -844,  -844,  -844,   301,   828,   828,
    -844,  9728,  -844,  -844,  -844,   360,   -54,   805,   -19,   -12,
      24,    60,    74,    76,    78,    85,   104,   106,   111,   123,
     143,   158,   163,   164,   171,   454,   454,  7316, 10934, 10934,
   10934,   -41, 10264,  7316,  -844,   914,   887,    15,   923,   624,
     863,   870,   865,   487,   407,   443,  1232,   371,   513,   454,
     454, 10130, 11068,   499, 11068, 11068,   -41, 10398, 10130,  4678,
    8120,   920,   895,    29,   931,   624,   872,   884,   888,   495,
     434,   447,  1424,   187,   929,   282,  9460,  7316,  7316,   883,
     666, 10532, 10934,  7316, 10934, 10934, 10934, 10934, 10934, 10934,
   10934, 10934, 10934, 10934, 10934, 10934, 10934, 10934, 10934, 10934,
   10934, 10934, 10934, 10934,  9996,  9996,  9594, 10130, 10130,  4678,
     890,   894,   842,  4678,   844,   666, 10666, 11068, 10130, 11068,
   11068, 11068, 11068, 11068, 11068, 11068, 11068, 11068, 11068, 11068,
   11068, 11068, 11068, 11068, 11068, 11068, 11068, 11068, 11068, 10130,
   10130,    70,   845, 10264, 10532,   923,   927,   624,   863,   870,
     865,   487,   407,   407,   407,   443,   443,   443,   443,   443,
     443, 10398,  4678,  4678,  4678, 10666,   931,   932,   624,   872,
     884,   888,   495,   434,   434,   434,   447,   447,   447,   447,
     447,   447,  4678,  4678,  4678,  4678,    27,   887,   895,   847,
    4678
};

/* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
   Performed when YYTABLE does not specify something else to do.  Zero
   means the default is an error.  */
static const yytype_int16 yydefact[] =
{
       3,     0,     0,     6,     4,    10,    11,     0,     1,   322,
       5,   312,   311,   323,   327,   328,   322,   322,   313,   315,
     316,   314,   317,   318,   321,     7,   325,     8,     9,     0,
     299,   301,     0,   302,   303,   304,   300,     0,   305,   306,
     307,   308,   309,   310,     0,   381,   333,   334,     0,     0,
     332,   337,   510,   297,     0,   379,   514,   361,   301,   302,
     303,   304,   300,   305,   306,   307,     0,     0,   360,   308,
       0,   366,   309,   310,   322,     0,   324,    16,   152,   152,
     319,   320,   331,   322,     0,   139,   322,     0,   335,   336,
     296,   377,   322,   380,   358,   322,   365,   326,   506,   503,
       0,   447,     0,   175,   425,     0,   436,     0,   404,     0,
       0,   485,   173,   152,   173,   504,     0,   488,    17,   382,
     384,   387,   386,   389,   390,   391,   392,   393,   394,   399,
     400,   401,   402,   395,   396,   397,   388,   403,     0,   398,
     385,   147,     0,   147,   201,     0,   277,   164,   145,   200,
     422,   165,   138,   152,   152,   152,   139,   152,   145,   139,
     139,   139,   281,   191,   192,   193,   194,   195,   196,   197,
     198,   199,   123,     0,    36,    37,    60,    64,    66,    70,
      72,    80,    82,    84,    86,    88,    92,    99,   105,   109,
     137,   171,   133,   134,   122,   127,   227,   128,   242,   129,
     130,   131,   132,   136,   423,   135,   405,   407,   408,   409,
     410,   411,   412,   417,   418,   419,   420,   413,   414,   415,
     406,   421,   416,     0,     0,   330,   329,   505,     0,   140,
       0,     0,   340,   343,   347,   348,   342,     0,   356,   514,
     507,   322,   511,   362,   173,   173,   448,     0,   458,   489,
     490,   174,   176,   152,   438,   435,     0,   438,   458,   486,
     173,   433,     0,   422,   173,   139,     0,     0,   405,   407,
     408,   409,   410,   411,   412,   417,   418,   419,   420,   413,
     414,   415,   406,   421,   416,   385,     0,     0,   152,   152,
     173,     0,     0,   145,   148,   152,   145,   282,   278,   279,
       0,   146,    42,   107,   108,   106,   322,     0,   256,   514,
     258,   251,     0,    68,   152,   152,   152,    13,    62,   152,
     152,   145,   152,   152,    74,    75,    76,    77,    78,    79,
     152,   152,   152,   152,   152,   152,   152,   152,   152,   152,
     152,   152,   152,   152,   152,   152,   152,   152,    43,    44,
      45,    46,    47,    50,    48,    49,    51,    52,    56,    53,
      54,    55,    57,    58,    59,   152,   152,   121,     0,   120,
     173,   152,   152,   172,   152,   152,   152,   139,     0,   153,
     151,   159,   160,     0,   173,   154,   156,     0,   265,   157,
     158,   139,    15,    32,   353,   226,   352,     0,   338,   139,
     341,   139,   354,   357,   298,     0,     0,   449,   444,     6,
     459,   514,   461,     0,   444,     6,   439,   514,   441,   481,
       0,     6,     6,   484,   173,   431,   173,   173,   173,   424,
     426,     0,     0,   383,   139,   163,    41,   152,   152,   201,
     152,   200,   152,   152,   152,   139,    18,   191,   192,   193,
     194,   195,   196,   199,    19,   123,   207,    23,    20,    21,
      22,   206,    26,     0,   204,   152,     0,    40,   280,   261,
     152,   139,   257,   252,     0,     0,   144,   152,   210,     0,
     142,     0,     0,   152,    65,    99,    71,    67,    69,    73,
      81,    83,    85,    87,    89,    90,    91,    93,    94,    95,
      96,    97,    98,   100,   101,   102,   103,   104,    38,    39,
     112,   173,   173,   173,   173,   110,   111,     0,     0,   508,
       0,   150,   514,   155,   162,   161,     0,     0,   152,   274,
       0,     0,   170,   322,   152,   263,   266,   267,   268,   269,
     244,   247,   139,     0,   514,   245,     0,   322,   322,     0,
     344,   346,     0,   349,   479,   444,     6,   450,   514,   452,
     445,     0,   322,   515,   460,   173,     0,   322,   515,   440,
     173,   322,   322,   430,   429,     0,   512,   514,    14,    12,
     499,     0,   492,   493,   514,   496,   494,     0,     0,     0,
     191,   194,   123,   139,   385,    24,    27,    25,   275,   208,
     146,   205,   139,     0,   173,   260,   253,     0,   259,   224,
     126,   146,   223,   152,   152,   152,   209,   211,   212,   514,
     125,   124,     0,    61,   116,   114,   115,   117,   113,   119,
     118,   152,   250,   284,   139,     0,   139,   139,     0,   322,
       0,   270,   152,   152,     0,     0,   230,   233,   236,   231,
     152,   515,     0,    31,    35,    33,   351,   350,     0,   322,
     515,   451,   464,   434,   462,     0,     0,   437,   442,   482,
       0,   477,   457,   432,   173,   428,     0,     0,   173,    16,
     139,   495,    29,    30,    28,   322,   385,   229,   276,   262,
     254,   225,   221,   152,   220,   152,   219,    63,   509,     0,
     283,   139,   202,   185,     0,   178,   514,   180,     0,   152,
       0,   271,   248,   241,   238,     0,   228,   139,   232,   235,
     249,   246,   243,     0,   455,   446,   453,   152,   139,   139,
     463,   466,   465,   467,   478,   173,   480,   513,   501,   500,
     498,   487,   499,   497,   152,     0,   213,   514,   216,   222,
     285,   286,   322,     0,   289,     0,   186,   322,    16,   139,
     179,    16,     0,   152,   152,   152,   237,   234,    34,   454,
     456,   470,     0,   444,     0,   472,   514,   474,   443,   502,
     152,   152,   215,   294,   287,   152,   183,   182,     0,   184,
       0,   181,     0,   273,     0,   239,   240,   469,   173,   468,
     139,   473,   218,   217,   152,   293,   292,     0,   173,   167,
     166,   169,   168,   272,   476,   475,   295,   139,   189,   189,
     290,   152,   188,   187,   190,   171,   422,   123,   405,   407,
     408,   409,   410,   411,   412,   417,   418,   419,   420,   413,
     414,   415,   406,   421,   416,   147,   147,   145,   152,   152,
     152,   139,   152,   145,   123,    37,    60,    66,    70,    72,
      80,    82,    84,    86,    88,    92,    99,   171,   123,   147,
     147,   145,   152,   485,   152,   152,   139,   152,   145,   173,
     152,    37,    60,    66,    70,    72,    80,    82,    84,    86,
      88,    92,    99,   105,     0,   504,   152,   145,   145,     0,
      62,   152,   152,   145,   152,   152,   152,   152,   152,   152,
     152,   152,   152,   152,   152,   152,   152,   152,   152,   152,
     152,   152,   152,   152,   152,   152,   152,   145,   145,   173,
       0,   382,     0,   173,     0,    62,   152,   152,   145,   152,
     152,   152,   152,   152,   152,   152,   152,   152,   152,   152,
     152,   152,   152,   152,   152,   152,   152,   152,   152,   152,
     152,     0,     0,   152,   152,    71,    69,    73,    81,    83,
      85,    87,    89,    90,    91,    93,    94,    95,    96,    97,
      98,   152,   173,   173,   173,   152,    71,    69,    73,    81,
      83,    85,    87,    89,    90,    91,    93,    94,    95,    96,
      97,    98,   173,   173,   173,   173,   139,    61,    61,     0,
      16
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -844,  -844,  -844,  -844,  -372,  -275,    -1,  -844,  -844,   -65,
     502,  -844,  -844,  -844,  -844,  -844,  -186,  -844,  -844,  4776,
    -338,  -820,   337,  -843,  2846,  -310,  1723,   818,  -826,  5167,
    5304,  5440,  5539,  5685,  5787,  5896,  4767,  6086,  -844,  2670,
    -844,  -844,  -116,  -142,  -844,  -271,  5045,  -844,  -844,  -844,
    -844,  -844,  -844,  -844,  -844,   585,  -844,   335,  -844,  -844,
     215,  -844,  -844,   154,   256,   128,   449,  -844,  -844,  -844,
    -844,  -844,  -844,  -844,   195,  -844,  -844,  -844,  -844,  -365,
    -844,  -844,  -844,  -844,  -844,  -844,   261,   263,  -844,  -844,
    -844,   333,  -844,  -844,  -812,  -844,  -844,   514,  -844,  -844,
    -844,  -844,  -844,  -844,  -844,  -844,  -844,  -844,  -844,  -844,
    -844,  -844,  -844,   288,  -844,  -844,  -844,   169,  -844,  -844,
    -844,     1,  -844,    57,  -844,   -11,     7,   -10,  -844,     2,
       4,     6,    20,    12,  -844,  -844,  -844,  -844,  -844,  -844,
     587,   590,    13,  -844,  -844,    14,  -844,  -844,  -844,    23,
    -844,  -844,    25,  -844,  -844,   -13,  4900,  -189,  -844,  -844,
     889,   605,  -844,  -844,   966,   978,  1507,  1569,  1788,  2052,
    2164,  -844,  -244,  -844,  -844,   424,  -396,  2516,  -844,  -844,
    -844,  -844,   331,  -844,  2705,   735,  -844,  -844,   431,  -844,
    -844,  -844,   271,  -844,  -844,  -844,   196,  2861,  3101,  3486,
    3642,  -844,  3704,   124,  3964,  5990,  -844,    -8,  -844,  -844,
    -844,   319,  -844,  -844,  4309,   593,  -844,  -844,   919,  -844,
     490
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
       0,     2,     3,     4,     9,    25,   854,    27,    28,   741,
     456,   457,   597,   458,   459,   460,   229,   546,   655,   301,
     174,   366,   175,   483,   176,   177,   178,   179,   330,   180,
     181,   182,   183,   184,   185,   186,   485,   188,   189,   306,
     479,   475,   313,   293,   520,   190,   191,   380,   294,   192,
     193,   381,   382,   383,   384,   117,   251,   704,   705,   706,
     707,   757,   787,   822,   194,   385,   463,   464,   465,   480,
     616,   617,   746,   747,   748,   618,   619,   476,   477,   397,
     195,   196,   645,   646,   718,   647,   648,   649,   197,   198,
     544,   545,   521,   199,   307,   308,   309,   310,   605,   386,
     387,   535,   536,   537,   538,   539,   388,   200,   201,   300,
     603,   202,   203,   389,   700,   390,   753,   754,   807,   755,
     805,    57,    90,    53,    30,    31,    32,    33,    76,    34,
      35,    36,    37,    38,   231,   232,   400,   550,   233,   234,
     235,   236,    39,   237,   238,    40,    66,    67,    68,    41,
      70,    71,    42,    54,    55,    43,   118,   119,   204,   205,
     120,   206,   122,   287,   207,   208,   209,   210,   211,   212,
     213,   255,   415,   416,   417,   418,   561,   214,   247,   556,
     557,   558,   559,   769,   215,   409,   410,   411,   412,   730,
     731,   732,   733,   774,   775,   776,   777,   216,   217,   218,
     219,   420,   220,   260,   221,   138,   252,   581,   582,   583,
     584,   585,   678,   586,   222,   223,    45,   522,    56,   577,
      93
};

/* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule whose
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] =
{
       7,   296,    51,   516,    73,   379,    58,    59,    26,   484,
    -404,  -139,   116,   421,    48,    26,    26,    52,   566,    60,
     454,    61,    49,    62,   462,  -255,   543,   508,   509,    63,
      64,    65,   302,   906,  -404,    50,   375,   562,   533,   899,
      69,    84,    72,   567,   298,  -387,   925,   320,   653,   571,
     572,     8,  -389,   902,     5,     6,    85,   964,     1,   941,
      86,   228,   510,  -515,   930,  -404,    29,   937,   534,    51,
      51,   228,   960,    26,    98,    97,   115,   172,   172,   510,
      -2,    48,    48,   227,  -404,    26,   240,    52,  -390,    49,
      49,    26,   985,   242,    26,    13,   243,  -139,  -139,   228,
    -387,   433,   225,   226,    10,    11,   373,  -389,  -504,    87,
     374,   115,   172,   115,   321,   511,   512,   322,    91,   513,
     903,     5,     6,   904,  -391,  -264,   375,   377,  -387,   228,
      12,   376,  1002,  1003,   938,    75,  1004,   939,  -392,    13,
    -393,   906,  -394,  -390,   115,   299,    74,   827,    75,  -399,
      13,  -491,   827,   827,   827,  -264,   827,   827,   228,   658,
      92,   144,   941,  -504,     5,     6,    46,  -504,  -400,    47,
    -401,   514,  -322,  -322,   228,  -402,  -339,   436,  -387,  -391,
     467,     5,     6,    14,   659,    15,   149,  -395,  1005,   395,
     454,   367,  -345,  -392,   462,  -393,  -389,  -394,     5,     6,
     228,    16,    95,    17,  -399,   487,   395,  -396,     5,     6,
      18,    19,    20,    21,    22,    23,   228,   377,    24,     5,
       6,    46,  -397,  -400,    47,  -401,   378,  -388,  -403,   396,
    -402,   368,  -368,   369,  -390,  -398,   370,   543,  -177,   288,
      26,  -369,  -395,   115,   115,    84,  -389,  -391,   371,  -392,
     372,   367,   172,   454,  -393,   676,  -394,   462,   289,   115,
     391,  -399,  -396,   115,   115,   244,   163,   164,   165,   166,
     167,   168,   169,   170,   171,  -400,  -401,  -397,  -402,   715,
       5,     6,  -388,  -403,  -390,  -370,   543,   172,   172,   115,
    -398,   961,   827,   369,   455,   827,   370,  -391,   404,  -392,
    -395,  -396,   228,  -397,  -393,    26,  -394,   469,   371,  -388,
     372,  -399,  -403,   172,   827,   172,  -398,  -364,   827,   827,
     827,   827,   827,  -367,  -515,  -400,  -401,  -371,  -402,   827,
     827,   827,   827,   827,   827,   827,   827,   827,   827,   827,
     827,   827,   827,   827,   827,   827,   827,  -372,  -325,   601,
    -395,  -396,    29,  -397,  -373,   228,   228,   228,   744,  -388,
     643,   612,  -403,   241,   827,   827,  -398,   515,   373,   115,
     172,   172,   896,   827,   228,  -229,   228,   798,  -471,   373,
     530,     5,     6,   926,    74,   727,    75,  -264,   375,   395,
     541,   394,   540,   376,  -288,   531,  -325,    84,  -264,   375,
       5,     6,   228,   228,   376,   343,   344,   345,   395,   728,
     245,   377,   602,   729,     5,     6,    86,  -264,    75,   809,
    -438,  -291,   395,   115,  -504,   115,   115,   115,  -264,  -504,
      51,   346,    73,  -504,    58,    59,   172,   172,   347,   172,
     473,   172,   592,   868,    26,    52,   613,    60,   614,    61,
      49,    62,    94,  -337,   337,   338,  -337,    63,    64,    65,
     615,   248,   228,    50,   455,   913,   914,  -374,    69,   827,
      72,   428,  -376,   228,  -333,    96,   172,  -333,   339,   377,
     340,   622,   827,   429,   772,   341,   377,   342,   378,   915,
     377,   916,   948,   949,   811,   253,   917,   228,   918,   378,
     643,   523,   525,   919,   920,   921,  -375,   954,   955,   956,
     115,   115,   115,   115,   259,  -515,   950,   676,   951,     5,
       6,   779,    29,   952,   254,   953,   256,   455,  -334,   922,
     257,  -334,    26,   957,   638,   258,   923,   334,   335,   290,
     958,    82,     5,     6,    83,   654,    26,    26,   656,   657,
     336,   396,   291,  -337,   910,   911,  -337,    80,    81,    84,
     662,    26,   945,   946,   115,   666,    26,   912,   292,   115,
      26,    26,   295,     5,     6,   947,    74,   317,    75,   677,
      73,   395,    58,    59,   228,    29,   508,   509,  -325,  -325,
    -325,   484,    26,  -504,   318,    60,   516,    61,   319,    62,
     323,   541,    44,   115,   331,    63,    64,    65,  -335,    44,
      44,  -335,   172,   332,   172,    74,    69,    75,    72,    29,
    -336,   508,   509,  -336,    29,  -325,   484,  -504,    29,    29,
     172,  -312,  -504,  -312,  -312,  -312,    88,    89,    26,   379,
     710,   172,   172,   714,  -311,   333,  -311,  -311,  -311,   172,
     541,    77,    78,    79,   633,   249,   250,   724,    26,   392,
     393,  -313,   641,  -313,  -313,  -313,   398,    44,   399,   401,
     140,   402,    73,   115,    58,    59,   419,   115,   115,    44,
     407,   379,   121,   427,    26,    44,   396,    60,    44,    61,
     931,    62,   827,   790,   172,   424,   792,    63,    64,    65,
     426,   430,   434,   897,   898,   140,   285,   140,    69,   435,
      72,   468,   855,   855,   470,   471,    29,   121,   268,   121,
     324,   325,   326,   327,   328,   329,   172,   927,   928,   403,
     377,   302,   482,   529,   115,   690,   103,   547,   297,   548,
     931,   677,   554,   172,   931,  -315,   429,  -315,  -315,  -315,
     285,    26,   560,   783,   563,   302,   895,   115,   788,   565,
     115,   568,   828,   172,   172,   570,   578,  -316,   711,  -316,
    -316,  -316,  -314,   604,  -314,  -314,  -314,   579,   595,   172,
     827,   436,   467,   598,   172,   609,  -317,   487,  -317,  -317,
    -317,   610,   620,   433,   931,   931,   621,   115,  -318,   472,
    -318,  -318,  -318,   172,   320,   628,    11,   115,   630,   629,
     631,   436,   467,   931,   931,   931,   931,   636,   634,   637,
     172,   931,   487,   642,   394,   650,  -321,   750,  -321,  -321,
    -321,    12,   651,   660,    44,   673,   674,   140,   140,  -333,
      13,  -333,  -333,  -333,  -334,   680,  -334,  -334,  -334,   121,
     121,   682,   679,   140,   688,   683,   684,   140,   140,   691,
     695,   697,   699,   702,   709,   121,   716,   717,   723,   121,
     121,   855,   722,   734,   735,   736,   738,   739,   115,   172,
     756,   758,   759,   140,    14,   761,    15,   763,   466,   764,
     793,   765,   727,   780,   781,   121,   784,   785,   797,    44,
     800,   564,    16,  -515,    17,  -515,   804,   569,   799,     5,
       6,    18,    19,    20,    21,    22,    23,   808,   810,    24,
     812,   817,   813,   821,  -504,   900,   901,   905,   115,   907,
     909,   935,   115,   908,   936,   940,   348,   349,   942,   350,
     351,   352,   353,   354,   355,   356,   357,   943,   358,   963,
     359,   881,   360,   944,   361,   962,   981,   362,   982,   363,
     515,   364,   365,   140,   983,   902,   984,   599,  1006,   532,
     937,  1010,   708,   823,   791,   121,   803,   635,   766,   768,
     767,   115,   115,   115,   721,   608,   820,   751,   553,   551,
     246,   726,   668,   422,   664,   770,   815,   929,  1009,   743,
       0,   115,   115,   115,   115,   239,     0,     0,     0,   115,
       0,     0,   632,     0,     0,     0,     0,   140,     0,   140,
     140,   140,     0,     0,   525,     0,     0,     0,     0,   121,
       0,   121,   121,   121,   652,     0,     0,   594,    44,     0,
       0,     0,     0,   123,     0,     0,   855,     0,   661,   268,
       0,     0,     0,     0,   525,   124,     0,     0,   466,     0,
       0,     0,     0,   285,     0,     0,     0,   675,     0,     0,
       0,     0,     0,     0,   681,   828,     0,     0,   123,   269,
     123,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     124,   270,   124,     0,     0,     0,     0,     0,     0,     0,
     855,     0,     0,     0,   140,   140,   140,   140,     0,   696,
       0,     0,     0,     0,     0,     0,   121,   121,   121,   121,
       0,   466,     0,   829,     0,     0,    44,     0,     0,     0,
       0,     0,     0,     0,     0,   830,     0,   719,   486,     0,
      44,    44,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    44,     0,     0,   140,     0,
      44,     0,     0,   140,    44,    44,     0,     0,     0,     0,
     121,     0,     0,     0,     0,   121,     0,     0,     0,     0,
       0,     0,     0,     0,   855,     0,   686,     0,     0,   855,
     855,     0,     0,   858,   858,     0,   760,   140,   121,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   881,   121,
     123,   123,     0,     0,   881,   881,     0,     0,     0,     0,
       0,     0,   124,   124,     0,     0,   123,     0,     0,     0,
     123,   123,    44,   881,   855,   855,     0,   782,   124,     0,
     855,     0,   124,   124,     0,     0,     0,     0,     0,     0,
       0,     0,    44,     0,     0,     0,   123,     0,     0,     0,
       0,   855,   855,   855,   881,   881,   801,   140,   124,    11,
       0,   140,   140,     0,     0,   881,     0,     0,   686,   121,
       0,     0,     0,   121,   121,     0,     0,     0,     0,     0,
     121,     0,     0,     0,    12,     0,   881,   881,     0,     0,
     855,   348,   349,    13,   350,   351,   352,   353,   354,   355,
     356,   357,     0,   358,     0,   359,     0,   360,   881,   361,
       0,     0,   362,     0,   363,     0,   364,   924,   140,     0,
       0,     0,     0,     0,     0,     0,   123,     0,     0,     0,
     121,     0,     0,     0,     0,    44,   228,    14,   124,    15,
     686,   140,   858,     0,   140,    11,     0,     0,     0,     0,
       0,     0,   121,   121,     0,    16,   121,    17,  -359,     0,
       0,     0,     5,     6,    18,    19,    20,    21,    22,    23,
      12,     0,    24,     0,     0,     0,     0,     0,     0,    13,
     123,   140,   123,   123,   123,     0,     0,     0,     0,     0,
       0,   140,   124,   121,   124,   124,   124,     0,     0,     0,
     269,     0,     0,   121,     0,     0,     0,     0,     0,     0,
       0,     0,   270,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   884,    14,     0,    15,   829,     0,     0,     0,
       0,     0,     0,     0,     0,   285,     0,     0,   830,     0,
       0,    16,  -378,    17,     0,     0,     0,   828,     5,     6,
      18,    19,    20,    21,    22,    23,     0,     0,    24,     0,
     285,     0,   140,   285,     0,     0,     0,   123,   123,   123,
     123,     0,   828,     0,   121,   268,     0,     0,     0,   124,
     124,   124,   124,   348,   349,     0,   350,   351,   352,   353,
     354,   355,   356,   357,     0,   358,     0,   359,     0,   360,
       0,   361,     0,     0,   362,     0,   363,     0,   364,   959,
       0,     0,   140,     0,     0,     0,   140,   858,     0,     0,
       0,   123,     0,     0,   121,     0,   123,     0,   121,     0,
       0,     0,     0,   124,     0,     0,     0,     0,   124,     0,
       0,     0,     0,     0,     0,     0,   285,     0,     0,   123,
       0,     0,     0,     0,     0,     0,     0,     0,   828,     0,
     123,   124,     0,     0,   285,   140,   140,   140,     0,     0,
       0,   858,   124,     0,   125,     0,   828,   121,   121,   121,
       0,     0,     0,     0,     0,   140,   140,   140,   140,     0,
       0,     0,     0,   140,     0,     0,     0,   121,   121,   121,
     121,     0,     0,     0,     0,   121,     0,     0,     0,   125,
     271,   125,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     123,     0,     0,     0,   123,   123,   126,     0,     0,     0,
       0,   123,   124,     0,     0,     0,   124,   124,     0,     0,
       0,     0,     0,   124,   831,   858,     0,     0,     0,     0,
     858,   858,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   126,   272,   126,     0,     0,     0,     0,     0,   884,
       0,     0,     0,     0,     0,   884,   884,     0,     0,     0,
       0,   123,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   124,   884,   858,   858,     0,     0,   858,
     965,   858,   858,   123,   123,     0,   832,   123,     0,     0,
       0,     0,     0,     0,     0,   124,   124,     0,     0,   124,
       0,     0,   858,   858,   858,   884,   884,     0,     0,     0,
       0,   125,   125,     0,   884,   986,   884,   884,     0,     0,
       0,     0,     0,     0,   123,     0,     0,   125,     0,     0,
       0,   125,   125,     0,   123,     0,   124,   884,   884,     0,
       0,   858,   858,    11,     0,     0,   124,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   125,     0,   884,
       0,     0,     0,   884,     0,     0,     0,     0,    12,     0,
       0,     0,     0,   126,   126,     0,     0,    13,   829,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   126,
     830,     0,     0,   126,   126,     0,     0,     0,     0,     0,
       0,     0,     0,   829,     0,   123,   269,     0,     0,     0,
       0,     0,     0,     0,     0,   830,     0,   124,   270,   126,
       0,    14,     0,    15,     0,   127,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   125,     0,    16,
       0,    17,  -359,     0,     0,     0,     5,     6,    18,    19,
      20,    21,    22,    23,     0,   123,    24,     0,     0,   123,
     127,   273,   127,     0,     0,     0,     0,   124,     0,     0,
       0,   124,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   829,
       0,   125,     0,   125,   125,   125,     0,     0,     0,   126,
       0,   830,     0,     0,     0,   833,     0,   829,   123,   123,
     123,   271,     0,     0,     0,     0,     0,     0,     0,   830,
     124,   124,   124,     0,     0,     0,     0,     0,   123,   123,
     123,   123,     0,     0,     0,     0,   123,   831,     0,     0,
     124,   124,   124,   124,     0,     0,     0,     0,   124,     0,
       0,     0,     0,   126,     0,   126,   126,   126,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   272,     0,     0,     0,     0,   125,   125,
     125,   125,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   127,   127,     0,     0,     0,     0,     0,   832,
       0,     0,     0,     0,     0,   488,     0,     0,   127,     0,
       0,     0,   127,   127,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   125,     0,     0,     0,     0,   125,   127,     0,
     126,   126,   126,   126,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    99,     0,     0,   857,   857,
     125,     0,     0,   142,   100,     0,     0,     0,     0,     0,
     101,   125,   102,     0,   103,   144,     0,     0,     0,     0,
       0,     0,   145,     0,   146,   104,   147,     0,     0,   128,
       0,     0,     0,     0,   126,   105,   106,     0,   107,   126,
     149,   150,     0,   109,   151,   152,   110,     0,     0,   153,
     111,     0,     0,     0,   154,   155,   156,     0,   127,     0,
       0,     0,   126,     0,   128,   274,   128,     0,     0,     0,
       0,     0,     0,   126,     0,     0,     0,     0,   157,     0,
       0,   125,     0,     0,     0,   125,   125,     0,     0,     0,
       0,     0,   125,     0,     0,   158,     0,     0,     0,   159,
     160,     0,     0,     0,     0,     0,     0,     0,   112,   834,
       0,   113,   127,   161,   127,   127,   127,   162,     5,     6,
     163,   164,   165,   166,   167,   168,   169,   170,   171,     0,
       0,     0,   273,     0,     0,     0,     0,     0,     0,     0,
       0,   129,   125,   126,     0,     0,     0,   126,   126,     0,
       0,     0,     0,     0,   126,     0,     0,   857,   833,     0,
       0,     0,     0,     0,   125,   125,     0,     0,   125,     0,
       0,     0,     0,     0,     0,     0,   129,   275,   129,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   128,   128,     0,   127,
     127,   127,   127,     0,   126,   125,     0,     0,     0,     0,
       0,     0,   128,     0,     0,   125,   128,   128,     0,     0,
       0,   835,     0,     0,     0,     0,   126,   126,     0,     0,
     126,     0,     0,     0,     0,     0,     0,   883,     0,     0,
       0,     0,   128,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   127,     0,     0,     0,     0,   127,   831,
       0,     0,     0,     0,     0,     0,     0,   126,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   126,     0,     0,
       0,   127,     0,     0,   831,     0,   125,   271,     0,     0,
       0,     0,   127,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   129,   129,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   832,   128,     0,   129,     0,     0,     0,   129,   129,
       0,     0,   857,     0,     0,     0,   125,     0,     0,     0,
     125,     0,     0,     0,     0,     0,   832,     0,   126,   272,
       0,     0,     0,     0,   129,     0,     0,     0,     0,     0,
       0,     0,   127,     0,     0,     0,   127,   127,     0,     0,
     831,     0,     0,   127,     0,     0,   128,     0,   128,   128,
     128,     0,     0,     0,     0,     0,   857,     0,   831,   125,
     125,   125,     0,     0,     0,     0,   274,     0,   126,     0,
       0,     0,   126,     0,     0,     0,     0,     0,     0,   125,
     125,   125,   125,     0,     0,     0,     0,   125,     0,     0,
       0,     0,   834,   127,     0,     0,     0,     0,     0,     0,
       0,     0,   832,     0,   129,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   127,   127,     0,     0,   127,
     832,   126,   126,   126,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   128,   128,   128,   128,     0,     0,     0,
     857,   126,   126,   126,   126,   857,   857,     0,     0,   126,
       0,     0,     0,     0,     0,     0,   127,     0,   129,     0,
     129,   129,   129,   130,   883,     0,   127,     0,     0,     0,
     883,   883,     0,     0,     0,     0,     0,     0,   275,     0,
       0,     0,     0,     0,     0,     0,     0,   128,     0,   883,
     857,   857,   128,     0,   857,     0,   857,   966,   130,   276,
     130,     0,     0,     0,   835,     0,     0,     0,     0,     0,
     833,     0,     0,     0,     0,   128,     0,   857,   857,   857,
     883,   883,     0,     0,     0,     0,   128,     0,     0,   883,
       0,   883,   987,     0,     0,   833,     0,   127,   273,     0,
       0,     0,     0,   836,     0,   129,   129,   129,   129,     0,
       0,     0,   883,   883,     0,     0,   857,   857,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   883,     0,     0,     0,   883,     0,
       0,     0,     0,     0,     0,     0,     0,   127,     0,     0,
       0,   127,     0,     0,     0,     0,   128,     0,     0,   129,
     128,   128,     0,     0,   129,     0,     0,   128,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   833,     0,     0,     0,   230,     0,   129,     0,     0,
     130,   130,     0,     0,     0,     0,     0,     0,   129,   833,
     127,   127,   127,     0,    11,     0,   130,     0,     0,     0,
     130,   130,   131,     0,     0,     0,     0,   128,     0,     0,
     127,   127,   127,   127,     0,     0,     0,     0,   127,    12,
       0,     0,     0,     0,     0,     0,   130,     0,    13,   128,
     128,     0,     0,   128,     0,     0,     0,   131,   277,   131,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   314,
     315,   316,     0,     0,     0,     0,     0,     0,   129,     0,
       0,     0,   129,   129,     0,     0,     0,     0,     0,   129,
     128,     0,    14,     0,    15,     0,     0,     0,     0,     0,
     128,     0,   837,     0,     0,     0,     0,     0,     0,     0,
      16,     0,    17,  -355,     0,     0,     0,     5,     6,    18,
      19,    20,    21,    22,    23,     0,   130,    24,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   129,
       0,     0,     0,     0,   834,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   408,     0,
       0,   129,   129,     0,   414,   129,     0,   414,   408,   834,
       0,   128,   274,     0,     0,   316,     0,     0,   132,     0,
     130,     0,   130,   130,   130,     0,     0,     0,     0,   131,
     131,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     276,     0,   129,     0,     0,   131,     0,     0,     0,   131,
     131,     0,   129,   132,   278,   132,     0,     0,     0,     0,
       0,   128,     0,     0,     0,   128,   836,     0,     0,     0,
       0,     0,     0,     0,     0,   131,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   834,   835,     0,   838,     0,
       0,     0,     0,     0,     0,     0,     0,   130,   130,   130,
     130,     0,     0,   834,   128,   128,   128,     0,     0,     0,
       0,   835,     0,   129,   275,     0,     0,   528,     0,     0,
       0,     0,     0,     0,   128,   128,   128,   128,     0,     0,
       0,   542,   128,     0,     0,     0,     0,     0,     0,   549,
       0,   552,     0,     0,     0,   131,     0,   555,     0,     0,
       0,   130,     0,     0,     0,     0,   130,     0,     0,     0,
       0,     0,     0,   129,     0,     0,     0,   129,     0,     0,
       0,     0,     0,     0,   580,   132,   132,     0,     0,   130,
       0,     0,     0,     0,     0,   316,     0,     0,     0,     0,
     130,   132,     0,     0,     0,   132,   132,   835,     0,   131,
       0,   131,   131,   131,     0,     0,     0,     0,     0,     0,
       0,    99,     0,     0,     0,   835,   129,   129,   129,   277,
     100,   132,     0,     0,     0,     0,   101,     0,   102,     0,
     103,     0,  -173,     0,     0,     0,   129,   129,   129,   129,
       0,   104,     0,     0,   129,   837,     0,     0,   133,     0,
       0,   105,   106,     0,   107,     0,     0,   108,     0,   109,
     130,     0,   110,     0,   130,   130,   111,     0,     0,     0,
       0,   130,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   644,   133,   279,   133,   131,   131,   131,   131,
       0,   856,   856,     0,     0,     0,     0,     0,     0,     0,
       0,   132,     0,   408,     0,     0,     0,     0,   414,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   130,     0,     0,   112,     0,     0,   113,   839,   114,
       0,     0,     0,   316,     5,     6,     0,     0,     0,     0,
     131,     0,   687,   130,   130,   131,     0,   130,     0,     0,
       0,     0,     0,     0,     0,   132,     0,   132,   132,   132,
       0,     0,     0,    99,     0,     0,     0,     0,   131,     0,
       0,     0,   100,     0,   701,   278,   703,   703,   101,   131,
     102,     0,   103,     0,   130,     0,     0,     0,     0,     0,
       0,     0,     0,   104,   130,     0,     0,     0,     0,   623,
     555,   838,     0,   105,   106,     0,   107,     0,     0,   108,
       0,   109,     0,     0,   110,   133,   133,     0,   111,     0,
     742,     0,     0,     0,     0,     0,     0,   644,     0,     0,
       0,   133,     0,     0,     0,   133,   133,     0,   836,     0,
       0,   752,   132,   132,   132,   132,     0,     0,     0,   131,
     856,     0,     0,   131,   131,     0,     0,   644,     0,     0,
     131,   133,     0,   836,     0,   130,   276,     0,   414,   773,
    -483,     0,     0,     0,     0,     0,   112,     0,     0,   113,
       0,   114,     0,     0,     0,     0,     5,     6,     0,     0,
       0,     0,     0,     0,   669,     0,   132,     0,     0,   703,
       0,   132,     0,     0,     0,     0,     0,     0,     0,     0,
     131,     0,     0,     0,     0,   130,     0,     0,     0,   130,
       0,     0,     0,     0,   132,     0,     0,     0,     0,     0,
     882,     0,   131,   131,     0,   132,   131,     0,     0,     0,
     773,   133,     0,     0,     0,     0,     0,     0,     0,   836,
       0,     0,     0,     0,     0,     0,     0,   752,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   836,   130,   130,
     130,     0,     0,   131,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   131,     0,     0,     0,     0,   130,   130,
     130,   130,     0,     0,     0,   133,   130,   133,   133,   133,
       0,     0,    99,     0,     0,   132,     0,     0,     0,   132,
     132,   100,     0,     0,     0,   279,   132,   101,     0,   102,
       0,   103,     0,     0,     0,   856,     0,   837,     0,     0,
       0,     0,   104,   134,     0,     0,     0,     0,     0,     0,
       0,   839,   105,   106,     0,   107,     0,     0,   108,     0,
     109,     0,   837,   110,   131,   277,     0,   111,     0,     0,
       0,     0,     0,     0,     0,     0,   132,     0,   134,   280,
     134,     0,     0,     0,     0,     0,     0,     0,     0,   856,
       0,     0,   133,   133,   133,   133,     0,     0,   132,   132,
       0,     0,   132,     0,     0,     0,     0,     0,     0,   228,
       0,     0,     0,     0,   131,     0,     0,     0,   131,     0,
       0,     0,     0,   840,     0,   112,     0,     0,   113,     0,
     114,  -427,     0,     0,     0,     5,     6,     0,     0,   132,
       0,     0,     0,     0,     0,     0,   133,     0,   837,   132,
       0,   133,     0,     0,     0,     0,   580,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   837,   131,   131,   131,
       0,     0,     0,   856,   133,     0,     0,     0,   856,   856,
       0,     0,     0,     0,     0,   133,     0,   131,   131,   131,
     131,     0,     0,   838,     0,   131,     0,   882,     0,   135,
       0,     0,     0,   882,   882,     0,     0,     0,     0,     0,
     134,   134,     0,     0,     0,     0,     0,     0,   838,     0,
     132,   278,   882,   856,   856,     0,   134,     0,     0,   856,
     134,   134,     0,     0,   135,   281,   135,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     856,   856,   856,   882,   882,   133,   134,     0,     0,   133,
     133,   136,     0,     0,   882,     0,   133,     0,     0,     0,
     132,     0,     0,     0,   132,     0,     0,     0,     0,   841,
       0,     0,     0,     0,     0,   882,   882,     0,     0,   856,
    1007,     0,     0,     0,     0,     0,   136,   282,   136,     0,
       0,     0,     0,     0,   838,     0,     0,   882,     0,     0,
       0,  1008,     0,     0,     0,     0,   133,     0,     0,     0,
       0,     0,   838,   132,   132,   132,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   134,     0,   133,   133,
       0,   842,   133,   132,   132,   132,   132,     0,     0,     0,
       0,   132,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   135,   135,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   133,
       0,     0,   135,     0,     0,     0,   135,   135,     0,   133,
     134,     0,   134,   134,   134,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     280,     0,   135,     0,     0,     0,     0,     0,     0,     0,
      11,     0,     0,     0,     0,     0,     0,     0,   136,   136,
       0,     0,     0,   839,     0,     0,   840,     0,     0,     0,
       0,     0,     0,     0,   136,    12,     0,     0,   136,   136,
       0,     0,     0,     0,    13,     0,    99,     0,   839,     0,
     133,   279,     0,     0,     0,   100,     0,     0,     0,     0,
       0,   101,     0,   102,   136,   103,     0,   134,   134,   134,
     134,     0,     0,     0,     0,     0,   104,     0,     0,     0,
       0,     0,   135,     0,     0,     0,   105,   106,    14,   107,
      15,     0,   108,     0,   109,     0,     0,   110,     0,     0,
     133,   111,     0,     0,   133,     0,    16,     0,    17,  -363,
       0,   137,     0,     5,     6,    18,    19,    20,    21,    22,
      23,   134,     0,    24,     0,     0,   134,     0,     0,     0,
       0,     0,     0,     0,   839,     0,   135,     0,   135,   135,
     135,     0,     0,     0,   136,     0,   137,   283,   137,   134,
       0,     0,   839,   133,   133,   133,   281,     0,     0,   112,
     134,     0,   113,     0,   114,  -427,     0,     0,     0,     5,
       6,     0,     0,   133,   133,   133,   133,     0,     0,     0,
       0,   133,   841,     0,     0,     0,     0,     0,     0,     0,
       0,   843,     0,     0,     0,     0,     0,     0,   136,     0,
     136,   136,   136,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    99,     0,     0,     0,     0,     0,   282,     0,
       0,   100,     0,   135,   135,   135,   135,   101,     0,   102,
     134,   103,     0,     0,   134,   134,     0,     0,     0,     0,
       0,   134,   104,     0,   842,     0,     0,     0,     0,     0,
       0,     0,   105,   106,     0,   107,     0,     0,   108,     0,
     109,     0,     0,   110,     0,     0,     0,   111,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   135,   137,   137,
       0,     0,   135,     0,     0,   136,   136,   136,   136,     0,
       0,   134,     0,     0,   137,     0,     0,     0,   137,   137,
       0,     0,     0,     0,     0,   135,     0,     0,     0,     0,
       0,     0,     0,   134,   134,     0,   135,   134,     0,     0,
       0,     0,     0,     0,   137,   112,     0,     0,   113,     0,
     114,  -515,     0,     0,     0,     5,     6,     0,     0,   136,
       0,     0,     0,     0,   136,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   134,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   134,     0,     0,   136,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   136,     0,
       0,     0,     0,    99,     0,     0,   135,     0,     0,     0,
     135,   135,   100,     0,     0,     0,     0,   135,   101,     0,
     102,     0,   103,     0,   137,     0,     0,     0,   840,     0,
       0,     0,     0,   104,     0,     0,     0,     0,     0,     0,
      11,     0,     0,   105,   106,     0,   107,     0,     0,   108,
       0,   109,     0,   840,   110,   134,   280,     0,   111,     0,
       0,     0,     0,     0,     0,    12,     0,   135,   136,     0,
       0,     0,   136,   136,    13,     0,   139,     0,   137,   136,
     137,   137,   137,     0,     0,     0,     0,     0,     0,   135,
     135,     0,     0,   135,     0,     0,     0,     0,   283,     0,
       0,     0,     0,     0,     0,   134,     0,     0,     0,   134,
       0,   139,   284,   139,     0,     0,   112,     0,    14,   113,
      15,   114,     0,     0,   843,     0,     5,     6,     0,   136,
     135,     0,     0,     0,     0,   663,    16,     0,    17,   840,
     135,     0,     0,     5,     6,    18,    19,    20,    21,    22,
      23,   136,   136,    24,     0,   136,   844,   840,   134,   134,
     134,     0,     0,     0,     0,   137,   137,   137,   137,     0,
       0,     0,     0,     0,    99,     0,     0,     0,   134,   134,
     134,   134,     0,   100,   841,     0,   134,     0,     0,   101,
       0,   102,   136,   103,     0,     0,     0,     0,     0,     0,
       0,     0,   136,     0,   104,     0,     0,     0,     0,   841,
       0,   135,   281,     0,   105,   106,     0,   107,     0,   137,
     108,     0,   109,     0,   137,   110,     0,     0,     0,   111,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   139,   139,     0,   842,   137,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   137,   139,
       0,   135,     0,   139,   139,   135,     0,     0,     0,     0,
       0,   842,     0,   136,   282,     0,   818,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   112,     0,   139,
     113,     0,   114,     0,     0,   841,     0,     5,     6,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   841,   135,   135,   135,     0,     0,     0,
       0,     0,     0,   136,     0,     0,     0,   136,   137,     0,
       0,     0,   137,   137,   135,   135,   135,   135,     0,   137,
       0,     0,   135,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   842,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   139,
       0,     0,     0,    99,     0,   842,   136,   136,   136,     0,
       0,     0,   100,     0,     0,     0,     0,     0,   101,   137,
     102,     0,   103,     0,     0,     0,   136,   136,   136,   136,
       0,     0,     0,   104,   136,     0,     0,     0,     0,     0,
       0,   137,   137,   105,   106,   137,   107,     0,     0,   108,
       0,   109,     0,   139,   110,   139,   139,   139,   873,     0,
      99,     0,     0,     0,     0,     0,     0,     0,     0,   100,
       0,     0,     0,   284,     0,   101,     0,   102,     0,   103,
      11,     0,   137,     0,     0,     0,     0,     0,     0,     0,
     104,     0,   137,     0,     0,     0,     0,     0,     0,   844,
     105,   106,     0,   107,     0,    12,   108,     0,   109,     0,
       0,   110,     0,     0,    13,   111,   879,     0,     0,   880,
       0,   114,     0,     0,     0,     0,     5,     6,     0,     0,
       0,     0,     0,     0,     0,     0,   843,     0,     0,     0,
     139,   139,   139,   139,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   228,    14,     0,
      15,   843,     0,   137,   283,   187,   187,     0,     0,     0,
       0,     0,     0,   112,   173,   224,   444,     0,   685,  -359,
       0,     0,     0,     5,     6,    18,    19,    20,    21,    22,
      23,     0,     0,    24,   139,     0,     0,     0,     0,   139,
     187,     0,     0,     0,     0,     0,     0,     0,     0,   266,
       0,     0,     0,   137,     0,     0,     0,   137,     0,     0,
       0,     0,   139,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   139,     0,   187,     0,     0,     0,     0,
     303,   304,   305,     0,   187,   187,     0,   843,    11,     0,
       0,     0,     0,   311,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   843,   137,   137,   137,     0,
       0,     0,     0,    12,     0,     0,     0,     0,     0,     0,
       0,     0,    13,     0,     0,     0,   137,   137,   137,   137,
       0,     0,     0,     0,   137,     0,     0,     0,     0,     0,
       0,     0,     0,   139,     0,     0,     0,   139,   139,     0,
       0,     0,     0,     0,   139,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    14,     0,    15,     0,
       0,     0,   261,   267,   286,     0,     0,     0,     0,     0,
     187,     0,     0,   667,    16,     0,    17,     0,     0,   413,
       0,     5,     6,    18,    19,    20,    21,    22,    23,     0,
       0,    24,     0,     0,   139,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   187,   187,   312,     0,     0,
     187,     0,   187,   187,   431,   432,   139,   139,     0,     0,
     139,   461,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   187,   187,   187,     0,     0,     0,     0,   187,     0,
     474,   478,   481,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   139,     0,     0,
     503,   504,   505,   506,   507,     0,     0,   139,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   187,   187,     0,     0,     0,     0,   187,   187,
       0,   187,   866,   866,   405,   406,     0,   518,   519,     0,
     524,   526,   527,    11,     0,     0,     0,     0,     0,     0,
     423,   844,     0,     0,   425,   286,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    12,     0,
       0,     0,     0,     0,     0,     0,   844,    13,   139,   284,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   187,   187,     0,   187,     0,   303,
     187,   187,     0,   587,   588,     0,   589,     0,     0,     0,
     266,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    14,   187,    15,     0,     0,     0,   187,   139,     0,
       0,   600,   139,    11,   187,     0,   606,     0,   671,    16,
       0,    17,     0,   611,     0,     0,     5,     6,    18,    19,
      20,    21,    22,    23,     0,     0,    24,     0,    12,     0,
     517,     0,   844,     0,     0,     0,     0,    13,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     844,   139,   139,   139,     0,   187,     0,     0,     0,     0,
       0,   866,     0,     0,   461,     0,     0,     0,     0,     0,
     640,   139,   139,   139,   139,     0,     0,     0,     0,   139,
       0,    14,     0,    15,   573,     0,   574,   575,   576,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   672,    16,
     825,    17,     0,     0,   267,     0,     5,     6,    18,    19,
      20,    21,    22,    23,     0,     0,    24,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     607,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     187,   892,   187,     0,     0,     0,     0,     0,     0,   692,
     693,   694,     0,     0,     0,     0,     0,     0,   187,     0,
       0,     0,     0,     0,     0,     0,     0,   698,     0,   187,
     187,   624,   625,   626,   627,     0,     0,   187,   712,   713,
     867,   867,     0,     0,     0,     0,   720,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     187,     0,   187,     0,     0,   665,     0,     0,     0,   745,
     670,   749,     0,     0,     0,     0,   866,     0,     0,     0,
       0,     0,     0,     0,     0,   762,     0,     0,     0,     0,
     489,     0,     0,   286,   187,     0,     0,     0,     0,     0,
       0,     0,     0,   771,   689,     0,     0,     0,     0,     0,
     825,   187,     0,     0,     0,     0,     0,     0,     0,     0,
     713,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     866,   187,   187,     0,     0,     0,     0,     0,     0,   794,
     795,   796,   859,   859,     0,     0,     0,   187,   187,     0,
       0,     0,   187,     0,     0,     0,   802,   745,     0,     0,
       0,   806,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   187,     0,   825,   737,     0,     0,     0,   740,   867,
     816,     0,     0,     0,     0,   286,     0,     0,   187,     0,
       0,     0,     0,     0,     0,     0,     0,   824,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   866,   303,   304,   305,     0,   866,
     866,     0,     0,     0,     0,     0,     0,     0,   311,     0,
       0,     0,     0,     0,   490,   778,     0,    11,   892,   303,
       0,   304,   305,     0,   892,   892,     0,   187,     0,     0,
       0,     0,     0,   311,     0,     0,   934,   789,     0,   825,
       0,     0,    12,   892,   866,   866,     0,     0,     0,     0,
     866,    13,   524,     0,     0,     0,     0,     0,     0,   860,
     860,     0,     0,     0,     0,     0,   503,   504,   505,   506,
     507,   866,   866,   866,   892,   892,     0,     0,   814,     0,
       0,   859,   524,     0,     0,   892,     0,     0,   819,     0,
       0,     0,     0,     0,     0,    14,     0,    15,     0,     0,
       0,   503,   504,   505,   506,   507,   892,   892,     0,     0,
     866,     0,   725,    16,     0,    17,     0,     0,     0,   606,
       5,     6,    18,    19,    20,    21,    22,    23,   892,     0,
      24,     0,   312,     0,   867,     0,     0,   606,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   491,     0,     0,     0,     0,     0,   312,     0,   261,
     267,   885,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   867,     0,
       0,     0,     0,     0,     0,   861,   861,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   423,
       0,     0,     0,   425,     0,     0,     0,     0,   860,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   607,     0,     0,     0,     0,     0,     0,
       0,   492,     0,     0,     0,     0,   859,     0,     0,     0,
       0,   607,     0,   573,   574,     0,     0,     0,     0,     0,
       0,     0,   867,   867,   867,   867,     0,   867,   867,     0,
       0,     0,   624,   625,   626,   627,     0,     0,     0,     0,
       0,     0,     0,     0,   862,   862,   825,   825,   886,   825,
     825,     0,   825,   825,     0,     0,     0,     0,     0,     0,
     859,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   825,   867,   867,     0,     0,   867,   867,   867,   867,
     867,   867,   867,   867,   867,   867,   867,   867,   867,   867,
     867,   867,   867,   867,   867,   867,   867,   867,   867,   867,
     867,   867,   825,   825,   861,     0,     0,     0,     0,     0,
       0,   825,   825,   825,   825,   825,   825,   825,   825,   825,
     825,   825,   825,   825,   825,   825,   825,   825,   825,   825,
     825,   825,   825,   825,   825,   825,     0,     0,   867,   867,
       0,     0,     0,   860,   859,     0,     0,     0,   493,   859,
     859,     0,     0,     0,     0,     0,   825,     0,     0,     0,
     825,     0,     0,     0,     0,     0,     0,     0,   885,     0,
       0,     0,     0,     0,   885,   885,     0,     0,     0,     0,
       0,     0,     0,     0,   887,     0,     0,     0,     0,     0,
     863,   863,     0,   885,   859,   859,     0,   860,   859,   859,
     859,   859,   967,   862,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   859,   859,   859,   885,   885,     0,     0,     0,     0,
       0,     0,     0,   885,   885,   885,   885,   988,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   494,   495,   496,     0,     0,   885,   885,     0,     0,
     859,   859,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   885,   861,
       0,   860,   885,   888,     0,     0,   860,   860,     0,     0,
       0,     0,   864,   864,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   886,     0,     0,     0,     0,
       0,   886,   886,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     886,   860,   860,   861,     0,   860,   860,   860,   860,   860,
     968,     0,     0,     0,     0,     0,     0,     0,     0,   863,
       0,     0,     0,     0,     0,     0,     0,     0,   860,   860,
     860,   886,   886,   497,   498,   499,   500,   501,   502,     0,
     886,   886,   886,   886,   886,   989,     0,     0,   862,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   886,   886,     0,     0,   860,   860,     0,
       0,   865,   865,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   886,     0,   861,     0,   886,
       0,     0,   861,   861,     0,     0,     0,     0,     0,   889,
       0,     0,   862,     0,     0,     0,     0,     0,     0,     0,
       0,   887,     0,     0,     0,     0,     0,   887,   887,     0,
       0,   864,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   887,   861,   861,     0,
       0,   861,   861,   861,   861,   861,   861,   969,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   861,   861,   861,   887,   887,     0,
       0,     0,     0,     0,     0,     0,   887,   887,   887,   887,
     887,   887,   990,     0,     0,     0,   862,     0,     0,     0,
       0,   862,   862,     0,   863,     0,     0,     0,     0,   887,
     887,   890,     0,   861,   861,     0,     0,     0,     0,     0,
     888,     0,     0,     0,     0,     0,   888,   888,     0,     0,
       0,   887,     0,     0,     0,   887,     0,     0,     0,     0,
     865,     0,     0,     0,     0,   888,   862,   862,     0,     0,
     862,   862,   862,   862,   862,   862,   862,   970,   863,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    11,     0,   862,   862,   862,   888,   888,     0,     0,
       0,     0,     0,     0,     0,   888,   888,   888,   888,   888,
     888,   888,   991,     0,     0,     0,    12,     0,     0,     0,
       0,     0,     0,     0,     0,    13,   864,     0,   888,   888,
       0,     0,   862,   862,     0,     0,     0,     0,     0,     0,
     891,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     888,     0,     0,     0,   888,     0,     0,     0,     0,     0,
       0,     0,   863,     0,     0,     0,     0,   863,   863,    14,
       0,    15,     0,     0,     0,     0,     0,     0,     0,     0,
     864,     0,     0,     0,     0,     0,   889,    16,     0,    17,
       0,     0,   889,   889,     5,     6,    18,    19,    20,    21,
      22,    23,     0,     0,    24,     0,     0,     0,     0,     0,
       0,   889,   863,   863,     0,     0,   863,   863,   863,   863,
     863,   863,   863,   863,   971,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   894,   865,     0,     0,     0,   863,
     863,   863,   889,   889,     0,     0,     0,     0,     0,     0,
       0,   889,   889,   889,   889,   889,   889,   889,   889,   992,
       0,     0,     0,     0,   864,     0,     0,     0,     0,   864,
     864,     0,     0,     0,   889,   889,     0,     0,   863,   863,
       0,     0,     0,     0,     0,     0,     0,     0,   890,   865,
       0,     0,     0,     0,   890,   890,   889,     0,     0,     0,
     889,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   890,   864,   864,     0,     0,   864,   864,
     864,   864,   864,   864,   864,   864,   864,   972,   973,   974,
     893,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   864,   864,   864,   890,   890,     0,     0,     0,     0,
       0,     0,     0,   890,   890,   890,   890,   890,   890,   890,
     890,   890,   993,   994,   995,     0,     0,     0,     0,     0,
       0,     0,     0,   865,     0,     0,   890,   890,   865,   865,
     864,   864,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   891,   890,     0,
       0,     0,   890,   891,   891,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   891,   865,   865,     0,     0,   865,   865,   865,
     865,   865,   865,   865,   865,   865,   865,   865,   865,   975,
     976,   977,   978,   979,   980,     0,     0,     0,     0,     0,
     865,   865,   865,   891,   891,     0,     0,     0,     0,     0,
       0,     0,   891,   891,   891,   891,   891,   891,   891,   891,
     891,   891,   891,   891,   996,   997,   998,   999,  1000,  1001,
       0,     0,     0,     0,     0,   891,   891,     0,     0,   865,
     865,   894,   894,     0,   894,   894,     0,   894,   894,   894,
       0,     0,     0,     0,     0,     0,     0,   891,     0,     0,
       0,   891,     0,     0,     0,     0,   894,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   894,   894,   894,
       0,     0,     0,   894,     0,     0,   894,   894,   894,   894,
     894,   894,   894,   894,   894,   894,   894,   894,   894,   894,
     894,   894,   894,   894,   894,   894,   894,   894,   894,   894,
     894,     0,     0,     0,     0,     0,     0,   893,   893,     0,
     893,   893,     0,   893,   893,     0,     0,     0,     0,     0,
       0,   894,   894,   894,   894,   894,     0,     0,     0,     0,
       0,     0,   893,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   894,   894,   894,   894,     0,     0,     0,     0,
     894,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   893,   893,     0,     0,     0,     0,     0,
       0,     0,   893,   893,   893,   893,   893,   893,   893,   893,
     893,   893,   893,   893,   893,   893,   893,   893,   893,   893,
     893,   893,   893,   893,   893,   893,   893,     0,     0,     0,
       0,     0,     0,    99,     0,     0,  -152,     0,   141,     0,
    -152,   142,   100,     0,   143,     0,     0,   893,   101,     0,
     102,   893,   103,   144,  -152,  -152,  -152,     0,     0,     0,
     145,  -152,   146,   104,   147,     0,     0,     0,     0,  -152,
       0,   148,     0,   105,   106,     0,   107,     0,   149,   150,
       0,   109,   151,   152,   110,  -152,     0,   153,   111,     0,
       0,     0,   154,   155,   156,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   157,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
    -152,     0,     0,   158,     0,     0,     0,   159,   160,     0,
       0,     0,     0,     0,     0,     0,   112,  -152,     0,   113,
       0,   161,     0,     0,     0,   162,     5,     6,   163,   164,
     165,   166,   167,   168,   169,   170,   171,    99,     0,     0,
       0,     0,   141,  -145,     0,   142,   100,     0,   143,     0,
       0,     0,   101,     0,   102,     0,   103,   144,     0,     0,
       0,     0,     0,     0,   145,     0,   146,   104,   147,     0,
       0,  -145,     0,     0,     0,   148,     0,   105,   106,     0,
     107,     0,   149,   150,     0,   109,   151,   152,   110,     0,
       0,   442,   111,     0,     0,     0,   154,   155,   156,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     157,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   158,     0,     0,
       0,   159,   160,     0,  -328,     0,  -328,  -328,  -328,     0,
     112,     0,  -145,   113,  -145,   161,     0,     0,  -145,   162,
       5,     6,   590,   164,   165,   591,   167,   168,   169,   170,
     171,    99,     0,     0,  -152,     0,   845,     0,  -152,   142,
     100,     0,   846,     0,     0,     0,   101,     0,   102,     0,
     103,   144,  -152,  -152,  -152,     0,     0,     0,   145,  -152,
     146,   104,   147,     0,     0,     0,     0,  -152,     0,   847,
       0,   105,   106,     0,   107,     0,   149,   150,     0,   109,
     151,   152,   110,  -152,     0,   848,   111,     0,     0,     0,
     849,   850,   851,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   852,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,  -152,     0,
       0,   853,     0,     0,     0,   159,   160,     0,     0,     0,
       0,     0,     0,     0,   112,     0,     0,   113,     0,   161,
       0,     0,     0,   162,     5,     6,   163,   164,   165,   166,
     167,   168,   169,   170,   171,    99,     0,     0,     0,     0,
     141,     0,     0,   142,   100,     0,   143,     0,   437,     0,
     101,   438,   102,     0,   103,   439,     0,     0,     0,     0,
       0,   440,   145,     0,   146,   104,   147,     0,     0,     0,
       0,     0,     0,   148,     0,   105,   106,     0,   107,     0,
     441,   150,     0,   109,   151,   152,   110,     0,     0,   442,
     111,     0,     0,     0,   154,   155,   156,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   157,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    14,     0,   443,     0,     0,     0,   159,
     160,     0,     0,     0,     0,     0,     0,     0,   112,     0,
    -203,   444,     0,   445,     0,     0,   446,   162,     5,     6,
     447,   448,   449,   450,   451,   452,   169,   170,   453,    99,
       0,     0,     0,     0,   141,     0,     0,   142,   100,     0,
     143,     0,   437,     0,   101,   438,   102,     0,   103,   439,
       0,     0,     0,     0,     0,   440,   145,     0,   146,   104,
     147,     0,     0,     0,     0,     0,     0,   148,     0,   105,
     106,     0,   107,     0,   441,   150,     0,   109,   151,   152,
     110,     0,     0,   442,   111,     0,     0,     0,   154,   155,
     156,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   157,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    14,     0,   443,
       0,     0,     0,   159,   160,     0,     0,     0,     0,     0,
       0,     0,   112,     0,  -145,   444,     0,   445,     0,     0,
     446,   162,     5,     6,   447,   448,   449,   450,   451,   452,
     169,   170,   453,    99,     0,     0,     0,     0,   141,     0,
       0,   142,   100,     0,   143,   262,     0,     0,   101,     0,
     102,     0,   103,   439,     0,     0,     0,     0,     0,     0,
     145,     0,   146,   104,   147,     0,     0,     0,     0,     0,
       0,   148,     0,   105,   106,     0,   107,     0,   441,   263,
       0,   109,   151,   152,   110,     0,     0,   442,   111,     0,
       0,     0,   154,   155,   156,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   157,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    14,     0,   443,     0,     0,     0,   159,   160,     0,
       0,     0,     0,     0,     0,     0,   112,     0,     0,   444,
     264,   593,     0,     0,     0,   162,     5,     6,   447,   448,
     449,   450,   451,   452,   169,   170,   453,    99,     0,     0,
       0,     0,   141,     0,     0,   142,   100,     0,   143,   262,
       0,     0,   101,     0,   102,     0,   103,   144,     0,     0,
       0,     0,     0,     0,   145,     0,   146,   104,   147,     0,
       0,     0,     0,     0,     0,   148,     0,   105,   106,     0,
     107,     0,   149,   263,     0,   109,   151,   152,   110,     0,
       0,   153,   111,     0,     0,     0,   154,   155,   156,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     157,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   158,     0,     0,
       0,   159,   160,     0,     0,     0,     0,     0,     0,     0,
     112,     0,     0,   113,   264,   265,     0,     0,     0,   162,
       5,     6,   163,   164,   165,   166,   167,   168,   169,   170,
     171,    99,     0,     0,     0,     0,   845,     0,     0,   142,
     100,     0,   846,     0,     0,     0,   101,     0,   102,     0,
     103,   144,     0,     0,     0,     0,   639,     0,   145,     0,
     146,   104,   147,     0,     0,     0,     0,     0,     0,   847,
       0,   105,   106,     0,   107,     0,   149,   150,     0,   109,
     151,   152,   110,     0,     0,   848,   111,     0,     0,     0,
     849,   850,   851,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   852,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   853,     0,     0,     0,   159,   160,     0,     0,     0,
       0,     0,     0,     0,   112,   377,     0,   113,     0,   161,
       0,     0,     0,   162,     5,     6,   163,   164,   165,   166,
     167,   168,   169,   170,   171,    99,     0,     0,     0,     0,
     141,     0,     0,   142,   100,     0,   143,   932,     0,     0,
     101,     0,   102,     0,   103,   144,     0,     0,     0,     0,
       0,     0,   145,     0,   146,   104,   147,     0,     0,     0,
       0,     0,     0,   148,     0,   105,   106,     0,   107,     0,
     149,   263,     0,   109,   151,   152,   110,     0,     0,   153,
     111,     0,     0,     0,   154,   155,   156,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   157,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   158,     0,     0,     0,   159,
     160,     0,     0,     0,     0,     0,     0,     0,   112,     0,
       0,   113,   933,   265,     0,     0,     0,   162,     5,     6,
     163,   164,   165,   166,   167,   168,   169,   170,   171,    99,
       0,     0,     0,     0,   141,     0,     0,   142,   100,     0,
     143,     0,     0,     0,   101,     0,   102,     0,   103,   144,
       0,     0,     0,     0,     0,     0,   145,     0,   146,   104,
     147,     0,     0,     0,     0,     0,     0,   148,     0,   105,
     106,     0,   107,     0,   149,   150,     0,   109,   151,   152,
     110,     0,     0,   153,   111,     0,     0,     0,   154,   155,
     156,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   157,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   158,
       0,     0,     0,   159,   160,     0,     0,     0,     0,     0,
       0,     0,   112,     0,     0,   113,     0,   161,  -143,     0,
       0,   162,     5,     6,   163,   164,   165,   166,   167,   168,
     169,   170,   171,    99,     0,     0,     0,     0,   141,     0,
       0,   142,   100,     0,   143,     0,     0,     0,   101,     0,
     102,     0,   103,   144,     0,     0,     0,     0,     0,     0,
     145,     0,   146,   104,   147,     0,     0,     0,     0,     0,
       0,   148,     0,   105,   106,     0,   107,     0,   149,   150,
       0,   109,   151,   152,   110,     0,     0,   153,   111,     0,
       0,     0,   154,   155,   156,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   157,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   158,     0,     0,     0,   159,   160,     0,
       0,     0,     0,     0,     0,     0,   112,     0,     0,   113,
    -141,   161,     0,     0,     0,   162,     5,     6,   163,   164,
     165,   166,   167,   168,   169,   170,   171,    99,     0,     0,
       0,     0,   141,     0,     0,   142,   100,     0,   143,     0,
       0,     0,   101,     0,   102,     0,   103,   144,     0,     0,
       0,     0,     0,     0,   145,     0,   146,   104,   147,     0,
       0,     0,     0,     0,     0,   148,     0,   105,   106,     0,
     107,     0,   149,   150,     0,   109,   151,   152,   110,     0,
       0,   153,   111,     0,     0,     0,   154,   155,   156,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     157,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   158,     0,     0,
       0,   159,   160,     0,     0,     0,     0,     0,     0,     0,
     112,     0,     0,   113,     0,   161,  -149,     0,     0,   162,
       5,     6,   163,   164,   165,   166,   167,   168,   169,   170,
     171,    99,     0,     0,     0,     0,   141,     0,     0,   142,
     100,     0,   143,     0,     0,     0,   101,     0,   102,     0,
     103,   144,     0,     0,     0,     0,     0,     0,   145,     0,
     146,   104,   147,     0,     0,     0,     0,     0,     0,   148,
       0,   105,   106,     0,   107,     0,   149,   150,     0,   109,
     151,   152,   110,     0,     0,   153,   111,     0,     0,     0,
     154,   155,   156,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   157,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   158,     0,     0,     0,   159,   160,     0,     0,     0,
       0,     0,     0,     0,   112,   377,     0,   113,     0,   161,
       0,     0,     0,   162,     5,     6,   163,   164,   165,   166,
     167,   168,   169,   170,   171,    99,     0,     0,     0,     0,
     141,     0,     0,   142,   100,     0,   143,     0,     0,     0,
     101,     0,   102,     0,   103,   144,     0,     0,     0,     0,
       0,     0,   145,     0,   146,   104,   147,     0,     0,     0,
       0,     0,     0,   148,     0,   105,   106,     0,   107,     0,
     149,   150,     0,   109,   151,   152,   110,     0,     0,   153,
     111,     0,     0,     0,   154,   155,   156,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   157,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   158,     0,     0,     0,   159,
     160,     0,     0,     0,     0,     0,     0,     0,   112,     0,
       0,   113,     0,   161,  -145,     0,     0,   162,     5,     6,
     163,   164,   165,   166,   167,   168,   169,   170,   171,    99,
       0,     0,     0,     0,   141,     0,     0,   142,   100,     0,
     143,     0,     0,     0,   101,     0,   102,     0,   103,   144,
       0,     0,     0,     0,     0,     0,   145,     0,   146,   104,
     147,     0,     0,     0,     0,     0,     0,   148,     0,   105,
     106,     0,   107,     0,   149,   150,     0,   109,   151,   152,
     110,     0,     0,   153,   111,     0,     0,     0,   154,   155,
     156,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   157,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   158,
       0,     0,     0,   159,   160,     0,     0,     0,     0,     0,
       0,     0,   112,     0,     0,   113,     0,   161,  -515,     0,
       0,   162,     5,     6,   163,   164,   165,   166,   167,   168,
     169,   170,   171,    99,     0,     0,     0,     0,   141,     0,
       0,   142,   100,     0,   143,     0,     0,     0,   101,     0,
     102,     0,   103,   144,     0,     0,     0,     0,     0,     0,
     145,     0,   146,   104,   147,     0,     0,     0,     0,     0,
       0,   148,     0,   105,   106,     0,   107,     0,   149,   150,
       0,   109,   151,   152,   110,     0,     0,   153,   111,     0,
       0,     0,   154,   155,   156,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   157,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   158,     0,     0,     0,   159,   160,     0,
       0,     0,     0,     0,     0,     0,   112,     0,     0,   113,
    -214,   161,     0,     0,     0,   162,     5,     6,   163,   164,
     165,   166,   167,   168,   169,   170,   171,    99,     0,     0,
       0,     0,   141,     0,     0,   142,   100,     0,   143,     0,
       0,     0,   101,     0,   102,     0,   103,   144,     0,     0,
       0,     0,     0,     0,   145,     0,   146,   104,   147,     0,
       0,     0,     0,     0,     0,   148,     0,   105,   106,     0,
     107,     0,   149,   150,     0,   109,   151,   152,   110,     0,
       0,   153,   111,     0,     0,     0,   154,   155,   156,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     157,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   158,     0,     0,
       0,   159,   160,     0,     0,     0,     0,     0,     0,     0,
     112,     0,     0,   113,  -515,   161,     0,     0,     0,   162,
       5,     6,   163,   164,   165,   166,   167,   168,   169,   170,
     171,    99,     0,     0,     0,     0,   141,     0,     0,   142,
     100,     0,   143,     0,     0,     0,   101,     0,   102,     0,
     103,   144,     0,     0,     0,     0,     0,     0,   145,     0,
     146,   104,   147,     0,     0,     0,     0,     0,     0,   148,
       0,   105,   106,     0,   107,     0,   149,   150,     0,   109,
     151,   152,   110,     0,     0,   153,   111,     0,     0,     0,
     154,   155,   156,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   157,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   158,     0,     0,     0,   159,   160,     0,     0,     0,
       0,     0,     0,     0,   112,     0,  -353,   113,     0,   161,
       0,     0,     0,   162,     5,     6,   163,   164,   165,   166,
     167,   168,   169,   170,   171,    99,     0,     0,     0,     0,
     869,     0,     0,   142,   100,     0,   870,     0,     0,     0,
     101,     0,   102,     0,   103,   144,     0,     0,     0,     0,
       0,     0,   145,     0,   146,   104,   147,     0,     0,     0,
       0,     0,     0,   871,     0,   105,   106,     0,   107,     0,
     149,   150,     0,   109,   151,   152,   110,     0,     0,   872,
     873,     0,     0,     0,   874,   875,   876,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   877,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   878,     0,     0,     0,   159,
     160,     0,     0,     0,     0,     0,     0,     0,   879,   377,
       0,   880,     0,   161,     0,     0,     0,   162,     5,     6,
     163,   164,   165,   166,   167,   168,   169,   170,   171,    99,
       0,     0,     0,     0,   845,     0,     0,   142,   100,     0,
     846,     0,     0,     0,   101,     0,   102,     0,   103,   144,
       0,     0,     0,     0,     0,     0,   145,     0,   146,   104,
     147,     0,     0,     0,     0,     0,     0,   847,     0,   105,
     106,     0,   107,     0,   149,   150,     0,   109,   151,   152,
     110,     0,     0,   848,   111,     0,     0,     0,   849,   850,
     851,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   852,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   853,
       0,     0,     0,   159,   160,     0,     0,     0,     0,     0,
       0,     0,   112,   377,     0,   113,     0,   161,     0,     0,
       0,   162,     5,     6,   163,   164,   165,   166,   167,   168,
     169,   170,   171,    99,     0,     0,     0,     0,   141,     0,
       0,   142,   100,     0,   143,     0,     0,     0,   101,     0,
     102,     0,   103,   144,     0,     0,     0,     0,     0,     0,
     145,     0,   146,   104,   147,     0,     0,     0,     0,     0,
       0,   148,     0,   105,   106,     0,   107,     0,   149,   150,
       0,   109,   151,   152,   110,     0,     0,   153,   111,     0,
       0,     0,   154,   155,   156,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   157,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   158,     0,     0,     0,   159,   160,     0,
       0,     0,     0,     0,     0,     0,   112,     0,     0,   113,
       0,   161,     0,     0,     0,   162,     5,     6,   163,   164,
     165,   166,   167,   168,   169,   170,   171,    99,     0,     0,
       0,     0,   141,     0,     0,   142,   100,     0,   143,     0,
       0,     0,   101,     0,   102,     0,   103,   144,     0,     0,
       0,     0,     0,     0,   145,     0,   146,   104,   147,     0,
       0,     0,     0,     0,     0,   148,     0,   105,   106,     0,
     107,     0,   149,   826,     0,   109,   151,   152,   110,     0,
       0,   153,   111,     0,     0,     0,   154,   155,   156,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     157,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   158,     0,     0,
       0,   159,   160,     0,     0,     0,     0,     0,     0,     0,
     112,     0,     0,   113,     0,   265,     0,     0,     0,   162,
       5,     6,   163,   164,   165,   166,   167,   168,   169,   170,
     171,    99,     0,     0,     0,     0,   845,     0,     0,   142,
     100,     0,   846,     0,     0,     0,   101,     0,   102,     0,
     103,   144,     0,     0,     0,     0,     0,     0,   145,     0,
     146,   104,   147,     0,     0,     0,     0,     0,     0,   847,
       0,   105,   106,     0,   107,     0,   149,   150,     0,   109,
     151,   152,   110,     0,     0,   848,   111,     0,     0,     0,
     849,   850,   851,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   852,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   853,     0,     0,     0,   159,   160,     0,     0,     0,
       0,     0,     0,     0,   112,     0,     0,   113,     0,   161,
       0,     0,     0,   162,     5,     6,   163,   164,   165,   166,
     167,   168,   169,   170,   171,    99,     0,     0,     0,     0,
     869,     0,     0,   142,   100,     0,   870,     0,     0,     0,
     101,     0,   102,     0,   103,   144,     0,     0,     0,     0,
       0,     0,   145,     0,   146,   104,   147,     0,     0,     0,
       0,     0,     0,   871,     0,   105,   106,     0,   107,     0,
     149,   150,     0,   109,   151,   152,   110,     0,     0,   872,
     873,     0,     0,     0,   874,   875,   876,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   877,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   878,     0,     0,     0,   159,
     160,     0,     0,     0,     0,     0,     0,     0,   879,     0,
       0,   880,     0,   161,     0,     0,     0,   162,     5,     6,
     163,   164,   165,   166,   167,   168,   169,   170,   171,    99,
       0,     0,     0,     0,   845,     0,     0,   142,   100,     0,
     846,     0,     0,     0,   101,     0,   102,     0,   103,   144,
       0,     0,     0,     0,     0,     0,   145,     0,   146,   104,
     147,     0,     0,     0,     0,     0,     0,   847,     0,   105,
     106,     0,   107,     0,   149,   826,     0,   109,   151,   152,
     110,     0,     0,   848,   111,     0,     0,     0,   849,   850,
     851,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   852,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   853,
       0,     0,     0,   159,   160,     0,     0,     0,     0,     0,
       0,     0,   112,     0,     0,   113,     0,   265,     0,     0,
       0,   162,     5,     6,   163,   164,   165,   166,   167,   168,
     169,   170,   171,    99,     0,     0,     0,     0,   869,     0,
       0,   142,   100,     0,   870,     0,     0,     0,   101,     0,
     102,     0,   103,   144,     0,     0,     0,     0,     0,     0,
     145,     0,   146,   104,   147,     0,     0,     0,     0,     0,
       0,   871,     0,   105,   106,     0,   107,     0,   149,   826,
       0,   109,   151,   152,   110,     0,     0,   872,   873,     0,
       0,     0,   874,   875,   876,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   877,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   878,     0,     0,     0,   159,   160,     0,
       0,     0,     0,     0,     0,     0,   879,     0,     0,   880,
       0,   265,     0,     0,     0,   162,     5,     6,   163,   164,
     165,   166,   167,   168,   169,   170,   171,    99,     0,     0,
       0,     0,     0,     0,     0,   142,   100,     0,     0,     0,
       0,     0,   101,     0,   102,     0,   103,   144,     0,     0,
       0,     0,     0,     0,   145,     0,   146,   104,   147,     0,
       0,     0,     0,     0,     0,     0,     0,   105,   106,     0,
     107,     0,   149,   150,     0,   109,   151,   152,   110,     0,
       0,   848,   111,     0,     0,     0,   849,   850,   851,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     852,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   853,     0,     0,
       0,   159,   160,     0,     0,     0,     0,     0,     0,     0,
     112,     0,     0,   113,     0,   161,     0,     0,     0,   162,
       5,     6,   163,   164,   165,   166,   167,   168,   169,   170,
     171,    99,     0,     0,     0,     0,     0,     0,     0,   142,
     100,     0,     0,     0,     0,     0,   101,     0,   102,     0,
     103,   144,     0,     0,     0,     0,     0,     0,   145,     0,
     146,   104,   147,     0,     0,     0,     0,     0,     0,     0,
       0,   105,   106,     0,   107,     0,   149,   150,     0,   109,
     151,   152,   110,     0,     0,   872,   873,     0,     0,     0,
     874,   875,   876,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   877,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   878,     0,     0,     0,   159,   160,     0,     0,     0,
       0,     0,     0,     0,   879,     0,     0,   880,     0,   161,
       0,     0,     0,   162,     5,     6,   163,   164,   165,   166,
     167,   168,   169,   170,   171,    99,     0,     0,     0,     0,
       0,     0,     0,   142,   100,     0,     0,     0,     0,     0,
     101,     0,   102,     0,   103,   144,     0,     0,     0,     0,
       0,     0,   145,     0,   146,   104,   147,     0,     0,     0,
       0,     0,     0,     0,     0,   105,   106,     0,   107,     0,
     149,   150,     0,   109,   151,   152,   110,     0,     0,   153,
     111,     0,     0,     0,   154,   155,   156,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   157,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   159,
     160,     0,     0,     0,     0,     0,     0,     0,   112,     0,
       0,   113,     0,   161,     0,     0,     0,   162,     5,     6,
     163,   164,   165,   166,   167,   168,   169,   170,   171,    99,
       0,     0,     0,     0,     0,     0,     0,   142,   100,     0,
       0,     0,     0,     0,   101,     0,   102,     0,   103,   144,
       0,     0,     0,     0,     0,     0,   145,     0,   146,   104,
     147,     0,     0,     0,     0,     0,     0,     0,     0,   105,
     106,     0,   107,     0,   149,   150,     0,   109,   151,   152,
     110,     0,     0,   848,   111,     0,     0,     0,   849,   850,
     851,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   852,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   159,   160,     0,     0,     0,     0,     0,
       0,     0,   112,     0,     0,   113,     0,   161,     0,     0,
       0,   162,     5,     6,   163,   164,   165,   166,   167,   168,
     169,   170,   171,    99,     0,     0,     0,     0,     0,     0,
       0,   142,   100,     0,     0,     0,     0,     0,   101,     0,
     102,     0,   103,   144,     0,     0,     0,     0,     0,     0,
     145,     0,   146,   104,   147,     0,     0,     0,     0,     0,
       0,     0,     0,   105,   106,     0,   107,     0,   149,   150,
      99,   109,   151,   152,   110,     0,     0,   872,   873,   100,
       0,     0,   874,   875,   876,   101,     0,   102,     0,   103,
      11,  -173,     0,     0,     0,     0,     0,     0,     0,     0,
     104,     0,     0,     0,     0,     0,   877,     0,     0,     0,
     105,   106,     0,   107,     0,    12,   108,     0,   109,     0,
       0,   110,     0,     0,    13,   111,     0,   159,   160,     0,
       0,     0,     0,     0,     0,     0,   879,     0,     0,   880,
       0,   161,     0,     0,     0,   162,     5,     6,   163,   164,
     165,   166,   167,   168,   169,   170,   171,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    14,     0,
      15,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   112,     0,     0,   444,     0,   685,  -359,
       0,     0,    99,     5,     6,    18,    19,    20,    21,    22,
      23,   100,     0,    24,     0,     0,     0,   101,     0,   102,
       0,   103,    11,  -173,     0,     0,     0,     0,     0,     0,
       0,     0,   104,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   105,   106,     0,   107,     0,    12,   108,     0,
     109,     0,     0,   110,     0,     0,    13,   111,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,  -137,
       0,     0,     0,     0,     0,     0,  -137,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      14,     0,    15,     0,   786,     0,     0,     0,     0,     0,
       0,     0,     0,  -137,  -137,   112,     0,     0,   444,     0,
     685,     0,     0,     0,     0,     5,     6,    18,    19,    20,
      21,    22,    23,  -137,     0,    24,  -137,  -137,  -137,     0,
       0,     0,  -137,  -137,  -137,  -137,     0,  -137,  -137,  -137,
    -137,  -137,  -137,  -137,  -137,  -137,  -137,  -137,  -137,  -137,
    -137,  -137,  -137,     0,  -137,  -137,  -137,  -137,  -137,  -137,
    -137,  -137,  -137,  -137,  -137,  -137,  -137,     0,     0,  -137,
       0,  -137,     0,  -137,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   596
};

static const yytype_int16 yycheck[] =
{
       1,   143,    15,   368,    17,   191,    17,    17,     9,   319,
      64,    42,    77,   257,    15,    16,    17,    16,   414,    17,
     295,    17,    15,    17,   295,    66,   391,   365,   366,    17,
      17,    17,   148,   859,    64,    15,    28,   409,    27,   851,
      17,   104,    17,   415,    51,    64,   866,    38,   122,   421,
     422,     0,    64,    38,   128,   129,   119,   900,    40,   885,
     123,   102,     9,    66,   876,   119,     9,    38,    57,    82,
      83,   102,   892,    74,    75,    74,    77,    78,    79,     9,
       0,    82,    83,    84,   114,    86,    87,    86,    64,    82,
      83,    92,   935,    92,    95,    59,    95,   128,   129,   102,
     119,   290,    82,    83,   126,    25,     8,   119,    64,   104,
      12,   112,   113,   114,   105,    62,    63,   108,   122,    66,
     105,   128,   129,   108,    64,    27,    28,   119,    64,   102,
      50,    33,    62,    63,   105,   104,    66,   108,    64,    59,
      64,   967,    64,   119,   145,   146,   102,   148,   104,    64,
      59,   124,   153,   154,   155,    57,   157,   158,   102,   555,
     112,    25,   988,   119,   128,   129,   130,   123,    64,   133,
      64,   118,   136,   137,   102,    64,   120,   293,   114,   119,
     296,   128,   129,   103,   556,   105,    50,    64,   118,   136,
     465,    64,   120,   119,   465,   119,    64,   119,   128,   129,
     102,   121,   112,   123,   119,   321,   136,    64,   128,   129,
     130,   131,   132,   133,   134,   135,   102,   119,   138,   128,
     129,   130,    64,   119,   133,   119,   128,    64,    64,   230,
     119,   104,   124,   106,    64,    64,   109,   602,   124,    95,
     241,   124,   119,   244,   245,   104,   114,    64,   121,    64,
     123,    64,   253,   528,    64,   103,    64,   528,   114,   260,
     119,    64,   119,   264,   265,   123,   130,   131,   132,   133,
     134,   135,   136,   137,   138,    64,    64,   119,    64,   644,
     128,   129,   119,   119,   114,   124,   651,   288,   289,   290,
     119,   104,   293,   106,   295,   296,   109,   114,   241,   114,
      64,    64,   102,    64,   114,   306,   114,   306,   121,    64,
     123,   114,    64,   314,   315,   316,    64,   124,   319,   320,
     321,   322,   323,   124,   124,   114,   114,   124,   114,   330,
     331,   332,   333,   334,   335,   336,   337,   338,   339,   340,
     341,   342,   343,   344,   345,   346,   347,   124,    66,   465,
     114,   114,   295,   114,   124,   102,   102,   102,   105,   114,
     105,   477,   114,    66,   365,   366,   114,   368,     8,   370,
     371,   372,    12,   374,   102,   120,   102,   773,   124,     8,
      26,   128,   129,    12,   102,    95,   104,    27,    28,   136,
     391,   105,   120,    33,   120,    41,   114,   104,    27,    28,
     128,   129,   102,   102,    33,    60,    61,    62,   136,   119,
     123,   119,   119,   123,   128,   129,   123,    57,   104,   127,
     120,   120,   136,   424,   114,   426,   427,   428,    57,   119,
     443,    86,   445,   119,   445,   445,   437,   438,    93,   440,
     312,   442,   443,   444,   445,   444,   112,   445,   114,   445,
     443,   445,   124,   105,    58,    59,   108,   445,   445,   445,
     126,   119,   102,   443,   465,    58,    59,   124,   445,   470,
     445,   112,   124,   102,   105,   124,   477,   108,    82,   119,
      84,   482,   483,   124,   728,    89,   119,    91,   128,    82,
     119,    84,    58,    59,   127,   123,    89,   102,    91,   128,
     105,   373,   374,    60,    61,    62,   124,    60,    61,    62,
     511,   512,   513,   514,    15,   120,    82,   103,    84,   128,
     129,   107,   465,    89,   119,    91,   123,   528,   105,    86,
     119,   108,   533,    86,   533,   119,    93,    67,    68,    64,
      93,   105,   128,   129,   108,   546,   547,   548,   547,   548,
      80,   552,    26,   105,    67,    68,   108,   136,   137,   104,
     561,   562,    67,    68,   565,   566,   567,    80,   114,   570,
     571,   572,   119,   128,   129,    80,   102,   126,   104,   580,
     593,   136,   593,   593,   102,   528,   924,   925,   114,   115,
     116,   901,   593,   119,    11,   593,   961,   593,    39,   593,
       4,   602,     9,   604,    66,   593,   593,   593,   105,    16,
      17,   108,   613,    63,   615,   102,   593,   104,   593,   562,
     105,   959,   960,   108,   567,   112,   936,   114,   571,   572,
     631,   112,   119,   114,   115,   116,   136,   137,   639,   825,
     639,   642,   643,   644,   112,    65,   114,   115,   116,   650,
     651,   114,   115,   116,   526,   131,   132,   658,   659,   126,
     121,   112,   534,   114,   115,   116,   120,    74,   112,   112,
      77,   124,   685,   674,   685,   685,   136,   678,   679,    86,
     119,   867,    77,   114,   685,    92,   687,   685,    95,   685,
     879,   685,   693,   758,   695,   122,   761,   685,   685,   685,
     122,   124,   123,   845,   846,   112,   113,   114,   685,   128,
     685,   119,   375,   376,    66,   112,   659,   112,   113,   114,
      96,    97,    98,    99,   100,   101,   727,   869,   870,   239,
     119,   847,    66,   114,   735,   607,    24,   114,   145,   114,
     929,   742,   124,   744,   933,   112,   124,   114,   115,   116,
     157,   752,    42,   752,   112,   871,   757,   758,   757,   112,
     761,   112,   157,   764,   765,   112,   126,   112,   640,   114,
     115,   116,   112,   114,   114,   115,   116,   126,   126,   780,
     781,   897,   898,   120,   785,   112,   112,   903,   114,   115,
     116,   124,   122,   982,   983,   984,   124,   798,   112,   309,
     114,   115,   116,   804,    38,   124,    25,   808,   124,   122,
     112,   927,   928,  1002,  1003,  1004,  1005,   123,   119,   123,
     821,  1010,   938,   114,   105,   114,   112,   699,   114,   115,
     116,    50,   112,   112,   241,   122,   112,   244,   245,   112,
      59,   114,   115,   116,   112,   112,   114,   115,   116,   244,
     245,   126,   124,   260,   120,   126,   126,   264,   265,   112,
     112,    66,    19,   120,    29,   260,   120,   112,    95,   264,
     265,   534,   120,   124,   114,   124,   114,   114,   879,   880,
      12,   124,   112,   290,   103,   124,   105,   116,   295,   114,
     762,   114,    95,   114,   112,   290,   120,   117,   120,   306,
     112,   411,   121,   122,   123,   124,    28,   417,   124,   128,
     129,   130,   131,   132,   133,   134,   135,   114,   790,   138,
     792,   112,   794,    95,   119,    11,    39,     4,   929,    66,
      65,    11,   933,    63,    39,     4,    69,    70,    66,    72,
      73,    74,    75,    76,    77,    78,    79,    63,    81,    66,
      83,   614,    85,    65,    87,    26,    66,    90,    64,    92,
     961,    94,    95,   370,   122,    38,   122,   465,   123,   384,
      38,   124,   637,   819,   759,   370,   781,   528,   717,   723,
     717,   982,   983,   984,   651,   471,   817,   699,   401,   399,
     101,   660,   568,   258,   563,   724,   800,   873,  1006,   680,
      -1,  1002,  1003,  1004,  1005,    86,    -1,    -1,    -1,  1010,
      -1,    -1,   522,    -1,    -1,    -1,    -1,   424,    -1,   426,
     427,   428,    -1,    -1,   896,    -1,    -1,    -1,    -1,   424,
      -1,   426,   427,   428,   544,    -1,    -1,   444,   445,    -1,
      -1,    -1,    -1,    77,    -1,    -1,   709,    -1,   558,   444,
      -1,    -1,    -1,    -1,   926,    77,    -1,    -1,   465,    -1,
      -1,    -1,    -1,   470,    -1,    -1,    -1,   577,    -1,    -1,
      -1,    -1,    -1,    -1,   584,   470,    -1,    -1,   112,   113,
     114,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     112,   113,   114,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     763,    -1,    -1,    -1,   511,   512,   513,   514,    -1,   619,
      -1,    -1,    -1,    -1,    -1,    -1,   511,   512,   513,   514,
      -1,   528,    -1,   157,    -1,    -1,   533,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   157,    -1,   647,   320,    -1,
     547,   548,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   562,    -1,    -1,   565,    -1,
     567,    -1,    -1,   570,   571,   572,    -1,    -1,    -1,    -1,
     565,    -1,    -1,    -1,    -1,   570,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   847,    -1,   593,    -1,    -1,   852,
     853,    -1,    -1,   375,   376,    -1,   706,   604,   593,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   871,   604,
     244,   245,    -1,    -1,   877,   878,    -1,    -1,    -1,    -1,
      -1,    -1,   244,   245,    -1,    -1,   260,    -1,    -1,    -1,
     264,   265,   639,   896,   897,   898,    -1,   747,   260,    -1,
     903,    -1,   264,   265,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   659,    -1,    -1,    -1,   290,    -1,    -1,    -1,
      -1,   924,   925,   926,   927,   928,   776,   674,   290,    25,
      -1,   678,   679,    -1,    -1,   938,    -1,    -1,   685,   674,
      -1,    -1,    -1,   678,   679,    -1,    -1,    -1,    -1,    -1,
     685,    -1,    -1,    -1,    50,    -1,   959,   960,    -1,    -1,
     963,    69,    70,    59,    72,    73,    74,    75,    76,    77,
      78,    79,    -1,    81,    -1,    83,    -1,    85,   981,    87,
      -1,    -1,    90,    -1,    92,    -1,    94,    95,   735,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   370,    -1,    -1,    -1,
     735,    -1,    -1,    -1,    -1,   752,   102,   103,   370,   105,
     757,   758,   534,    -1,   761,    25,    -1,    -1,    -1,    -1,
      -1,    -1,   757,   758,    -1,   121,   761,   123,   124,    -1,
      -1,    -1,   128,   129,   130,   131,   132,   133,   134,   135,
      50,    -1,   138,    -1,    -1,    -1,    -1,    -1,    -1,    59,
     424,   798,   426,   427,   428,    -1,    -1,    -1,    -1,    -1,
      -1,   808,   424,   798,   426,   427,   428,    -1,    -1,    -1,
     444,    -1,    -1,   808,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   444,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   614,   103,    -1,   105,   470,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   852,    -1,    -1,   470,    -1,
      -1,   121,   122,   123,    -1,    -1,    -1,   852,   128,   129,
     130,   131,   132,   133,   134,   135,    -1,    -1,   138,    -1,
     877,    -1,   879,   880,    -1,    -1,    -1,   511,   512,   513,
     514,    -1,   877,    -1,   879,   880,    -1,    -1,    -1,   511,
     512,   513,   514,    69,    70,    -1,    72,    73,    74,    75,
      76,    77,    78,    79,    -1,    81,    -1,    83,    -1,    85,
      -1,    87,    -1,    -1,    90,    -1,    92,    -1,    94,    95,
      -1,    -1,   929,    -1,    -1,    -1,   933,   709,    -1,    -1,
      -1,   565,    -1,    -1,   929,    -1,   570,    -1,   933,    -1,
      -1,    -1,    -1,   565,    -1,    -1,    -1,    -1,   570,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   963,    -1,    -1,   593,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   963,    -1,
     604,   593,    -1,    -1,   981,   982,   983,   984,    -1,    -1,
      -1,   763,   604,    -1,    77,    -1,   981,   982,   983,   984,
      -1,    -1,    -1,    -1,    -1,  1002,  1003,  1004,  1005,    -1,
      -1,    -1,    -1,  1010,    -1,    -1,    -1,  1002,  1003,  1004,
    1005,    -1,    -1,    -1,    -1,  1010,    -1,    -1,    -1,   112,
     113,   114,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     674,    -1,    -1,    -1,   678,   679,    77,    -1,    -1,    -1,
      -1,   685,   674,    -1,    -1,    -1,   678,   679,    -1,    -1,
      -1,    -1,    -1,   685,   157,   847,    -1,    -1,    -1,    -1,
     852,   853,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   112,   113,   114,    -1,    -1,    -1,    -1,    -1,   871,
      -1,    -1,    -1,    -1,    -1,   877,   878,    -1,    -1,    -1,
      -1,   735,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   735,   896,   897,   898,    -1,    -1,   901,
     902,   903,   904,   757,   758,    -1,   157,   761,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   757,   758,    -1,    -1,   761,
      -1,    -1,   924,   925,   926,   927,   928,    -1,    -1,    -1,
      -1,   244,   245,    -1,   936,   937,   938,   939,    -1,    -1,
      -1,    -1,    -1,    -1,   798,    -1,    -1,   260,    -1,    -1,
      -1,   264,   265,    -1,   808,    -1,   798,   959,   960,    -1,
      -1,   963,   964,    25,    -1,    -1,   808,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   290,    -1,   981,
      -1,    -1,    -1,   985,    -1,    -1,    -1,    -1,    50,    -1,
      -1,    -1,    -1,   244,   245,    -1,    -1,    59,   852,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   260,
     852,    -1,    -1,   264,   265,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   877,    -1,   879,   880,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   877,    -1,   879,   880,   290,
      -1,   103,    -1,   105,    -1,    77,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   370,    -1,   121,
      -1,   123,   124,    -1,    -1,    -1,   128,   129,   130,   131,
     132,   133,   134,   135,    -1,   929,   138,    -1,    -1,   933,
     112,   113,   114,    -1,    -1,    -1,    -1,   929,    -1,    -1,
      -1,   933,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   963,
      -1,   424,    -1,   426,   427,   428,    -1,    -1,    -1,   370,
      -1,   963,    -1,    -1,    -1,   157,    -1,   981,   982,   983,
     984,   444,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   981,
     982,   983,   984,    -1,    -1,    -1,    -1,    -1,  1002,  1003,
    1004,  1005,    -1,    -1,    -1,    -1,  1010,   470,    -1,    -1,
    1002,  1003,  1004,  1005,    -1,    -1,    -1,    -1,  1010,    -1,
      -1,    -1,    -1,   424,    -1,   426,   427,   428,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   444,    -1,    -1,    -1,    -1,   511,   512,
     513,   514,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   244,   245,    -1,    -1,    -1,    -1,    -1,   470,
      -1,    -1,    -1,    -1,    -1,   322,    -1,    -1,   260,    -1,
      -1,    -1,   264,   265,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   565,    -1,    -1,    -1,    -1,   570,   290,    -1,
     511,   512,   513,   514,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,     5,    -1,    -1,   375,   376,
     593,    -1,    -1,    13,    14,    -1,    -1,    -1,    -1,    -1,
      20,   604,    22,    -1,    24,    25,    -1,    -1,    -1,    -1,
      -1,    -1,    32,    -1,    34,    35,    36,    -1,    -1,    77,
      -1,    -1,    -1,    -1,   565,    45,    46,    -1,    48,   570,
      50,    51,    -1,    53,    54,    55,    56,    -1,    -1,    59,
      60,    -1,    -1,    -1,    64,    65,    66,    -1,   370,    -1,
      -1,    -1,   593,    -1,   112,   113,   114,    -1,    -1,    -1,
      -1,    -1,    -1,   604,    -1,    -1,    -1,    -1,    88,    -1,
      -1,   674,    -1,    -1,    -1,   678,   679,    -1,    -1,    -1,
      -1,    -1,   685,    -1,    -1,   105,    -1,    -1,    -1,   109,
     110,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   118,   157,
      -1,   121,   424,   123,   426,   427,   428,   127,   128,   129,
     130,   131,   132,   133,   134,   135,   136,   137,   138,    -1,
      -1,    -1,   444,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    77,   735,   674,    -1,    -1,    -1,   678,   679,    -1,
      -1,    -1,    -1,    -1,   685,    -1,    -1,   534,   470,    -1,
      -1,    -1,    -1,    -1,   757,   758,    -1,    -1,   761,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   112,   113,   114,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   244,   245,    -1,   511,
     512,   513,   514,    -1,   735,   798,    -1,    -1,    -1,    -1,
      -1,    -1,   260,    -1,    -1,   808,   264,   265,    -1,    -1,
      -1,   157,    -1,    -1,    -1,    -1,   757,   758,    -1,    -1,
     761,    -1,    -1,    -1,    -1,    -1,    -1,   614,    -1,    -1,
      -1,    -1,   290,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   565,    -1,    -1,    -1,    -1,   570,   852,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   798,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   808,    -1,    -1,
      -1,   593,    -1,    -1,   877,    -1,   879,   880,    -1,    -1,
      -1,    -1,   604,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   244,   245,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   852,   370,    -1,   260,    -1,    -1,    -1,   264,   265,
      -1,    -1,   709,    -1,    -1,    -1,   929,    -1,    -1,    -1,
     933,    -1,    -1,    -1,    -1,    -1,   877,    -1,   879,   880,
      -1,    -1,    -1,    -1,   290,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   674,    -1,    -1,    -1,   678,   679,    -1,    -1,
     963,    -1,    -1,   685,    -1,    -1,   424,    -1,   426,   427,
     428,    -1,    -1,    -1,    -1,    -1,   763,    -1,   981,   982,
     983,   984,    -1,    -1,    -1,    -1,   444,    -1,   929,    -1,
      -1,    -1,   933,    -1,    -1,    -1,    -1,    -1,    -1,  1002,
    1003,  1004,  1005,    -1,    -1,    -1,    -1,  1010,    -1,    -1,
      -1,    -1,   470,   735,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   963,    -1,   370,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   757,   758,    -1,    -1,   761,
     981,   982,   983,   984,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   511,   512,   513,   514,    -1,    -1,    -1,
     847,  1002,  1003,  1004,  1005,   852,   853,    -1,    -1,  1010,
      -1,    -1,    -1,    -1,    -1,    -1,   798,    -1,   424,    -1,
     426,   427,   428,    77,   871,    -1,   808,    -1,    -1,    -1,
     877,   878,    -1,    -1,    -1,    -1,    -1,    -1,   444,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   565,    -1,   896,
     897,   898,   570,    -1,   901,    -1,   903,   904,   112,   113,
     114,    -1,    -1,    -1,   470,    -1,    -1,    -1,    -1,    -1,
     852,    -1,    -1,    -1,    -1,   593,    -1,   924,   925,   926,
     927,   928,    -1,    -1,    -1,    -1,   604,    -1,    -1,   936,
      -1,   938,   939,    -1,    -1,   877,    -1,   879,   880,    -1,
      -1,    -1,    -1,   157,    -1,   511,   512,   513,   514,    -1,
      -1,    -1,   959,   960,    -1,    -1,   963,   964,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   981,    -1,    -1,    -1,   985,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   929,    -1,    -1,
      -1,   933,    -1,    -1,    -1,    -1,   674,    -1,    -1,   565,
     678,   679,    -1,    -1,   570,    -1,    -1,   685,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   963,    -1,    -1,    -1,    85,    -1,   593,    -1,    -1,
     244,   245,    -1,    -1,    -1,    -1,    -1,    -1,   604,   981,
     982,   983,   984,    -1,    25,    -1,   260,    -1,    -1,    -1,
     264,   265,    77,    -1,    -1,    -1,    -1,   735,    -1,    -1,
    1002,  1003,  1004,  1005,    -1,    -1,    -1,    -1,  1010,    50,
      -1,    -1,    -1,    -1,    -1,    -1,   290,    -1,    59,   757,
     758,    -1,    -1,   761,    -1,    -1,    -1,   112,   113,   114,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   159,
     160,   161,    -1,    -1,    -1,    -1,    -1,    -1,   674,    -1,
      -1,    -1,   678,   679,    -1,    -1,    -1,    -1,    -1,   685,
     798,    -1,   103,    -1,   105,    -1,    -1,    -1,    -1,    -1,
     808,    -1,   157,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     121,    -1,   123,   124,    -1,    -1,    -1,   128,   129,   130,
     131,   132,   133,   134,   135,    -1,   370,   138,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   735,
      -1,    -1,    -1,    -1,   852,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   248,    -1,
      -1,   757,   758,    -1,   254,   761,    -1,   257,   258,   877,
      -1,   879,   880,    -1,    -1,   265,    -1,    -1,    77,    -1,
     424,    -1,   426,   427,   428,    -1,    -1,    -1,    -1,   244,
     245,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     444,    -1,   798,    -1,    -1,   260,    -1,    -1,    -1,   264,
     265,    -1,   808,   112,   113,   114,    -1,    -1,    -1,    -1,
      -1,   929,    -1,    -1,    -1,   933,   470,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   290,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   963,   852,    -1,   157,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   511,   512,   513,
     514,    -1,    -1,   981,   982,   983,   984,    -1,    -1,    -1,
      -1,   877,    -1,   879,   880,    -1,    -1,   377,    -1,    -1,
      -1,    -1,    -1,    -1,  1002,  1003,  1004,  1005,    -1,    -1,
      -1,   391,  1010,    -1,    -1,    -1,    -1,    -1,    -1,   399,
      -1,   401,    -1,    -1,    -1,   370,    -1,   407,    -1,    -1,
      -1,   565,    -1,    -1,    -1,    -1,   570,    -1,    -1,    -1,
      -1,    -1,    -1,   929,    -1,    -1,    -1,   933,    -1,    -1,
      -1,    -1,    -1,    -1,   434,   244,   245,    -1,    -1,   593,
      -1,    -1,    -1,    -1,    -1,   445,    -1,    -1,    -1,    -1,
     604,   260,    -1,    -1,    -1,   264,   265,   963,    -1,   424,
      -1,   426,   427,   428,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,     5,    -1,    -1,    -1,   981,   982,   983,   984,   444,
      14,   290,    -1,    -1,    -1,    -1,    20,    -1,    22,    -1,
      24,    -1,    26,    -1,    -1,    -1,  1002,  1003,  1004,  1005,
      -1,    35,    -1,    -1,  1010,   470,    -1,    -1,    77,    -1,
      -1,    45,    46,    -1,    48,    -1,    -1,    51,    -1,    53,
     674,    -1,    56,    -1,   678,   679,    60,    -1,    -1,    -1,
      -1,   685,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   542,   112,   113,   114,   511,   512,   513,   514,
      -1,   375,   376,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   370,    -1,   563,    -1,    -1,    -1,    -1,   568,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   735,    -1,    -1,   118,    -1,    -1,   121,   157,   123,
      -1,    -1,    -1,   593,   128,   129,    -1,    -1,    -1,    -1,
     565,    -1,   602,   757,   758,   570,    -1,   761,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   424,    -1,   426,   427,   428,
      -1,    -1,    -1,     5,    -1,    -1,    -1,    -1,   593,    -1,
      -1,    -1,    14,    -1,   634,   444,   636,   637,    20,   604,
      22,    -1,    24,    -1,   798,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    35,   808,    -1,    -1,    -1,    -1,   483,
     660,   470,    -1,    45,    46,    -1,    48,    -1,    -1,    51,
      -1,    53,    -1,    -1,    56,   244,   245,    -1,    60,    -1,
     680,    -1,    -1,    -1,    -1,    -1,    -1,   687,    -1,    -1,
      -1,   260,    -1,    -1,    -1,   264,   265,    -1,   852,    -1,
      -1,   701,   511,   512,   513,   514,    -1,    -1,    -1,   674,
     534,    -1,    -1,   678,   679,    -1,    -1,   717,    -1,    -1,
     685,   290,    -1,   877,    -1,   879,   880,    -1,   728,   729,
     112,    -1,    -1,    -1,    -1,    -1,   118,    -1,    -1,   121,
      -1,   123,    -1,    -1,    -1,    -1,   128,   129,    -1,    -1,
      -1,    -1,    -1,    -1,   136,    -1,   565,    -1,    -1,   759,
      -1,   570,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     735,    -1,    -1,    -1,    -1,   929,    -1,    -1,    -1,   933,
      -1,    -1,    -1,    -1,   593,    -1,    -1,    -1,    -1,    -1,
     614,    -1,   757,   758,    -1,   604,   761,    -1,    -1,    -1,
     800,   370,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   963,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   817,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   981,   982,   983,
     984,    -1,    -1,   798,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   808,    -1,    -1,    -1,    -1,  1002,  1003,
    1004,  1005,    -1,    -1,    -1,   424,  1010,   426,   427,   428,
      -1,    -1,     5,    -1,    -1,   674,    -1,    -1,    -1,   678,
     679,    14,    -1,    -1,    -1,   444,   685,    20,    -1,    22,
      -1,    24,    -1,    -1,    -1,   709,    -1,   852,    -1,    -1,
      -1,    -1,    35,    77,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   470,    45,    46,    -1,    48,    -1,    -1,    51,    -1,
      53,    -1,   877,    56,   879,   880,    -1,    60,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   735,    -1,   112,   113,
     114,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   763,
      -1,    -1,   511,   512,   513,   514,    -1,    -1,   757,   758,
      -1,    -1,   761,    -1,    -1,    -1,    -1,    -1,    -1,   102,
      -1,    -1,    -1,    -1,   929,    -1,    -1,    -1,   933,    -1,
      -1,    -1,    -1,   157,    -1,   118,    -1,    -1,   121,    -1,
     123,   124,    -1,    -1,    -1,   128,   129,    -1,    -1,   798,
      -1,    -1,    -1,    -1,    -1,    -1,   565,    -1,   963,   808,
      -1,   570,    -1,    -1,    -1,    -1,  1006,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   981,   982,   983,   984,
      -1,    -1,    -1,   847,   593,    -1,    -1,    -1,   852,   853,
      -1,    -1,    -1,    -1,    -1,   604,    -1,  1002,  1003,  1004,
    1005,    -1,    -1,   852,    -1,  1010,    -1,   871,    -1,    77,
      -1,    -1,    -1,   877,   878,    -1,    -1,    -1,    -1,    -1,
     244,   245,    -1,    -1,    -1,    -1,    -1,    -1,   877,    -1,
     879,   880,   896,   897,   898,    -1,   260,    -1,    -1,   903,
     264,   265,    -1,    -1,   112,   113,   114,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     924,   925,   926,   927,   928,   674,   290,    -1,    -1,   678,
     679,    77,    -1,    -1,   938,    -1,   685,    -1,    -1,    -1,
     929,    -1,    -1,    -1,   933,    -1,    -1,    -1,    -1,   157,
      -1,    -1,    -1,    -1,    -1,   959,   960,    -1,    -1,   963,
     964,    -1,    -1,    -1,    -1,    -1,   112,   113,   114,    -1,
      -1,    -1,    -1,    -1,   963,    -1,    -1,   981,    -1,    -1,
      -1,   985,    -1,    -1,    -1,    -1,   735,    -1,    -1,    -1,
      -1,    -1,   981,   982,   983,   984,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   370,    -1,   757,   758,
      -1,   157,   761,  1002,  1003,  1004,  1005,    -1,    -1,    -1,
      -1,  1010,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   244,   245,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   798,
      -1,    -1,   260,    -1,    -1,    -1,   264,   265,    -1,   808,
     424,    -1,   426,   427,   428,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     444,    -1,   290,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      25,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   244,   245,
      -1,    -1,    -1,   852,    -1,    -1,   470,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   260,    50,    -1,    -1,   264,   265,
      -1,    -1,    -1,    -1,    59,    -1,     5,    -1,   877,    -1,
     879,   880,    -1,    -1,    -1,    14,    -1,    -1,    -1,    -1,
      -1,    20,    -1,    22,   290,    24,    -1,   511,   512,   513,
     514,    -1,    -1,    -1,    -1,    -1,    35,    -1,    -1,    -1,
      -1,    -1,   370,    -1,    -1,    -1,    45,    46,   103,    48,
     105,    -1,    51,    -1,    53,    -1,    -1,    56,    -1,    -1,
     929,    60,    -1,    -1,   933,    -1,   121,    -1,   123,   124,
      -1,    77,    -1,   128,   129,   130,   131,   132,   133,   134,
     135,   565,    -1,   138,    -1,    -1,   570,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   963,    -1,   424,    -1,   426,   427,
     428,    -1,    -1,    -1,   370,    -1,   112,   113,   114,   593,
      -1,    -1,   981,   982,   983,   984,   444,    -1,    -1,   118,
     604,    -1,   121,    -1,   123,   124,    -1,    -1,    -1,   128,
     129,    -1,    -1,  1002,  1003,  1004,  1005,    -1,    -1,    -1,
      -1,  1010,   470,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   157,    -1,    -1,    -1,    -1,    -1,    -1,   424,    -1,
     426,   427,   428,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,     5,    -1,    -1,    -1,    -1,    -1,   444,    -1,
      -1,    14,    -1,   511,   512,   513,   514,    20,    -1,    22,
     674,    24,    -1,    -1,   678,   679,    -1,    -1,    -1,    -1,
      -1,   685,    35,    -1,   470,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    45,    46,    -1,    48,    -1,    -1,    51,    -1,
      53,    -1,    -1,    56,    -1,    -1,    -1,    60,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   565,   244,   245,
      -1,    -1,   570,    -1,    -1,   511,   512,   513,   514,    -1,
      -1,   735,    -1,    -1,   260,    -1,    -1,    -1,   264,   265,
      -1,    -1,    -1,    -1,    -1,   593,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   757,   758,    -1,   604,   761,    -1,    -1,
      -1,    -1,    -1,    -1,   290,   118,    -1,    -1,   121,    -1,
     123,   124,    -1,    -1,    -1,   128,   129,    -1,    -1,   565,
      -1,    -1,    -1,    -1,   570,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   798,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   808,    -1,    -1,   593,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   604,    -1,
      -1,    -1,    -1,     5,    -1,    -1,   674,    -1,    -1,    -1,
     678,   679,    14,    -1,    -1,    -1,    -1,   685,    20,    -1,
      22,    -1,    24,    -1,   370,    -1,    -1,    -1,   852,    -1,
      -1,    -1,    -1,    35,    -1,    -1,    -1,    -1,    -1,    -1,
      25,    -1,    -1,    45,    46,    -1,    48,    -1,    -1,    51,
      -1,    53,    -1,   877,    56,   879,   880,    -1,    60,    -1,
      -1,    -1,    -1,    -1,    -1,    50,    -1,   735,   674,    -1,
      -1,    -1,   678,   679,    59,    -1,    77,    -1,   424,   685,
     426,   427,   428,    -1,    -1,    -1,    -1,    -1,    -1,   757,
     758,    -1,    -1,   761,    -1,    -1,    -1,    -1,   444,    -1,
      -1,    -1,    -1,    -1,    -1,   929,    -1,    -1,    -1,   933,
      -1,   112,   113,   114,    -1,    -1,   118,    -1,   103,   121,
     105,   123,    -1,    -1,   470,    -1,   128,   129,    -1,   735,
     798,    -1,    -1,    -1,    -1,   120,   121,    -1,   123,   963,
     808,    -1,    -1,   128,   129,   130,   131,   132,   133,   134,
     135,   757,   758,   138,    -1,   761,   157,   981,   982,   983,
     984,    -1,    -1,    -1,    -1,   511,   512,   513,   514,    -1,
      -1,    -1,    -1,    -1,     5,    -1,    -1,    -1,  1002,  1003,
    1004,  1005,    -1,    14,   852,    -1,  1010,    -1,    -1,    20,
      -1,    22,   798,    24,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   808,    -1,    35,    -1,    -1,    -1,    -1,   877,
      -1,   879,   880,    -1,    45,    46,    -1,    48,    -1,   565,
      51,    -1,    53,    -1,   570,    56,    -1,    -1,    -1,    60,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   244,   245,    -1,   852,   593,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   604,   260,
      -1,   929,    -1,   264,   265,   933,    -1,    -1,    -1,    -1,
      -1,   877,    -1,   879,   880,    -1,   107,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   118,    -1,   290,
     121,    -1,   123,    -1,    -1,   963,    -1,   128,   129,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   981,   982,   983,   984,    -1,    -1,    -1,
      -1,    -1,    -1,   929,    -1,    -1,    -1,   933,   674,    -1,
      -1,    -1,   678,   679,  1002,  1003,  1004,  1005,    -1,   685,
      -1,    -1,  1010,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   963,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   370,
      -1,    -1,    -1,     5,    -1,   981,   982,   983,   984,    -1,
      -1,    -1,    14,    -1,    -1,    -1,    -1,    -1,    20,   735,
      22,    -1,    24,    -1,    -1,    -1,  1002,  1003,  1004,  1005,
      -1,    -1,    -1,    35,  1010,    -1,    -1,    -1,    -1,    -1,
      -1,   757,   758,    45,    46,   761,    48,    -1,    -1,    51,
      -1,    53,    -1,   424,    56,   426,   427,   428,    60,    -1,
       5,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    14,
      -1,    -1,    -1,   444,    -1,    20,    -1,    22,    -1,    24,
      25,    -1,   798,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      35,    -1,   808,    -1,    -1,    -1,    -1,    -1,    -1,   470,
      45,    46,    -1,    48,    -1,    50,    51,    -1,    53,    -1,
      -1,    56,    -1,    -1,    59,    60,   118,    -1,    -1,   121,
      -1,   123,    -1,    -1,    -1,    -1,   128,   129,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   852,    -1,    -1,    -1,
     511,   512,   513,   514,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   102,   103,    -1,
     105,   877,    -1,   879,   880,    78,    79,    -1,    -1,    -1,
      -1,    -1,    -1,   118,    78,    79,   121,    -1,   123,   124,
      -1,    -1,    -1,   128,   129,   130,   131,   132,   133,   134,
     135,    -1,    -1,   138,   565,    -1,    -1,    -1,    -1,   570,
     113,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   113,
      -1,    -1,    -1,   929,    -1,    -1,    -1,   933,    -1,    -1,
      -1,    -1,   593,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   604,    -1,   148,    -1,    -1,    -1,    -1,
     153,   154,   155,    -1,   157,   158,    -1,   963,    25,    -1,
      -1,    -1,    -1,   157,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   981,   982,   983,   984,    -1,
      -1,    -1,    -1,    50,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    59,    -1,    -1,    -1,  1002,  1003,  1004,  1005,
      -1,    -1,    -1,    -1,  1010,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   674,    -1,    -1,    -1,   678,   679,    -1,
      -1,    -1,    -1,    -1,   685,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   103,    -1,   105,    -1,
      -1,    -1,   112,   113,   114,    -1,    -1,    -1,    -1,    -1,
     253,    -1,    -1,   120,   121,    -1,   123,    -1,    -1,   253,
      -1,   128,   129,   130,   131,   132,   133,   134,   135,    -1,
      -1,   138,    -1,    -1,   735,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   288,   289,   157,    -1,    -1,
     293,    -1,   295,   296,   288,   289,   757,   758,    -1,    -1,
     761,   295,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   314,   315,   316,    -1,    -1,    -1,    -1,   321,    -1,
     314,   315,   316,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   798,    -1,    -1,
     343,   344,   345,   346,   347,    -1,    -1,   808,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   365,   366,    -1,    -1,    -1,    -1,   371,   372,
      -1,   374,   375,   376,   244,   245,    -1,   371,   372,    -1,
     374,   375,   376,    25,    -1,    -1,    -1,    -1,    -1,    -1,
     260,   852,    -1,    -1,   264,   265,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    50,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   877,    59,   879,   880,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   437,   438,    -1,   440,    -1,   442,
     443,   444,    -1,   437,   438,    -1,   440,    -1,    -1,    -1,
     444,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   103,   465,   105,    -1,    -1,    -1,   470,   929,    -1,
      -1,   465,   933,    25,   477,    -1,   470,    -1,   120,   121,
      -1,   123,    -1,   477,    -1,    -1,   128,   129,   130,   131,
     132,   133,   134,   135,    -1,    -1,   138,    -1,    50,    -1,
     370,    -1,   963,    -1,    -1,    -1,    -1,    59,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     981,   982,   983,   984,    -1,   528,    -1,    -1,    -1,    -1,
      -1,   534,    -1,    -1,   528,    -1,    -1,    -1,    -1,    -1,
     534,  1002,  1003,  1004,  1005,    -1,    -1,    -1,    -1,  1010,
      -1,   103,    -1,   105,   424,    -1,   426,   427,   428,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   120,   121,
     295,   123,    -1,    -1,   444,    -1,   128,   129,   130,   131,
     132,   133,   134,   135,    -1,    -1,   138,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     470,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     613,   614,   615,    -1,    -1,    -1,    -1,    -1,    -1,   613,
     614,   615,    -1,    -1,    -1,    -1,    -1,    -1,   631,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   631,    -1,   642,
     643,   511,   512,   513,   514,    -1,    -1,   650,   642,   643,
     375,   376,    -1,    -1,    -1,    -1,   650,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     693,    -1,   695,    -1,    -1,   565,    -1,    -1,    -1,   693,
     570,   695,    -1,    -1,    -1,    -1,   709,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   709,    -1,    -1,    -1,    -1,
     323,    -1,    -1,   593,   727,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   727,   604,    -1,    -1,    -1,    -1,    -1,
     465,   744,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     744,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     763,   764,   765,    -1,    -1,    -1,    -1,    -1,    -1,   763,
     764,   765,   375,   376,    -1,    -1,    -1,   780,   781,    -1,
      -1,    -1,   785,    -1,    -1,    -1,   780,   781,    -1,    -1,
      -1,   785,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   804,    -1,   528,   674,    -1,    -1,    -1,   678,   534,
     804,    -1,    -1,    -1,    -1,   685,    -1,    -1,   821,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   821,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   847,   848,   849,   850,    -1,   852,
     853,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   852,    -1,
      -1,    -1,    -1,    -1,   330,   735,    -1,    25,   871,   872,
      -1,   874,   875,    -1,   877,   878,    -1,   880,    -1,    -1,
      -1,    -1,    -1,   877,    -1,    -1,   880,   757,    -1,   614,
      -1,    -1,    50,   896,   897,   898,    -1,    -1,    -1,    -1,
     903,    59,   896,    -1,    -1,    -1,    -1,    -1,    -1,   375,
     376,    -1,    -1,    -1,    -1,    -1,   919,   920,   921,   922,
     923,   924,   925,   926,   927,   928,    -1,    -1,   798,    -1,
      -1,   534,   926,    -1,    -1,   938,    -1,    -1,   808,    -1,
      -1,    -1,    -1,    -1,    -1,   103,    -1,   105,    -1,    -1,
      -1,   954,   955,   956,   957,   958,   959,   960,    -1,    -1,
     963,    -1,   120,   121,    -1,   123,    -1,    -1,    -1,   963,
     128,   129,   130,   131,   132,   133,   134,   135,   981,    -1,
     138,    -1,   852,    -1,   709,    -1,    -1,   981,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   331,    -1,    -1,    -1,    -1,    -1,   877,    -1,   879,
     880,   614,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   763,    -1,
      -1,    -1,    -1,    -1,    -1,   375,   376,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   929,
      -1,    -1,    -1,   933,    -1,    -1,    -1,    -1,   534,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   963,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   332,    -1,    -1,    -1,    -1,   709,    -1,    -1,    -1,
      -1,   981,    -1,   983,   984,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   847,   848,   849,   850,    -1,   852,   853,    -1,
      -1,    -1,  1002,  1003,  1004,  1005,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   375,   376,   871,   872,   614,   874,
     875,    -1,   877,   878,    -1,    -1,    -1,    -1,    -1,    -1,
     763,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   896,   897,   898,    -1,    -1,   901,   902,   903,   904,
     905,   906,   907,   908,   909,   910,   911,   912,   913,   914,
     915,   916,   917,   918,   919,   920,   921,   922,   923,   924,
     925,   926,   927,   928,   534,    -1,    -1,    -1,    -1,    -1,
      -1,   936,   937,   938,   939,   940,   941,   942,   943,   944,
     945,   946,   947,   948,   949,   950,   951,   952,   953,   954,
     955,   956,   957,   958,   959,   960,    -1,    -1,   963,   964,
      -1,    -1,    -1,   709,   847,    -1,    -1,    -1,   333,   852,
     853,    -1,    -1,    -1,    -1,    -1,   981,    -1,    -1,    -1,
     985,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   871,    -1,
      -1,    -1,    -1,    -1,   877,   878,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   614,    -1,    -1,    -1,    -1,    -1,
     375,   376,    -1,   896,   897,   898,    -1,   763,   901,   902,
     903,   904,   905,   534,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   924,   925,   926,   927,   928,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   936,   937,   938,   939,   940,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   334,   335,   336,    -1,    -1,   959,   960,    -1,    -1,
     963,   964,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   981,   709,
      -1,   847,   985,   614,    -1,    -1,   852,   853,    -1,    -1,
      -1,    -1,   375,   376,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   871,    -1,    -1,    -1,    -1,
      -1,   877,   878,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     896,   897,   898,   763,    -1,   901,   902,   903,   904,   905,
     906,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   534,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   924,   925,
     926,   927,   928,   337,   338,   339,   340,   341,   342,    -1,
     936,   937,   938,   939,   940,   941,    -1,    -1,   709,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   959,   960,    -1,    -1,   963,   964,    -1,
      -1,   375,   376,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   981,    -1,   847,    -1,   985,
      -1,    -1,   852,   853,    -1,    -1,    -1,    -1,    -1,   614,
      -1,    -1,   763,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   871,    -1,    -1,    -1,    -1,    -1,   877,   878,    -1,
      -1,   534,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   896,   897,   898,    -1,
      -1,   901,   902,   903,   904,   905,   906,   907,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   924,   925,   926,   927,   928,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   936,   937,   938,   939,
     940,   941,   942,    -1,    -1,    -1,   847,    -1,    -1,    -1,
      -1,   852,   853,    -1,   709,    -1,    -1,    -1,    -1,   959,
     960,   614,    -1,   963,   964,    -1,    -1,    -1,    -1,    -1,
     871,    -1,    -1,    -1,    -1,    -1,   877,   878,    -1,    -1,
      -1,   981,    -1,    -1,    -1,   985,    -1,    -1,    -1,    -1,
     534,    -1,    -1,    -1,    -1,   896,   897,   898,    -1,    -1,
     901,   902,   903,   904,   905,   906,   907,   908,   763,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    25,    -1,   924,   925,   926,   927,   928,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   936,   937,   938,   939,   940,
     941,   942,   943,    -1,    -1,    -1,    50,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    59,   709,    -1,   959,   960,
      -1,    -1,   963,   964,    -1,    -1,    -1,    -1,    -1,    -1,
     614,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     981,    -1,    -1,    -1,   985,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   847,    -1,    -1,    -1,    -1,   852,   853,   103,
      -1,   105,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     763,    -1,    -1,    -1,    -1,    -1,   871,   121,    -1,   123,
      -1,    -1,   877,   878,   128,   129,   130,   131,   132,   133,
     134,   135,    -1,    -1,   138,    -1,    -1,    -1,    -1,    -1,
      -1,   896,   897,   898,    -1,    -1,   901,   902,   903,   904,
     905,   906,   907,   908,   909,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   614,   709,    -1,    -1,    -1,   924,
     925,   926,   927,   928,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   936,   937,   938,   939,   940,   941,   942,   943,   944,
      -1,    -1,    -1,    -1,   847,    -1,    -1,    -1,    -1,   852,
     853,    -1,    -1,    -1,   959,   960,    -1,    -1,   963,   964,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   871,   763,
      -1,    -1,    -1,    -1,   877,   878,   981,    -1,    -1,    -1,
     985,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   896,   897,   898,    -1,    -1,   901,   902,
     903,   904,   905,   906,   907,   908,   909,   910,   911,   912,
     614,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   924,   925,   926,   927,   928,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   936,   937,   938,   939,   940,   941,   942,
     943,   944,   945,   946,   947,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   847,    -1,    -1,   959,   960,   852,   853,
     963,   964,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   871,   981,    -1,
      -1,    -1,   985,   877,   878,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   896,   897,   898,    -1,    -1,   901,   902,   903,
     904,   905,   906,   907,   908,   909,   910,   911,   912,   913,
     914,   915,   916,   917,   918,    -1,    -1,    -1,    -1,    -1,
     924,   925,   926,   927,   928,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   936,   937,   938,   939,   940,   941,   942,   943,
     944,   945,   946,   947,   948,   949,   950,   951,   952,   953,
      -1,    -1,    -1,    -1,    -1,   959,   960,    -1,    -1,   963,
     964,   871,   872,    -1,   874,   875,    -1,   877,   878,   879,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   981,    -1,    -1,
      -1,   985,    -1,    -1,    -1,    -1,   896,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   927,   928,   929,
      -1,    -1,    -1,   933,    -1,    -1,   936,   937,   938,   939,
     940,   941,   942,   943,   944,   945,   946,   947,   948,   949,
     950,   951,   952,   953,   954,   955,   956,   957,   958,   959,
     960,    -1,    -1,    -1,    -1,    -1,    -1,   871,   872,    -1,
     874,   875,    -1,   877,   878,    -1,    -1,    -1,    -1,    -1,
      -1,   981,   982,   983,   984,   985,    -1,    -1,    -1,    -1,
      -1,    -1,   896,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,  1002,  1003,  1004,  1005,    -1,    -1,    -1,    -1,
    1010,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   927,   928,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   936,   937,   938,   939,   940,   941,   942,   943,
     944,   945,   946,   947,   948,   949,   950,   951,   952,   953,
     954,   955,   956,   957,   958,   959,   960,    -1,    -1,    -1,
      -1,    -1,    -1,     5,    -1,    -1,     8,    -1,    10,    -1,
      12,    13,    14,    -1,    16,    -1,    -1,   981,    20,    -1,
      22,   985,    24,    25,    26,    27,    28,    -1,    -1,    -1,
      32,    33,    34,    35,    36,    -1,    -1,    -1,    -1,    41,
      -1,    43,    -1,    45,    46,    -1,    48,    -1,    50,    51,
      -1,    53,    54,    55,    56,    57,    -1,    59,    60,    -1,
      -1,    -1,    64,    65,    66,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    88,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     102,    -1,    -1,   105,    -1,    -1,    -1,   109,   110,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   118,   119,    -1,   121,
      -1,   123,    -1,    -1,    -1,   127,   128,   129,   130,   131,
     132,   133,   134,   135,   136,   137,   138,     5,    -1,    -1,
      -1,    -1,    10,    11,    -1,    13,    14,    -1,    16,    -1,
      -1,    -1,    20,    -1,    22,    -1,    24,    25,    -1,    -1,
      -1,    -1,    -1,    -1,    32,    -1,    34,    35,    36,    -1,
      -1,    39,    -1,    -1,    -1,    43,    -1,    45,    46,    -1,
      48,    -1,    50,    51,    -1,    53,    54,    55,    56,    -1,
      -1,    59,    60,    -1,    -1,    -1,    64,    65,    66,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      88,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   105,    -1,    -1,
      -1,   109,   110,    -1,   112,    -1,   114,   115,   116,    -1,
     118,    -1,   120,   121,   122,   123,    -1,    -1,   126,   127,
     128,   129,   130,   131,   132,   133,   134,   135,   136,   137,
     138,     5,    -1,    -1,     8,    -1,    10,    -1,    12,    13,
      14,    -1,    16,    -1,    -1,    -1,    20,    -1,    22,    -1,
      24,    25,    26,    27,    28,    -1,    -1,    -1,    32,    33,
      34,    35,    36,    -1,    -1,    -1,    -1,    41,    -1,    43,
      -1,    45,    46,    -1,    48,    -1,    50,    51,    -1,    53,
      54,    55,    56,    57,    -1,    59,    60,    -1,    -1,    -1,
      64,    65,    66,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    88,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   102,    -1,
      -1,   105,    -1,    -1,    -1,   109,   110,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   118,    -1,    -1,   121,    -1,   123,
      -1,    -1,    -1,   127,   128,   129,   130,   131,   132,   133,
     134,   135,   136,   137,   138,     5,    -1,    -1,    -1,    -1,
      10,    -1,    -1,    13,    14,    -1,    16,    -1,    18,    -1,
      20,    21,    22,    -1,    24,    25,    -1,    -1,    -1,    -1,
      -1,    31,    32,    -1,    34,    35,    36,    -1,    -1,    -1,
      -1,    -1,    -1,    43,    -1,    45,    46,    -1,    48,    -1,
      50,    51,    -1,    53,    54,    55,    56,    -1,    -1,    59,
      60,    -1,    -1,    -1,    64,    65,    66,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    88,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   103,    -1,   105,    -1,    -1,    -1,   109,
     110,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   118,    -1,
     120,   121,    -1,   123,    -1,    -1,   126,   127,   128,   129,
     130,   131,   132,   133,   134,   135,   136,   137,   138,     5,
      -1,    -1,    -1,    -1,    10,    -1,    -1,    13,    14,    -1,
      16,    -1,    18,    -1,    20,    21,    22,    -1,    24,    25,
      -1,    -1,    -1,    -1,    -1,    31,    32,    -1,    34,    35,
      36,    -1,    -1,    -1,    -1,    -1,    -1,    43,    -1,    45,
      46,    -1,    48,    -1,    50,    51,    -1,    53,    54,    55,
      56,    -1,    -1,    59,    60,    -1,    -1,    -1,    64,    65,
      66,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    88,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   103,    -1,   105,
      -1,    -1,    -1,   109,   110,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   118,    -1,   120,   121,    -1,   123,    -1,    -1,
     126,   127,   128,   129,   130,   131,   132,   133,   134,   135,
     136,   137,   138,     5,    -1,    -1,    -1,    -1,    10,    -1,
      -1,    13,    14,    -1,    16,    17,    -1,    -1,    20,    -1,
      22,    -1,    24,    25,    -1,    -1,    -1,    -1,    -1,    -1,
      32,    -1,    34,    35,    36,    -1,    -1,    -1,    -1,    -1,
      -1,    43,    -1,    45,    46,    -1,    48,    -1,    50,    51,
      -1,    53,    54,    55,    56,    -1,    -1,    59,    60,    -1,
      -1,    -1,    64,    65,    66,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    88,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   103,    -1,   105,    -1,    -1,    -1,   109,   110,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   118,    -1,    -1,   121,
     122,   123,    -1,    -1,    -1,   127,   128,   129,   130,   131,
     132,   133,   134,   135,   136,   137,   138,     5,    -1,    -1,
      -1,    -1,    10,    -1,    -1,    13,    14,    -1,    16,    17,
      -1,    -1,    20,    -1,    22,    -1,    24,    25,    -1,    -1,
      -1,    -1,    -1,    -1,    32,    -1,    34,    35,    36,    -1,
      -1,    -1,    -1,    -1,    -1,    43,    -1,    45,    46,    -1,
      48,    -1,    50,    51,    -1,    53,    54,    55,    56,    -1,
      -1,    59,    60,    -1,    -1,    -1,    64,    65,    66,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      88,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   105,    -1,    -1,
      -1,   109,   110,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     118,    -1,    -1,   121,   122,   123,    -1,    -1,    -1,   127,
     128,   129,   130,   131,   132,   133,   134,   135,   136,   137,
     138,     5,    -1,    -1,    -1,    -1,    10,    -1,    -1,    13,
      14,    -1,    16,    -1,    -1,    -1,    20,    -1,    22,    -1,
      24,    25,    -1,    -1,    -1,    -1,    30,    -1,    32,    -1,
      34,    35,    36,    -1,    -1,    -1,    -1,    -1,    -1,    43,
      -1,    45,    46,    -1,    48,    -1,    50,    51,    -1,    53,
      54,    55,    56,    -1,    -1,    59,    60,    -1,    -1,    -1,
      64,    65,    66,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    88,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   105,    -1,    -1,    -1,   109,   110,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   118,   119,    -1,   121,    -1,   123,
      -1,    -1,    -1,   127,   128,   129,   130,   131,   132,   133,
     134,   135,   136,   137,   138,     5,    -1,    -1,    -1,    -1,
      10,    -1,    -1,    13,    14,    -1,    16,    17,    -1,    -1,
      20,    -1,    22,    -1,    24,    25,    -1,    -1,    -1,    -1,
      -1,    -1,    32,    -1,    34,    35,    36,    -1,    -1,    -1,
      -1,    -1,    -1,    43,    -1,    45,    46,    -1,    48,    -1,
      50,    51,    -1,    53,    54,    55,    56,    -1,    -1,    59,
      60,    -1,    -1,    -1,    64,    65,    66,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    88,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   105,    -1,    -1,    -1,   109,
     110,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   118,    -1,
      -1,   121,   122,   123,    -1,    -1,    -1,   127,   128,   129,
     130,   131,   132,   133,   134,   135,   136,   137,   138,     5,
      -1,    -1,    -1,    -1,    10,    -1,    -1,    13,    14,    -1,
      16,    -1,    -1,    -1,    20,    -1,    22,    -1,    24,    25,
      -1,    -1,    -1,    -1,    -1,    -1,    32,    -1,    34,    35,
      36,    -1,    -1,    -1,    -1,    -1,    -1,    43,    -1,    45,
      46,    -1,    48,    -1,    50,    51,    -1,    53,    54,    55,
      56,    -1,    -1,    59,    60,    -1,    -1,    -1,    64,    65,
      66,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    88,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   105,
      -1,    -1,    -1,   109,   110,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   118,    -1,    -1,   121,    -1,   123,   124,    -1,
      -1,   127,   128,   129,   130,   131,   132,   133,   134,   135,
     136,   137,   138,     5,    -1,    -1,    -1,    -1,    10,    -1,
      -1,    13,    14,    -1,    16,    -1,    -1,    -1,    20,    -1,
      22,    -1,    24,    25,    -1,    -1,    -1,    -1,    -1,    -1,
      32,    -1,    34,    35,    36,    -1,    -1,    -1,    -1,    -1,
      -1,    43,    -1,    45,    46,    -1,    48,    -1,    50,    51,
      -1,    53,    54,    55,    56,    -1,    -1,    59,    60,    -1,
      -1,    -1,    64,    65,    66,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    88,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   105,    -1,    -1,    -1,   109,   110,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   118,    -1,    -1,   121,
     122,   123,    -1,    -1,    -1,   127,   128,   129,   130,   131,
     132,   133,   134,   135,   136,   137,   138,     5,    -1,    -1,
      -1,    -1,    10,    -1,    -1,    13,    14,    -1,    16,    -1,
      -1,    -1,    20,    -1,    22,    -1,    24,    25,    -1,    -1,
      -1,    -1,    -1,    -1,    32,    -1,    34,    35,    36,    -1,
      -1,    -1,    -1,    -1,    -1,    43,    -1,    45,    46,    -1,
      48,    -1,    50,    51,    -1,    53,    54,    55,    56,    -1,
      -1,    59,    60,    -1,    -1,    -1,    64,    65,    66,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      88,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   105,    -1,    -1,
      -1,   109,   110,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     118,    -1,    -1,   121,    -1,   123,   124,    -1,    -1,   127,
     128,   129,   130,   131,   132,   133,   134,   135,   136,   137,
     138,     5,    -1,    -1,    -1,    -1,    10,    -1,    -1,    13,
      14,    -1,    16,    -1,    -1,    -1,    20,    -1,    22,    -1,
      24,    25,    -1,    -1,    -1,    -1,    -1,    -1,    32,    -1,
      34,    35,    36,    -1,    -1,    -1,    -1,    -1,    -1,    43,
      -1,    45,    46,    -1,    48,    -1,    50,    51,    -1,    53,
      54,    55,    56,    -1,    -1,    59,    60,    -1,    -1,    -1,
      64,    65,    66,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    88,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   105,    -1,    -1,    -1,   109,   110,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   118,   119,    -1,   121,    -1,   123,
      -1,    -1,    -1,   127,   128,   129,   130,   131,   132,   133,
     134,   135,   136,   137,   138,     5,    -1,    -1,    -1,    -1,
      10,    -1,    -1,    13,    14,    -1,    16,    -1,    -1,    -1,
      20,    -1,    22,    -1,    24,    25,    -1,    -1,    -1,    -1,
      -1,    -1,    32,    -1,    34,    35,    36,    -1,    -1,    -1,
      -1,    -1,    -1,    43,    -1,    45,    46,    -1,    48,    -1,
      50,    51,    -1,    53,    54,    55,    56,    -1,    -1,    59,
      60,    -1,    -1,    -1,    64,    65,    66,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    88,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   105,    -1,    -1,    -1,   109,
     110,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   118,    -1,
      -1,   121,    -1,   123,   124,    -1,    -1,   127,   128,   129,
     130,   131,   132,   133,   134,   135,   136,   137,   138,     5,
      -1,    -1,    -1,    -1,    10,    -1,    -1,    13,    14,    -1,
      16,    -1,    -1,    -1,    20,    -1,    22,    -1,    24,    25,
      -1,    -1,    -1,    -1,    -1,    -1,    32,    -1,    34,    35,
      36,    -1,    -1,    -1,    -1,    -1,    -1,    43,    -1,    45,
      46,    -1,    48,    -1,    50,    51,    -1,    53,    54,    55,
      56,    -1,    -1,    59,    60,    -1,    -1,    -1,    64,    65,
      66,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    88,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   105,
      -1,    -1,    -1,   109,   110,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   118,    -1,    -1,   121,    -1,   123,   124,    -1,
      -1,   127,   128,   129,   130,   131,   132,   133,   134,   135,
     136,   137,   138,     5,    -1,    -1,    -1,    -1,    10,    -1,
      -1,    13,    14,    -1,    16,    -1,    -1,    -1,    20,    -1,
      22,    -1,    24,    25,    -1,    -1,    -1,    -1,    -1,    -1,
      32,    -1,    34,    35,    36,    -1,    -1,    -1,    -1,    -1,
      -1,    43,    -1,    45,    46,    -1,    48,    -1,    50,    51,
      -1,    53,    54,    55,    56,    -1,    -1,    59,    60,    -1,
      -1,    -1,    64,    65,    66,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    88,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   105,    -1,    -1,    -1,   109,   110,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   118,    -1,    -1,   121,
     122,   123,    -1,    -1,    -1,   127,   128,   129,   130,   131,
     132,   133,   134,   135,   136,   137,   138,     5,    -1,    -1,
      -1,    -1,    10,    -1,    -1,    13,    14,    -1,    16,    -1,
      -1,    -1,    20,    -1,    22,    -1,    24,    25,    -1,    -1,
      -1,    -1,    -1,    -1,    32,    -1,    34,    35,    36,    -1,
      -1,    -1,    -1,    -1,    -1,    43,    -1,    45,    46,    -1,
      48,    -1,    50,    51,    -1,    53,    54,    55,    56,    -1,
      -1,    59,    60,    -1,    -1,    -1,    64,    65,    66,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      88,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   105,    -1,    -1,
      -1,   109,   110,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     118,    -1,    -1,   121,   122,   123,    -1,    -1,    -1,   127,
     128,   129,   130,   131,   132,   133,   134,   135,   136,   137,
     138,     5,    -1,    -1,    -1,    -1,    10,    -1,    -1,    13,
      14,    -1,    16,    -1,    -1,    -1,    20,    -1,    22,    -1,
      24,    25,    -1,    -1,    -1,    -1,    -1,    -1,    32,    -1,
      34,    35,    36,    -1,    -1,    -1,    -1,    -1,    -1,    43,
      -1,    45,    46,    -1,    48,    -1,    50,    51,    -1,    53,
      54,    55,    56,    -1,    -1,    59,    60,    -1,    -1,    -1,
      64,    65,    66,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    88,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   105,    -1,    -1,    -1,   109,   110,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   118,    -1,   120,   121,    -1,   123,
      -1,    -1,    -1,   127,   128,   129,   130,   131,   132,   133,
     134,   135,   136,   137,   138,     5,    -1,    -1,    -1,    -1,
      10,    -1,    -1,    13,    14,    -1,    16,    -1,    -1,    -1,
      20,    -1,    22,    -1,    24,    25,    -1,    -1,    -1,    -1,
      -1,    -1,    32,    -1,    34,    35,    36,    -1,    -1,    -1,
      -1,    -1,    -1,    43,    -1,    45,    46,    -1,    48,    -1,
      50,    51,    -1,    53,    54,    55,    56,    -1,    -1,    59,
      60,    -1,    -1,    -1,    64,    65,    66,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    88,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   105,    -1,    -1,    -1,   109,
     110,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   118,   119,
      -1,   121,    -1,   123,    -1,    -1,    -1,   127,   128,   129,
     130,   131,   132,   133,   134,   135,   136,   137,   138,     5,
      -1,    -1,    -1,    -1,    10,    -1,    -1,    13,    14,    -1,
      16,    -1,    -1,    -1,    20,    -1,    22,    -1,    24,    25,
      -1,    -1,    -1,    -1,    -1,    -1,    32,    -1,    34,    35,
      36,    -1,    -1,    -1,    -1,    -1,    -1,    43,    -1,    45,
      46,    -1,    48,    -1,    50,    51,    -1,    53,    54,    55,
      56,    -1,    -1,    59,    60,    -1,    -1,    -1,    64,    65,
      66,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    88,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   105,
      -1,    -1,    -1,   109,   110,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   118,   119,    -1,   121,    -1,   123,    -1,    -1,
      -1,   127,   128,   129,   130,   131,   132,   133,   134,   135,
     136,   137,   138,     5,    -1,    -1,    -1,    -1,    10,    -1,
      -1,    13,    14,    -1,    16,    -1,    -1,    -1,    20,    -1,
      22,    -1,    24,    25,    -1,    -1,    -1,    -1,    -1,    -1,
      32,    -1,    34,    35,    36,    -1,    -1,    -1,    -1,    -1,
      -1,    43,    -1,    45,    46,    -1,    48,    -1,    50,    51,
      -1,    53,    54,    55,    56,    -1,    -1,    59,    60,    -1,
      -1,    -1,    64,    65,    66,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    88,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   105,    -1,    -1,    -1,   109,   110,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   118,    -1,    -1,   121,
      -1,   123,    -1,    -1,    -1,   127,   128,   129,   130,   131,
     132,   133,   134,   135,   136,   137,   138,     5,    -1,    -1,
      -1,    -1,    10,    -1,    -1,    13,    14,    -1,    16,    -1,
      -1,    -1,    20,    -1,    22,    -1,    24,    25,    -1,    -1,
      -1,    -1,    -1,    -1,    32,    -1,    34,    35,    36,    -1,
      -1,    -1,    -1,    -1,    -1,    43,    -1,    45,    46,    -1,
      48,    -1,    50,    51,    -1,    53,    54,    55,    56,    -1,
      -1,    59,    60,    -1,    -1,    -1,    64,    65,    66,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      88,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   105,    -1,    -1,
      -1,   109,   110,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     118,    -1,    -1,   121,    -1,   123,    -1,    -1,    -1,   127,
     128,   129,   130,   131,   132,   133,   134,   135,   136,   137,
     138,     5,    -1,    -1,    -1,    -1,    10,    -1,    -1,    13,
      14,    -1,    16,    -1,    -1,    -1,    20,    -1,    22,    -1,
      24,    25,    -1,    -1,    -1,    -1,    -1,    -1,    32,    -1,
      34,    35,    36,    -1,    -1,    -1,    -1,    -1,    -1,    43,
      -1,    45,    46,    -1,    48,    -1,    50,    51,    -1,    53,
      54,    55,    56,    -1,    -1,    59,    60,    -1,    -1,    -1,
      64,    65,    66,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    88,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   105,    -1,    -1,    -1,   109,   110,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   118,    -1,    -1,   121,    -1,   123,
      -1,    -1,    -1,   127,   128,   129,   130,   131,   132,   133,
     134,   135,   136,   137,   138,     5,    -1,    -1,    -1,    -1,
      10,    -1,    -1,    13,    14,    -1,    16,    -1,    -1,    -1,
      20,    -1,    22,    -1,    24,    25,    -1,    -1,    -1,    -1,
      -1,    -1,    32,    -1,    34,    35,    36,    -1,    -1,    -1,
      -1,    -1,    -1,    43,    -1,    45,    46,    -1,    48,    -1,
      50,    51,    -1,    53,    54,    55,    56,    -1,    -1,    59,
      60,    -1,    -1,    -1,    64,    65,    66,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    88,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   105,    -1,    -1,    -1,   109,
     110,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   118,    -1,
      -1,   121,    -1,   123,    -1,    -1,    -1,   127,   128,   129,
     130,   131,   132,   133,   134,   135,   136,   137,   138,     5,
      -1,    -1,    -1,    -1,    10,    -1,    -1,    13,    14,    -1,
      16,    -1,    -1,    -1,    20,    -1,    22,    -1,    24,    25,
      -1,    -1,    -1,    -1,    -1,    -1,    32,    -1,    34,    35,
      36,    -1,    -1,    -1,    -1,    -1,    -1,    43,    -1,    45,
      46,    -1,    48,    -1,    50,    51,    -1,    53,    54,    55,
      56,    -1,    -1,    59,    60,    -1,    -1,    -1,    64,    65,
      66,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    88,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   105,
      -1,    -1,    -1,   109,   110,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   118,    -1,    -1,   121,    -1,   123,    -1,    -1,
      -1,   127,   128,   129,   130,   131,   132,   133,   134,   135,
     136,   137,   138,     5,    -1,    -1,    -1,    -1,    10,    -1,
      -1,    13,    14,    -1,    16,    -1,    -1,    -1,    20,    -1,
      22,    -1,    24,    25,    -1,    -1,    -1,    -1,    -1,    -1,
      32,    -1,    34,    35,    36,    -1,    -1,    -1,    -1,    -1,
      -1,    43,    -1,    45,    46,    -1,    48,    -1,    50,    51,
      -1,    53,    54,    55,    56,    -1,    -1,    59,    60,    -1,
      -1,    -1,    64,    65,    66,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    88,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   105,    -1,    -1,    -1,   109,   110,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   118,    -1,    -1,   121,
      -1,   123,    -1,    -1,    -1,   127,   128,   129,   130,   131,
     132,   133,   134,   135,   136,   137,   138,     5,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    13,    14,    -1,    -1,    -1,
      -1,    -1,    20,    -1,    22,    -1,    24,    25,    -1,    -1,
      -1,    -1,    -1,    -1,    32,    -1,    34,    35,    36,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    45,    46,    -1,
      48,    -1,    50,    51,    -1,    53,    54,    55,    56,    -1,
      -1,    59,    60,    -1,    -1,    -1,    64,    65,    66,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      88,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   105,    -1,    -1,
      -1,   109,   110,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     118,    -1,    -1,   121,    -1,   123,    -1,    -1,    -1,   127,
     128,   129,   130,   131,   132,   133,   134,   135,   136,   137,
     138,     5,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    13,
      14,    -1,    -1,    -1,    -1,    -1,    20,    -1,    22,    -1,
      24,    25,    -1,    -1,    -1,    -1,    -1,    -1,    32,    -1,
      34,    35,    36,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    45,    46,    -1,    48,    -1,    50,    51,    -1,    53,
      54,    55,    56,    -1,    -1,    59,    60,    -1,    -1,    -1,
      64,    65,    66,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    88,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   105,    -1,    -1,    -1,   109,   110,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   118,    -1,    -1,   121,    -1,   123,
      -1,    -1,    -1,   127,   128,   129,   130,   131,   132,   133,
     134,   135,   136,   137,   138,     5,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    13,    14,    -1,    -1,    -1,    -1,    -1,
      20,    -1,    22,    -1,    24,    25,    -1,    -1,    -1,    -1,
      -1,    -1,    32,    -1,    34,    35,    36,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    45,    46,    -1,    48,    -1,
      50,    51,    -1,    53,    54,    55,    56,    -1,    -1,    59,
      60,    -1,    -1,    -1,    64,    65,    66,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    88,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   109,
     110,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   118,    -1,
      -1,   121,    -1,   123,    -1,    -1,    -1,   127,   128,   129,
     130,   131,   132,   133,   134,   135,   136,   137,   138,     5,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    13,    14,    -1,
      -1,    -1,    -1,    -1,    20,    -1,    22,    -1,    24,    25,
      -1,    -1,    -1,    -1,    -1,    -1,    32,    -1,    34,    35,
      36,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    45,
      46,    -1,    48,    -1,    50,    51,    -1,    53,    54,    55,
      56,    -1,    -1,    59,    60,    -1,    -1,    -1,    64,    65,
      66,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    88,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   109,   110,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   118,    -1,    -1,   121,    -1,   123,    -1,    -1,
      -1,   127,   128,   129,   130,   131,   132,   133,   134,   135,
     136,   137,   138,     5,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    13,    14,    -1,    -1,    -1,    -1,    -1,    20,    -1,
      22,    -1,    24,    25,    -1,    -1,    -1,    -1,    -1,    -1,
      32,    -1,    34,    35,    36,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    45,    46,    -1,    48,    -1,    50,    51,
       5,    53,    54,    55,    56,    -1,    -1,    59,    60,    14,
      -1,    -1,    64,    65,    66,    20,    -1,    22,    -1,    24,
      25,    26,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      35,    -1,    -1,    -1,    -1,    -1,    88,    -1,    -1,    -1,
      45,    46,    -1,    48,    -1,    50,    51,    -1,    53,    -1,
      -1,    56,    -1,    -1,    59,    60,    -1,   109,   110,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   118,    -1,    -1,   121,
      -1,   123,    -1,    -1,    -1,   127,   128,   129,   130,   131,
     132,   133,   134,   135,   136,   137,   138,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   103,    -1,
     105,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   118,    -1,    -1,   121,    -1,   123,   124,
      -1,    -1,     5,   128,   129,   130,   131,   132,   133,   134,
     135,    14,    -1,   138,    -1,    -1,    -1,    20,    -1,    22,
      -1,    24,    25,    26,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    35,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    45,    46,    -1,    48,    -1,    50,    51,    -1,
      53,    -1,    -1,    56,    -1,    -1,    59,    60,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,     4,
      -1,    -1,    -1,    -1,    -1,    -1,    11,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     103,    -1,   105,    -1,   107,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    38,    39,   118,    -1,    -1,   121,    -1,
     123,    -1,    -1,    -1,    -1,   128,   129,   130,   131,   132,
     133,   134,   135,    58,    -1,   138,    61,    62,    63,    -1,
      -1,    -1,    67,    68,    69,    70,    -1,    72,    73,    74,
      75,    76,    77,    78,    79,    80,    81,    82,    83,    84,
      85,    86,    87,    -1,    89,    90,    91,    92,    93,    94,
      95,    96,    97,    98,    99,   100,   101,    -1,    -1,   104,
      -1,   106,    -1,   108,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   126
};

/* YYSTOS[STATE-NUM] -- The symbol kind of the accessing symbol of
   state STATE-NUM.  */
static const yytype_int16 yystos[] =
{
       0,    40,   142,   143,   144,   128,   129,   147,     0,   145,
     126,    25,    50,    59,   103,   105,   121,   123,   130,   131,
     132,   133,   134,   135,   138,   146,   147,   148,   149,   264,
     265,   266,   267,   268,   270,   271,   272,   273,   274,   283,
     286,   290,   293,   296,   356,   357,   130,   133,   147,   267,
     273,   296,   262,   264,   294,   295,   359,   262,   266,   268,
     270,   271,   272,   274,   283,   286,   287,   288,   289,   290,
     291,   292,   293,   296,   102,   104,   269,   114,   115,   116,
     136,   137,   105,   108,   104,   119,   123,   104,   136,   137,
     263,   122,   112,   361,   124,   112,   124,   262,   147,     5,
      14,    20,    22,    24,    35,    45,    46,    48,    51,    53,
      56,    60,   118,   121,   123,   147,   150,   196,   297,   298,
     301,   302,   303,   305,   306,   307,   308,   309,   310,   311,
     318,   325,   338,   339,   340,   341,   343,   345,   346,   355,
     356,    10,    13,    16,    25,    32,    34,    36,    43,    50,
      51,    54,    55,    59,    64,    65,    66,    88,   105,   109,
     110,   123,   127,   130,   131,   132,   133,   134,   135,   136,
     137,   138,   147,   160,   161,   163,   165,   166,   167,   168,
     170,   171,   172,   173,   174,   175,   176,   177,   178,   179,
     186,   187,   190,   191,   205,   221,   222,   229,   230,   234,
     248,   249,   252,   253,   299,   300,   302,   305,   306,   307,
     308,   309,   310,   311,   318,   325,   338,   339,   340,   341,
     343,   345,   355,   356,   160,   273,   273,   147,   102,   157,
     180,   275,   276,   279,   280,   281,   282,   284,   285,   359,
     147,    66,   262,   262,   123,   123,   301,   319,   119,   131,
     132,   197,   347,   123,   119,   312,   123,   119,   119,    15,
     344,   297,    17,    51,   122,   123,   160,   297,   302,   305,
     306,   307,   308,   309,   310,   311,   318,   325,   338,   339,
     340,   341,   343,   345,   355,   356,   297,   304,    95,   114,
      64,    26,   114,   184,   189,   119,   184,   356,    51,   147,
     250,   160,   183,   177,   177,   177,   180,   235,   236,   237,
     238,   160,   297,   183,   180,   180,   180,   126,    11,    39,
      38,   105,   108,     4,    96,    97,    98,    99,   100,   101,
     169,    66,    63,    65,    67,    68,    80,    58,    59,    82,
      84,    89,    91,    60,    61,    62,    86,    93,    69,    70,
      72,    73,    74,    75,    76,    77,    78,    79,    81,    83,
      85,    87,    90,    92,    94,    95,   162,    64,   104,   106,
     109,   121,   123,     8,    12,    28,    33,   119,   128,   157,
     188,   192,   193,   194,   195,   206,   240,   241,   247,   254,
     256,   119,   126,   121,   105,   136,   147,   220,   120,   112,
     277,   112,   124,   361,   264,   297,   297,   119,   180,   326,
     327,   328,   329,   160,   180,   313,   314,   315,   316,   136,
     342,   313,   326,   297,   122,   297,   122,   114,   112,   124,
     124,   160,   160,   298,   123,   128,   183,    18,    21,    25,
      31,    50,    59,   105,   121,   123,   126,   130,   131,   132,
     133,   134,   135,   138,   146,   147,   151,   152,   154,   155,
     156,   160,   186,   207,   208,   209,   356,   183,   119,   262,
      66,   112,   361,   206,   160,   182,   218,   219,   160,   181,
     210,   160,    66,   164,   166,   177,   168,   183,   167,   170,
     171,   172,   173,   174,   175,   175,   175,   176,   176,   176,
     176,   176,   176,   177,   177,   177,   177,   177,   161,   161,
       9,    62,    63,    66,   118,   147,   220,   297,   160,   160,
     185,   233,   358,   206,   160,   206,   160,   160,   180,   114,
      26,    41,   196,    27,    57,   242,   243,   244,   245,   246,
     120,   147,   180,   220,   231,   232,   158,   114,   114,   180,
     278,   282,   180,   281,   124,   180,   320,   321,   322,   323,
      42,   317,   145,   112,   361,   112,   317,   145,   112,   361,
     112,   145,   145,   297,   297,   297,   297,   360,   126,   126,
     180,   348,   349,   350,   351,   352,   354,   160,   160,   160,
     130,   133,   147,   123,   356,   126,   126,   153,   120,   151,
     160,   183,   119,   251,   114,   239,   160,   297,   238,   112,
     124,   160,   183,   112,   114,   126,   211,   212,   216,   217,
     122,   124,   147,   165,   297,   297,   297,   297,   124,   122,
     124,   112,   361,   206,   119,   207,   123,   123,   262,    30,
     160,   206,   114,   105,   180,   223,   224,   226,   227,   228,
     114,   112,   361,   122,   147,   159,   262,   262,   317,   145,
     112,   361,   147,   120,   329,   297,   147,   120,   316,   136,
     297,   120,   120,   122,   112,   361,   103,   147,   353,   124,
     112,   361,   126,   126,   126,   123,   356,   180,   120,   297,
     206,   112,   160,   160,   160,   112,   361,    66,   160,    19,
     255,   180,   120,   180,   198,   199,   200,   201,   198,    29,
     262,   206,   160,   160,   147,   220,   120,   112,   225,   361,
     160,   232,   120,    95,   147,   120,   323,    95,   119,   123,
     330,   331,   332,   333,   124,   114,   124,   297,   114,   114,
     297,   150,   180,   352,   105,   160,   213,   214,   215,   160,
     206,   254,   180,   257,   258,   260,    12,   202,   124,   112,
     361,   124,   160,   116,   114,   114,   227,   228,   205,   324,
     333,   160,   313,   180,   334,   335,   336,   337,   297,   107,
     114,   112,   361,   262,   120,   117,   107,   203,   262,   297,
     150,   201,   150,   206,   160,   160,   160,   120,   317,   124,
     112,   361,   160,   215,    28,   261,   160,   259,   114,   127,
     206,   127,   206,   206,   297,   337,   160,   112,   107,   297,
     258,    95,   204,   204,   160,   187,    51,   147,   302,   305,
     306,   307,   308,   309,   310,   311,   318,   325,   338,   339,
     340,   341,   343,   345,   355,    10,    16,    43,    59,    64,
      65,    66,    88,   105,   147,   163,   165,   167,   168,   170,
     171,   172,   173,   174,   175,   176,   177,   187,   147,    10,
      16,    43,    59,    60,    64,    65,    66,    88,   105,   118,
     121,   163,   165,   167,   168,   170,   171,   172,   173,   174,
     175,   176,   177,   178,   346,   147,    12,   184,   184,   235,
      11,    39,    38,   105,   108,     4,   169,    66,    63,    65,
      67,    68,    80,    58,    59,    82,    84,    89,    91,    60,
      61,    62,    86,    93,    95,   162,    12,   184,   184,   344,
     235,   298,    17,   122,   160,    11,    39,    38,   105,   108,
       4,   169,    66,    63,    65,    67,    68,    80,    58,    59,
      82,    84,    89,    91,    60,    61,    62,    86,    93,    95,
     162,   104,    26,    66,   164,   168,   167,   170,   171,   172,
     173,   174,   175,   175,   175,   176,   176,   176,   176,   176,
     176,    66,    64,   122,   122,   164,   168,   167,   170,   171,
     172,   173,   174,   175,   175,   175,   176,   176,   176,   176,
     176,   176,    62,    63,    66,   118,   123,   165,   165,   348,
     124
};

/* YYR1[RULE-NUM] -- Symbol kind of the left-hand side of rule RULE-NUM.  */
static const yytype_int16 yyr1[] =
{
       0,   141,   142,   143,   143,   144,   145,   145,   146,   146,
     147,   147,   148,   148,   149,   149,   150,   150,   151,   151,
     151,   151,   151,   151,   152,   152,   153,   153,   154,   155,
     156,   157,   158,   158,   159,   159,   160,   161,   161,   161,
     161,   161,   161,   162,   162,   162,   162,   162,   162,   162,
     162,   162,   162,   162,   162,   162,   162,   162,   162,   162,
     163,   163,   164,   164,   165,   165,   166,   166,   166,   166,
     167,   167,   168,   168,   169,   169,   169,   169,   169,   169,
     170,   170,   171,   171,   172,   172,   173,   173,   174,   174,
     174,   174,   175,   175,   175,   175,   175,   175,   175,   176,
     176,   176,   176,   176,   176,   177,   177,   177,   177,   178,
     178,   178,   178,   178,   178,   178,   178,   178,   178,   178,
     178,   178,   179,   179,   179,   179,   179,   179,   179,   179,
     179,   179,   179,   179,   179,   179,   179,   179,   179,   180,
     180,   181,   181,   182,   182,   183,   183,   184,   184,   185,
     185,   186,   187,   187,   188,   188,   188,   188,   188,   188,
     188,   188,   188,   189,   190,   191,   192,   192,   193,   193,
     194,   195,   195,   196,   196,   197,   197,   198,   198,   199,
     200,   200,   201,   201,   201,   202,   202,   203,   203,   204,
     204,   205,   205,   205,   205,   205,   205,   205,   205,   205,
     205,   205,   206,   207,   207,   208,   208,   209,   209,   210,
     211,   211,   211,   212,   213,   213,   214,   214,   215,   216,
     216,   217,   217,   218,   219,   219,   220,   221,   222,   223,
     223,   223,   224,   225,   225,   225,   226,   226,   227,   227,
     227,   228,   229,   230,   230,   231,   231,   232,   232,   232,
     233,   234,   234,   234,   234,   235,   235,   236,   237,   237,
     238,   239,   239,   240,   241,   241,   242,   242,   242,   242,
     243,   244,   245,   246,   247,   248,   249,   250,   250,   250,
     251,   252,   253,   254,   255,   255,   255,   256,   257,   257,
     258,   258,   259,   260,   261,   261,   262,   263,   263,   264,
     264,   265,   265,   265,   265,   265,   265,   265,   265,   265,
     265,   266,   266,   266,   266,   266,   266,   266,   266,   266,
     266,   266,   267,   267,   268,   269,   269,   270,   271,   272,
     272,   272,   272,   273,   273,   273,   273,   273,   274,   275,
     275,   276,   276,   277,   277,   278,   278,   279,   280,   280,
     281,   281,   281,   282,   283,   284,   284,   285,   286,   287,
     287,   288,   288,   289,   289,   290,   291,   291,   292,   292,
     292,   292,   292,   292,   292,   292,   292,   293,   294,   294,
     295,   296,   297,   297,   298,   298,   298,   298,   298,   298,
     298,   298,   298,   298,   298,   298,   298,   298,   298,   298,
     298,   298,   298,   298,   298,   299,   299,   299,   299,   299,
     299,   299,   299,   299,   299,   299,   299,   299,   299,   299,
     299,   299,   299,   300,   301,   302,   303,   304,   304,   305,
     306,   307,   308,   309,   310,   311,   312,   312,   313,   313,
     314,   315,   315,   316,   317,   317,   318,   319,   319,   320,
     320,   321,   322,   322,   323,   324,   324,   325,   326,   326,
     327,   328,   328,   329,   330,   330,   330,   330,   331,   332,
     333,   334,   334,   335,   336,   336,   337,   338,   339,   340,
     341,   342,   342,   342,   343,   344,   344,   345,   346,   347,
     347,   348,   348,   349,   349,   350,   351,   351,   352,   353,
     353,   353,   354,   355,   356,   356,   357,   357,   358,   358,
     359,   359,   360,   360,   361,   361
};

/* YYR2[RULE-NUM] -- Number of symbols on the right-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr2[] =
{
       0,     2,     2,     0,     1,     3,     0,     2,     1,     1,
       1,     1,     6,     4,     6,     4,     0,     1,     1,     1,
       1,     1,     1,     1,     2,     2,     0,     1,     3,     3,
       3,     4,     0,     2,     3,     1,     1,     1,     3,     3,
       3,     3,     2,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     4,     0,     3,     1,     3,     1,     3,     2,     3,
       1,     3,     1,     3,     1,     1,     1,     1,     1,     1,
       1,     3,     1,     3,     1,     3,     1,     3,     1,     3,
       3,     3,     1,     3,     3,     3,     3,     3,     3,     1,
       3,     3,     3,     3,     3,     1,     2,     2,     2,     1,
       3,     3,     3,     4,     4,     4,     4,     4,     4,     4,
       2,     2,     1,     1,     4,     4,     4,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     0,
       1,     0,     1,     0,     1,     0,     1,     0,     1,     0,
       1,     2,     0,     2,     1,     2,     1,     1,     1,     1,
       1,     2,     2,     2,     1,     1,     7,     7,     7,     7,
       2,     0,     1,     0,     2,     0,     1,     0,     1,     2,
       1,     3,     3,     3,     3,     0,     1,     4,     4,     0,
       2,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     4,     0,     1,     2,     1,     1,     2,     2,
       0,     1,     1,     3,     0,     2,     1,     3,     3,     2,
       2,     2,     3,     2,     2,     3,     1,     1,     5,     0,
       1,     1,     2,     0,     2,     1,     1,     3,     2,     4,
       4,     2,     1,     5,     3,     1,     3,     1,     3,     3,
       2,     2,     3,     4,     5,     0,     1,     2,     1,     3,
       3,     0,     2,     2,     0,     1,     1,     1,     1,     1,
       2,     3,     6,     5,     2,     4,     5,     0,     1,     1,
       0,     1,     2,     4,     0,     2,     2,     6,     0,     1,
       5,     4,     1,     3,     0,     2,     2,     0,     3,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     2,
       2,     1,     0,     1,     2,     0,     2,     1,     1,     3,
       3,     2,     2,     1,     1,     2,     2,     1,     4,     0,
       1,     2,     1,     0,     2,     0,     1,     1,     1,     3,
       4,     4,     2,     2,     4,     0,     1,     2,     3,     0,
       1,     1,     3,     2,     1,     3,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     3,     0,     1,
       2,     1,     1,     3,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     3,     1,     3,     0,     4,     4,
       4,     3,     5,     2,     5,     2,     0,     4,     0,     1,
       2,     1,     3,     5,     0,     1,     6,     0,     1,     0,
       1,     2,     1,     3,     4,     0,     1,     5,     0,     1,
       2,     1,     3,     4,     0,     1,     1,     1,     3,     3,
       2,     0,     1,     2,     1,     3,     3,     5,     6,     4,
       6,     1,     3,     2,     3,     0,     1,     6,     1,     1,
       1,     0,     1,     1,     1,     2,     1,     3,     3,     0,
       2,     2,     4,     1,     1,     3,     3,     3,     1,     3,
       1,     3,     1,     3,     0,     1
};


enum { YYENOMEM = -2 };

#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab
#define YYNOMEM         goto yyexhaustedlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                    \
  do                                                              \
    if (yychar == YYEMPTY)                                        \
      {                                                           \
        yychar = (Token);                                         \
        yylval = (Value);                                         \
        YYPOPSTACK (yylen);                                       \
        yystate = *yyssp;                                         \
        goto yybackup;                                            \
      }                                                           \
    else                                                          \
      {                                                           \
        yyerror (YY_("syntax error: cannot back up")); \
        YYERROR;                                                  \
      }                                                           \
  while (0)

/* Backward compatibility with an undocumented macro.
   Use YYerror or YYUNDEF. */
#define YYERRCODE YYUNDEF

/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)                                \
    do                                                                  \
      if (N)                                                            \
        {                                                               \
          (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;        \
          (Current).first_column = YYRHSLOC (Rhs, 1).first_column;      \
          (Current).last_line    = YYRHSLOC (Rhs, N).last_line;         \
          (Current).last_column  = YYRHSLOC (Rhs, N).last_column;       \
        }                                                               \
      else                                                              \
        {                                                               \
          (Current).first_line   = (Current).last_line   =              \
            YYRHSLOC (Rhs, 0).last_line;                                \
          (Current).first_column = (Current).last_column =              \
            YYRHSLOC (Rhs, 0).last_column;                              \
        }                                                               \
    while (0)
#endif

#define YYRHSLOC(Rhs, K) ((Rhs)[K])


/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)


/* YYLOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

# ifndef YYLOCATION_PRINT

#  if defined YY_LOCATION_PRINT

   /* Temporary convenience wrapper in case some people defined the
      undocumented and private YY_LOCATION_PRINT macros.  */
#   define YYLOCATION_PRINT(File, Loc)  YY_LOCATION_PRINT(File, *(Loc))

#  elif defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL

/* Print *YYLOCP on YYO.  Private, do not rely on its existence. */

YY_ATTRIBUTE_UNUSED
static int
yy_location_print_ (FILE *yyo, YYLTYPE const * const yylocp)
{
  int res = 0;
  int end_col = 0 != yylocp->last_column ? yylocp->last_column - 1 : 0;
  if (0 <= yylocp->first_line)
    {
      res += YYFPRINTF (yyo, "%d", yylocp->first_line);
      if (0 <= yylocp->first_column)
        res += YYFPRINTF (yyo, ".%d", yylocp->first_column);
    }
  if (0 <= yylocp->last_line)
    {
      if (yylocp->first_line < yylocp->last_line)
        {
          res += YYFPRINTF (yyo, "-%d", yylocp->last_line);
          if (0 <= end_col)
            res += YYFPRINTF (yyo, ".%d", end_col);
        }
      else if (0 <= end_col && yylocp->first_column < end_col)
        res += YYFPRINTF (yyo, "-%d", end_col);
    }
  return res;
}

#   define YYLOCATION_PRINT  yy_location_print_

    /* Temporary convenience wrapper in case some people defined the
       undocumented and private YY_LOCATION_PRINT macros.  */
#   define YY_LOCATION_PRINT(File, Loc)  YYLOCATION_PRINT(File, &(Loc))

#  else

#   define YYLOCATION_PRINT(File, Loc) ((void) 0)
    /* Temporary convenience wrapper in case some people defined the
       undocumented and private YY_LOCATION_PRINT macros.  */
#   define YY_LOCATION_PRINT  YYLOCATION_PRINT

#  endif
# endif /* !defined YYLOCATION_PRINT */


# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Kind, Value, Location); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*-----------------------------------.
| Print this symbol's value on YYO.  |
`-----------------------------------*/

static void
yy_symbol_value_print (FILE *yyo,
                       yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp)
{
  FILE *yyoutput = yyo;
  YY_USE (yyoutput);
  YY_USE (yylocationp);
  if (!yyvaluep)
    return;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/*---------------------------.
| Print this symbol on YYO.  |
`---------------------------*/

static void
yy_symbol_print (FILE *yyo,
                 yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp)
{
  YYFPRINTF (yyo, "%s %s (",
             yykind < YYNTOKENS ? "token" : "nterm", yysymbol_name (yykind));

  YYLOCATION_PRINT (yyo, yylocationp);
  YYFPRINTF (yyo, ": ");
  yy_symbol_value_print (yyo, yykind, yyvaluep, yylocationp);
  YYFPRINTF (yyo, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yy_state_t *yybottom, yy_state_t *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yy_state_t *yyssp, YYSTYPE *yyvsp, YYLTYPE *yylsp,
                 int yyrule)
{
  int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %d):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       YY_ACCESSING_SYMBOL (+yyssp[yyi + 1 - yynrhs]),
                       &yyvsp[(yyi + 1) - (yynrhs)],
                       &(yylsp[(yyi + 1) - (yynrhs)]));
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, yylsp, Rule); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args) ((void) 0)
# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


/* Context of a parse error.  */
typedef struct
{
  yy_state_t *yyssp;
  yysymbol_kind_t yytoken;
  YYLTYPE *yylloc;
} yypcontext_t;

/* Put in YYARG at most YYARGN of the expected tokens given the
   current YYCTX, and return the number of tokens stored in YYARG.  If
   YYARG is null, return the number of expected tokens (guaranteed to
   be less than YYNTOKENS).  Return YYENOMEM on memory exhaustion.
   Return 0 if there are more than YYARGN expected tokens, yet fill
   YYARG up to YYARGN. */
static int
yypcontext_expected_tokens (const yypcontext_t *yyctx,
                            yysymbol_kind_t yyarg[], int yyargn)
{
  /* Actual size of YYARG. */
  int yycount = 0;
  int yyn = yypact[+*yyctx->yyssp];
  if (!yypact_value_is_default (yyn))
    {
      /* Start YYX at -YYN if negative to avoid negative indexes in
         YYCHECK.  In other words, skip the first -YYN actions for
         this state because they are default actions.  */
      int yyxbegin = yyn < 0 ? -yyn : 0;
      /* Stay within bounds of both yycheck and yytname.  */
      int yychecklim = YYLAST - yyn + 1;
      int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
      int yyx;
      for (yyx = yyxbegin; yyx < yyxend; ++yyx)
        if (yycheck[yyx + yyn] == yyx && yyx != YYSYMBOL_YYerror
            && !yytable_value_is_error (yytable[yyx + yyn]))
          {
            if (!yyarg)
              ++yycount;
            else if (yycount == yyargn)
              return 0;
            else
              yyarg[yycount++] = YY_CAST (yysymbol_kind_t, yyx);
          }
    }
  if (yyarg && yycount == 0 && 0 < yyargn)
    yyarg[0] = YYSYMBOL_YYEMPTY;
  return yycount;
}




#ifndef yystrlen
# if defined __GLIBC__ && defined _STRING_H
#  define yystrlen(S) (YY_CAST (YYPTRDIFF_T, strlen (S)))
# else
/* Return the length of YYSTR.  */
static YYPTRDIFF_T
yystrlen (const char *yystr)
{
  YYPTRDIFF_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
# endif
#endif

#ifndef yystpcpy
# if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#  define yystpcpy stpcpy
# else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
# endif
#endif

#ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYPTRDIFF_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYPTRDIFF_T yyn = 0;
      char const *yyp = yystr;
      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            else
              goto append;

          append:
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (yyres)
    return yystpcpy (yyres, yystr) - yyres;
  else
    return yystrlen (yystr);
}
#endif


static int
yy_syntax_error_arguments (const yypcontext_t *yyctx,
                           yysymbol_kind_t yyarg[], int yyargn)
{
  /* Actual size of YYARG. */
  int yycount = 0;
  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yyctx->yytoken != YYSYMBOL_YYEMPTY)
    {
      int yyn;
      if (yyarg)
        yyarg[yycount] = yyctx->yytoken;
      ++yycount;
      yyn = yypcontext_expected_tokens (yyctx,
                                        yyarg ? yyarg + 1 : yyarg, yyargn - 1);
      if (yyn == YYENOMEM)
        return YYENOMEM;
      else
        yycount += yyn;
    }
  return yycount;
}

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return -1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return YYENOMEM if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYPTRDIFF_T *yymsg_alloc, char **yymsg,
                const yypcontext_t *yyctx)
{
  enum { YYARGS_MAX = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat: reported tokens (one for the "unexpected",
     one per "expected"). */
  yysymbol_kind_t yyarg[YYARGS_MAX];
  /* Cumulated lengths of YYARG.  */
  YYPTRDIFF_T yysize = 0;

  /* Actual size of YYARG. */
  int yycount = yy_syntax_error_arguments (yyctx, yyarg, YYARGS_MAX);
  if (yycount == YYENOMEM)
    return YYENOMEM;

  switch (yycount)
    {
#define YYCASE_(N, S)                       \
      case N:                               \
        yyformat = S;                       \
        break
    default: /* Avoid compiler warnings. */
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
#undef YYCASE_
    }

  /* Compute error message size.  Don't count the "%s"s, but reserve
     room for the terminator.  */
  yysize = yystrlen (yyformat) - 2 * yycount + 1;
  {
    int yyi;
    for (yyi = 0; yyi < yycount; ++yyi)
      {
        YYPTRDIFF_T yysize1
          = yysize + yytnamerr (YY_NULLPTR, yytname[yyarg[yyi]]);
        if (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM)
          yysize = yysize1;
        else
          return YYENOMEM;
      }
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return -1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yytname[yyarg[yyi++]]);
          yyformat += 2;
        }
      else
        {
          ++yyp;
          ++yyformat;
        }
  }
  return 0;
}


/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg,
            yysymbol_kind_t yykind, YYSTYPE *yyvaluep, YYLTYPE *yylocationp)
{
  YY_USE (yyvaluep);
  YY_USE (yylocationp);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yykind, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/* Lookahead token kind.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;
/* Location data for the lookahead symbol.  */
YYLTYPE yylloc
# if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL
  = { 1, 1, 1, 1 }
# endif
;
/* Number of syntax errors so far.  */
int yynerrs;




/*----------.
| yyparse.  |
`----------*/

int
yyparse (void)
{
    yy_state_fast_t yystate = 0;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus = 0;

    /* Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* Their size.  */
    YYPTRDIFF_T yystacksize = YYINITDEPTH;

    /* The state stack: array, bottom, top.  */
    yy_state_t yyssa[YYINITDEPTH];
    yy_state_t *yyss = yyssa;
    yy_state_t *yyssp = yyss;

    /* The semantic value stack: array, bottom, top.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs = yyvsa;
    YYSTYPE *yyvsp = yyvs;

    /* The location stack: array, bottom, top.  */
    YYLTYPE yylsa[YYINITDEPTH];
    YYLTYPE *yyls = yylsa;
    YYLTYPE *yylsp = yyls;

  int yyn;
  /* The return value of yyparse.  */
  int yyresult;
  /* Lookahead symbol kind.  */
  yysymbol_kind_t yytoken = YYSYMBOL_YYEMPTY;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;
  YYLTYPE yyloc;

  /* The locations where the error started and ended.  */
  YYLTYPE yyerror_range[3];

  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYPTRDIFF_T yymsg_alloc = sizeof yymsgbuf;

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N), yylsp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yychar = YYEMPTY; /* Cause a token to be read.  */

  yylsp[0] = yylloc;
  goto yysetstate;


/*------------------------------------------------------------.
| yynewstate -- push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;


/*--------------------------------------------------------------------.
| yysetstate -- set current state (the top of the stack) to yystate.  |
`--------------------------------------------------------------------*/
yysetstate:
  YYDPRINTF ((stderr, "Entering state %d\n", yystate));
  YY_ASSERT (0 <= yystate && yystate < YYNSTATES);
  YY_IGNORE_USELESS_CAST_BEGIN
  *yyssp = YY_CAST (yy_state_t, yystate);
  YY_IGNORE_USELESS_CAST_END
  YY_STACK_PRINT (yyss, yyssp);

  if (yyss + yystacksize - 1 <= yyssp)
#if !defined yyoverflow && !defined YYSTACK_RELOCATE
    YYNOMEM;
#else
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYPTRDIFF_T yysize = yyssp - yyss + 1;

# if defined yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        yy_state_t *yyss1 = yyss;
        YYSTYPE *yyvs1 = yyvs;
        YYLTYPE *yyls1 = yyls;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * YYSIZEOF (*yyssp),
                    &yyvs1, yysize * YYSIZEOF (*yyvsp),
                    &yyls1, yysize * YYSIZEOF (*yylsp),
                    &yystacksize);
        yyss = yyss1;
        yyvs = yyvs1;
        yyls = yyls1;
      }
# else /* defined YYSTACK_RELOCATE */
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        YYNOMEM;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yy_state_t *yyss1 = yyss;
        union yyalloc *yyptr =
          YY_CAST (union yyalloc *,
                   YYSTACK_ALLOC (YY_CAST (YYSIZE_T, YYSTACK_BYTES (yystacksize))));
        if (! yyptr)
          YYNOMEM;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
        YYSTACK_RELOCATE (yyls_alloc, yyls);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;
      yylsp = yyls + yysize - 1;

      YY_IGNORE_USELESS_CAST_BEGIN
      YYDPRINTF ((stderr, "Stack size increased to %ld\n",
                  YY_CAST (long, yystacksize)));
      YY_IGNORE_USELESS_CAST_END

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }
#endif /* !defined yyoverflow && !defined YYSTACK_RELOCATE */


  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;


/*-----------.
| yybackup.  |
`-----------*/
yybackup:
  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either empty, or end-of-input, or a valid lookahead.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token\n"));
      yychar = yylex ();
    }

  if (yychar <= YYEOF)
    {
      yychar = YYEOF;
      yytoken = YYSYMBOL_YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else if (yychar == YYerror)
    {
      /* The scanner already issued an error message, process directly
         to error recovery.  But do not keep the error token as
         lookahead, it is too special and may lead us to an endless
         loop in error recovery. */
      yychar = YYUNDEF;
      yytoken = YYSYMBOL_YYerror;
      yyerror_range[1] = yylloc;
      goto yyerrlab1;
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);
  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END
  *++yylsp = yylloc;

  /* Discard the shifted token.  */
  yychar = YYEMPTY;
  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];

  /* Default location. */
  YYLLOC_DEFAULT (yyloc, (yylsp - yylen), yylen);
  yyerror_range[1] = yyloc;
  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
  case 2: /* program: packageDecl_opt declarations_opt  */
#line 138 "parser.y"
    { ast_root = program_node((yyvsp[-1].node), (yyvsp[0].node), ZL); (yyval.node) = ast_root; }
#line 4691 "parser.tab.c"
    break;

  case 3: /* packageDecl_opt: %empty  */
#line 142 "parser.y"
                        { (yyval.node) = NULL; }
#line 4697 "parser.tab.c"
    break;

  case 4: /* packageDecl_opt: packageDecl  */
#line 143 "parser.y"
                        { (yyval.node) = (yyvsp[0].node); }
#line 4703 "parser.tab.c"
    break;

  case 5: /* packageDecl: PACKAGE identifier EOS  */
#line 148 "parser.y"
    { (yyval.node) = package_decl((yyvsp[-1].node), ZL); }
#line 4709 "parser.tab.c"
    break;

  case 6: /* declarations_opt: %empty  */
#line 152 "parser.y"
                                    { (yyval.node) = NULL; }
#line 4715 "parser.tab.c"
    break;

  case 7: /* declarations_opt: declarations_opt declaration  */
#line 153 "parser.y"
                                    { (yyval.node) = decl_list_append((yyvsp[-1].node), (yyvsp[0].node)); }
#line 4721 "parser.tab.c"
    break;

  case 10: /* identifier: NON_KEYWORD_IDENTIFIER  */
#line 162 "parser.y"
                            { (yyval.node) = identifier_node((yyvsp[0].str), ZL); }
#line 4727 "parser.tab.c"
    break;

  case 11: /* identifier: RAW_IDENTIFIER  */
#line 163 "parser.y"
                            { (yyval.node) = raw_identifier_node((yyvsp[0].str), ZL); }
#line 4733 "parser.tab.c"
    break;

  case 12: /* constDecl: patternNoTopAlt COLON type_opt COLON expression EOS  */
#line 168 "parser.y"
    { (yyval.node) = const_decl((yyvsp[-5].node), (yyvsp[-3].node), (yyvsp[-1].node), ZL); }
#line 4739 "parser.tab.c"
    break;

  case 13: /* constDecl: patternNoTopAlt COLONCOLON expression EOS  */
#line 170 "parser.y"
    { (yyval.node) = const_decl((yyvsp[-3].node), NULL, (yyvsp[-1].node), ZL); }
#line 4745 "parser.tab.c"
    break;

  case 14: /* varDecl: patternNoTopAlt COLON type_opt EQ expression EOS  */
#line 175 "parser.y"
    { (yyval.node) = var_decl((yyvsp[-5].node), (yyvsp[-3].node), (yyvsp[-1].node), ZL); }
#line 4751 "parser.tab.c"
    break;

  case 15: /* varDecl: patternNoTopAlt COLONEQ expression EOS  */
#line 177 "parser.y"
    { (yyval.node) = var_decl((yyvsp[-3].node), NULL, (yyvsp[-1].node), ZL); }
#line 4757 "parser.tab.c"
    break;

  case 16: /* type_opt: %empty  */
#line 181 "parser.y"
                { (yyval.node) = NULL; }
#line 4763 "parser.tab.c"
    break;

  case 17: /* type_opt: type_  */
#line 182 "parser.y"
                { (yyval.node) = (yyvsp[0].node); }
#line 4769 "parser.tab.c"
    break;

  case 18: /* statement: EOS  */
#line 190 "parser.y"
                               { (yyval.node) = NULL; }
#line 4775 "parser.tab.c"
    break;

  case 19: /* statement: declaration  */
#line 191 "parser.y"
                               { (yyval.node) = (yyvsp[0].node); }
#line 4781 "parser.tab.c"
    break;

  case 20: /* statement: insertStatement  */
#line 192 "parser.y"
                               { (yyval.node) = (yyvsp[0].node); }
#line 4787 "parser.tab.c"
    break;

  case 21: /* statement: deferStatement  */
#line 193 "parser.y"
                               { (yyval.node) = (yyvsp[0].node); }
#line 4793 "parser.tab.c"
    break;

  case 22: /* statement: errdeferStatement  */
#line 194 "parser.y"
                               { (yyval.node) = (yyvsp[0].node); }
#line 4799 "parser.tab.c"
    break;

  case 23: /* statement: expressionStatement  */
#line 195 "parser.y"
                               { (yyval.node) = (yyvsp[0].node); }
#line 4805 "parser.tab.c"
    break;

  case 24: /* expressionStatement: expression EOS  */
#line 199 "parser.y"
                               { (yyval.node) = (yyvsp[-1].node); }
#line 4811 "parser.tab.c"
    break;

  case 25: /* expressionStatement: attr_block_expr EOS_opt  */
#line 200 "parser.y"
                               { (yyval.node) = (yyvsp[-1].node); }
#line 4817 "parser.tab.c"
    break;

  case 26: /* EOS_opt: %empty  */
#line 204 "parser.y"
                { (yyval.node) = NULL; }
#line 4823 "parser.tab.c"
    break;

  case 27: /* EOS_opt: EOS  */
#line 205 "parser.y"
                { (yyval.node) = NULL; }
#line 4829 "parser.tab.c"
    break;

  case 28: /* insertStatement: INSERT expression EOS  */
#line 209 "parser.y"
                               { (yyval.node) = insert_stmt((yyvsp[-1].node), ZL); }
#line 4835 "parser.tab.c"
    break;

  case 29: /* deferStatement: DEFER expression EOS  */
#line 213 "parser.y"
                               { (yyval.node) = defer_stmt((yyvsp[-1].node), ZL); }
#line 4841 "parser.tab.c"
    break;

  case 30: /* errdeferStatement: ERRDEFER expression EOS  */
#line 217 "parser.y"
                               { (yyval.node) = errdefer_stmt((yyvsp[-1].node), ZL); }
#line 4847 "parser.tab.c"
    break;

  case 31: /* attribute: AT LSQUAREBRACKET attrs_opt RSQUAREBRACKET  */
#line 223 "parser.y"
    { (yyval.node) = (yyvsp[-1].node); /* list itself */ }
#line 4853 "parser.tab.c"
    break;

  case 32: /* attrs_opt: %empty  */
#line 227 "parser.y"
                           { (yyval.node) = NULL; }
#line 4859 "parser.tab.c"
    break;

  case 33: /* attrs_opt: attrs_opt attr  */
#line 228 "parser.y"
                           { (yyval.node) = attr_list_append((yyvsp[-1].node), (yyvsp[0].node)); }
#line 4865 "parser.tab.c"
    break;

  case 34: /* attr: identifier EQ literalExpression  */
#line 232 "parser.y"
                                     { (yyval.node) = attr_key_value((yyvsp[-2].node), (yyvsp[0].node), ZL); }
#line 4871 "parser.tab.c"
    break;

  case 35: /* attr: identifier  */
#line 233 "parser.y"
                                     { (yyval.node) = attr_key((yyvsp[0].node), ZL); }
#line 4877 "parser.tab.c"
    break;

  case 36: /* expression: assign_expr  */
#line 241 "parser.y"
                { (yyval.node) = (yyvsp[0].node); }
#line 4883 "parser.tab.c"
    break;

  case 37: /* assign_expr: catch_expr  */
#line 245 "parser.y"
                                                    { (yyval.node) = (yyvsp[0].node); }
#line 4889 "parser.tab.c"
    break;

  case 38: /* assign_expr: unary_expr EQ assign_expr  */
#line 246 "parser.y"
                                                    { (yyval.node) = assign_expr((yyvsp[-2].node), (yyvsp[0].node), ZL); }
#line 4895 "parser.tab.c"
    break;

  case 39: /* assign_expr: unary_expr compoundAssignOperator assign_expr  */
#line 247 "parser.y"
                                                    { (yyval.node) = compound_assign_expr((yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].op), ZL); }
#line 4901 "parser.tab.c"
    break;

  case 40: /* assign_expr: CONTINUE label_opt expression_opt  */
#line 248 "parser.y"
                                                    { (yyval.node) = continue_expr((yyvsp[-1].node), (yyvsp[0].node), ZL); }
#line 4907 "parser.tab.c"
    break;

  case 41: /* assign_expr: BREAK label_opt expression_opt  */
#line 249 "parser.y"
                                                    { (yyval.node) = break_expr((yyvsp[-1].node), (yyvsp[0].node), ZL); }
#line 4913 "parser.tab.c"
    break;

  case 42: /* assign_expr: RETURN expression_opt  */
#line 250 "parser.y"
                                                    { (yyval.node) = return_expr((yyvsp[0].node), ZL); }
#line 4919 "parser.tab.c"
    break;

  case 43: /* compoundAssignOperator: PLUSEQ  */
#line 254 "parser.y"
                   { (yyval.op) = OP_ADD_ASSIGN; }
#line 4925 "parser.tab.c"
    break;

  case 44: /* compoundAssignOperator: MINUSEQ  */
#line 255 "parser.y"
                   { (yyval.op) = OP_SUB_ASSIGN; }
#line 4931 "parser.tab.c"
    break;

  case 45: /* compoundAssignOperator: STAREQ  */
#line 256 "parser.y"
                   { (yyval.op) = OP_MUL_ASSIGN; }
#line 4937 "parser.tab.c"
    break;

  case 46: /* compoundAssignOperator: SLASHEQ  */
#line 257 "parser.y"
                   { (yyval.op) = OP_DIV_ASSIGN; }
#line 4943 "parser.tab.c"
    break;

  case 47: /* compoundAssignOperator: PERCENTEQ  */
#line 258 "parser.y"
                   { (yyval.op) = OP_MOD_ASSIGN; }
#line 4949 "parser.tab.c"
    break;

  case 48: /* compoundAssignOperator: ANDEQ  */
#line 259 "parser.y"
                   { (yyval.op) = OP_AND_ASSIGN; }
#line 4955 "parser.tab.c"
    break;

  case 49: /* compoundAssignOperator: OREQ  */
#line 260 "parser.y"
                   { (yyval.op) = OP_OR_ASSIGN; }
#line 4961 "parser.tab.c"
    break;

  case 50: /* compoundAssignOperator: CARETEQ  */
#line 261 "parser.y"
                   { (yyval.op) = OP_XOR_ASSIGN; }
#line 4967 "parser.tab.c"
    break;

  case 51: /* compoundAssignOperator: SHLEQ  */
#line 262 "parser.y"
                   { (yyval.op) = OP_SHL_ASSIGN; }
#line 4973 "parser.tab.c"
    break;

  case 52: /* compoundAssignOperator: SHREQ  */
#line 263 "parser.y"
                   { (yyval.op) = OP_SHR_ASSIGN; }
#line 4979 "parser.tab.c"
    break;

  case 53: /* compoundAssignOperator: PLUSPIPEEQ  */
#line 264 "parser.y"
                   { (yyval.op) = OP_ADD_SAT_ASSIGN; }
#line 4985 "parser.tab.c"
    break;

  case 54: /* compoundAssignOperator: MINUSPIPEEQ  */
#line 265 "parser.y"
                   { (yyval.op) = OP_SUB_SAT_ASSIGN; }
#line 4991 "parser.tab.c"
    break;

  case 55: /* compoundAssignOperator: STARPIPEEQ  */
#line 266 "parser.y"
                   { (yyval.op) = OP_MUL_SAT_ASSIGN; }
#line 4997 "parser.tab.c"
    break;

  case 56: /* compoundAssignOperator: SHLPIPEEQ  */
#line 267 "parser.y"
                   { (yyval.op) = OP_SHL_SAT_ASSIGN; }
#line 5003 "parser.tab.c"
    break;

  case 57: /* compoundAssignOperator: PLUSPERCENTEQ  */
#line 268 "parser.y"
                   { (yyval.op) = OP_ADD_WRAP_ASSIGN; }
#line 5009 "parser.tab.c"
    break;

  case 58: /* compoundAssignOperator: MINUSPERCENTEQ  */
#line 269 "parser.y"
                   { (yyval.op) = OP_SUB_WRAP_ASSIGN; }
#line 5015 "parser.tab.c"
    break;

  case 59: /* compoundAssignOperator: STARPERCENTEQ  */
#line 270 "parser.y"
                   { (yyval.op) = OP_MUL_WRAP_ASSIGN; }
#line 5021 "parser.tab.c"
    break;

  case 60: /* catch_expr: orelse_expr  */
#line 274 "parser.y"
                                                          { (yyval.node) = (yyvsp[0].node); }
#line 5027 "parser.tab.c"
    break;

  case 61: /* catch_expr: catch_expr CATCH catchBinder_opt orelse_expr  */
#line 275 "parser.y"
                                                          { (yyval.node) = catch_expr((yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[0].node), ZL); }
#line 5033 "parser.tab.c"
    break;

  case 62: /* catchBinder_opt: %empty  */
#line 279 "parser.y"
                                     { (yyval.node) = NULL; }
#line 5039 "parser.tab.c"
    break;

  case 63: /* catchBinder_opt: B_OR identifier B_OR  */
#line 280 "parser.y"
                                     { (yyval.node) = (yyvsp[-1].node); }
#line 5045 "parser.tab.c"
    break;

  case 64: /* orelse_expr: range_expr  */
#line 284 "parser.y"
                                       { (yyval.node) = (yyvsp[0].node); }
#line 5051 "parser.tab.c"
    break;

  case 65: /* orelse_expr: orelse_expr ORELSE range_expr  */
#line 285 "parser.y"
                                       { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_ORELSE, ZL); }
#line 5057 "parser.tab.c"
    break;

  case 66: /* range_expr: or_expr  */
#line 289 "parser.y"
                                       { (yyval.node) = (yyvsp[0].node); }
#line 5063 "parser.tab.c"
    break;

  case 67: /* range_expr: or_expr DOTDOT expression_opt  */
#line 290 "parser.y"
                                       { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_DOTDOT, ZL); }
#line 5069 "parser.tab.c"
    break;

  case 68: /* range_expr: DOTDOT expression_opt  */
#line 291 "parser.y"
                                       { (yyval.node) = unary_expr((yyvsp[0].node), OP_DOTDOT, ZL); }
#line 5075 "parser.tab.c"
    break;

  case 69: /* range_expr: or_expr DOTDOTEQ or_expr  */
#line 292 "parser.y"
                                       { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_DOTDOTEQ, ZL); }
#line 5081 "parser.tab.c"
    break;

  case 70: /* or_expr: and_expr  */
#line 296 "parser.y"
                                 { (yyval.node) = (yyvsp[0].node); }
#line 5087 "parser.tab.c"
    break;

  case 71: /* or_expr: or_expr OR and_expr  */
#line 297 "parser.y"
                                 { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_OR, ZL); }
#line 5093 "parser.tab.c"
    break;

  case 72: /* and_expr: cmp_expr  */
#line 301 "parser.y"
                                 { (yyval.node) = (yyvsp[0].node); }
#line 5099 "parser.tab.c"
    break;

  case 73: /* and_expr: and_expr AND cmp_expr  */
#line 302 "parser.y"
                                 { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_AND, ZL); }
#line 5105 "parser.tab.c"
    break;

  case 74: /* comparisonOperator: EQEQ  */
#line 306 "parser.y"
           { (yyval.op) = OP_EQ; }
#line 5111 "parser.tab.c"
    break;

  case 75: /* comparisonOperator: NE  */
#line 307 "parser.y"
           { (yyval.op) = OP_NEQ; }
#line 5117 "parser.tab.c"
    break;

  case 76: /* comparisonOperator: GT  */
#line 308 "parser.y"
           { (yyval.op) = OP_GT; }
#line 5123 "parser.tab.c"
    break;

  case 77: /* comparisonOperator: LT  */
#line 309 "parser.y"
           { (yyval.op) = OP_LT; }
#line 5129 "parser.tab.c"
    break;

  case 78: /* comparisonOperator: GE  */
#line 310 "parser.y"
           { (yyval.op) = OP_GTE; }
#line 5135 "parser.tab.c"
    break;

  case 79: /* comparisonOperator: LE  */
#line 311 "parser.y"
           { (yyval.op) = OP_LTE; }
#line 5141 "parser.tab.c"
    break;

  case 80: /* cmp_expr: bitor_expr  */
#line 315 "parser.y"
                                                { (yyval.node) = (yyvsp[0].node); }
#line 5147 "parser.tab.c"
    break;

  case 81: /* cmp_expr: cmp_expr comparisonOperator bitor_expr  */
#line 316 "parser.y"
                                                 { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].op), ZL); }
#line 5153 "parser.tab.c"
    break;

  case 82: /* bitor_expr: xor_expr  */
#line 320 "parser.y"
                                { (yyval.node) = (yyvsp[0].node); }
#line 5159 "parser.tab.c"
    break;

  case 83: /* bitor_expr: bitor_expr B_OR xor_expr  */
#line 321 "parser.y"
                                { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_BOR, ZL); }
#line 5165 "parser.tab.c"
    break;

  case 84: /* xor_expr: bitand_expr  */
#line 325 "parser.y"
                                 { (yyval.node) = (yyvsp[0].node); }
#line 5171 "parser.tab.c"
    break;

  case 85: /* xor_expr: xor_expr CARET bitand_expr  */
#line 326 "parser.y"
                                 { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_BXOR, ZL); }
#line 5177 "parser.tab.c"
    break;

  case 86: /* bitand_expr: shift_expr  */
#line 330 "parser.y"
                                  { (yyval.node) = (yyvsp[0].node); }
#line 5183 "parser.tab.c"
    break;

  case 87: /* bitand_expr: bitand_expr B_AND shift_expr  */
#line 331 "parser.y"
                                  { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_BAND, ZL); }
#line 5189 "parser.tab.c"
    break;

  case 88: /* shift_expr: add_expr  */
#line 335 "parser.y"
                                   { (yyval.node) = (yyvsp[0].node); }
#line 5195 "parser.tab.c"
    break;

  case 89: /* shift_expr: shift_expr SHL add_expr  */
#line 336 "parser.y"
                                   { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_SHL, ZL); }
#line 5201 "parser.tab.c"
    break;

  case 90: /* shift_expr: shift_expr SHR add_expr  */
#line 337 "parser.y"
                                   { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_SHR, ZL); }
#line 5207 "parser.tab.c"
    break;

  case 91: /* shift_expr: shift_expr SHLPIPE add_expr  */
#line 338 "parser.y"
                                   { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_SHL_SAT, ZL); }
#line 5213 "parser.tab.c"
    break;

  case 92: /* add_expr: mul_expr  */
#line 342 "parser.y"
                                       { (yyval.node) = (yyvsp[0].node); }
#line 5219 "parser.tab.c"
    break;

  case 93: /* add_expr: add_expr PLUS mul_expr  */
#line 343 "parser.y"
                                       { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_ADD, ZL); }
#line 5225 "parser.tab.c"
    break;

  case 94: /* add_expr: add_expr MINUS mul_expr  */
#line 344 "parser.y"
                                       { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_SUB, ZL); }
#line 5231 "parser.tab.c"
    break;

  case 95: /* add_expr: add_expr PLUSPIPE mul_expr  */
#line 345 "parser.y"
                                       { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_ADD_SAT, ZL); }
#line 5237 "parser.tab.c"
    break;

  case 96: /* add_expr: add_expr MINUSPIPE mul_expr  */
#line 346 "parser.y"
                                       { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_SUB_SAT, ZL); }
#line 5243 "parser.tab.c"
    break;

  case 97: /* add_expr: add_expr PLUSPERCENT mul_expr  */
#line 347 "parser.y"
                                       { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_ADD_WRAP, ZL); }
#line 5249 "parser.tab.c"
    break;

  case 98: /* add_expr: add_expr MINUSPERCENT mul_expr  */
#line 348 "parser.y"
                                       { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_SUB_WRAP, ZL); }
#line 5255 "parser.tab.c"
    break;

  case 99: /* mul_expr: unary_expr  */
#line 352 "parser.y"
                                      { (yyval.node) = (yyvsp[0].node); }
#line 5261 "parser.tab.c"
    break;

  case 100: /* mul_expr: mul_expr STAR unary_expr  */
#line 353 "parser.y"
                                      { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_MUL, ZL); }
#line 5267 "parser.tab.c"
    break;

  case 101: /* mul_expr: mul_expr SLASH unary_expr  */
#line 354 "parser.y"
                                      { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_DIV, ZL); }
#line 5273 "parser.tab.c"
    break;

  case 102: /* mul_expr: mul_expr PERCENT unary_expr  */
#line 355 "parser.y"
                                      { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_MOD, ZL); }
#line 5279 "parser.tab.c"
    break;

  case 103: /* mul_expr: mul_expr STARPIPE unary_expr  */
#line 356 "parser.y"
                                      { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_MUL_SAT, ZL); }
#line 5285 "parser.tab.c"
    break;

  case 104: /* mul_expr: mul_expr STARPERCENT unary_expr  */
#line 357 "parser.y"
                                      { (yyval.node) = binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_MUL_WRAP, ZL); }
#line 5291 "parser.tab.c"
    break;

  case 105: /* unary_expr: postfix_expr  */
#line 361 "parser.y"
                                               { (yyval.node) = (yyvsp[0].node); }
#line 5297 "parser.tab.c"
    break;

  case 106: /* unary_expr: B_AND unary_expr  */
#line 362 "parser.y"
                                               { (yyval.node) = unary_expr((yyvsp[0].node), OP_ADDR, ZL); }
#line 5303 "parser.tab.c"
    break;

  case 107: /* unary_expr: MINUS unary_expr  */
#line 363 "parser.y"
                                               { (yyval.node) = unary_expr((yyvsp[0].node), OP_NEG, ZL); }
#line 5309 "parser.tab.c"
    break;

  case 108: /* unary_expr: BANG unary_expr  */
#line 364 "parser.y"
                                               { (yyval.node) = unary_expr((yyvsp[0].node), OP_NOT, ZL); }
#line 5315 "parser.tab.c"
    break;

  case 109: /* postfix_expr: primary_expr  */
#line 368 "parser.y"
                                            { (yyval.node) = (yyvsp[0].node); }
#line 5321 "parser.tab.c"
    break;

  case 110: /* postfix_expr: postfix_expr DOT identifier  */
#line 369 "parser.y"
                                            { (yyval.node) = field_access_expr((yyvsp[-2].node), (yyvsp[0].node), ZL); }
#line 5327 "parser.tab.c"
    break;

  case 111: /* postfix_expr: postfix_expr DOT tupleIndex  */
#line 370 "parser.y"
                                            { (yyval.node) = tuple_index_expr((yyvsp[-2].node), (yyvsp[0].node), ZL); }
#line 5333 "parser.tab.c"
    break;

  case 112: /* postfix_expr: postfix_expr DOT AWAIT  */
#line 371 "parser.y"
                                            { (yyval.node) = await_expr((yyvsp[-2].node), ZL); }
#line 5339 "parser.tab.c"
    break;

  case 113: /* postfix_expr: postfix_expr DOTLPAREN type_ RPAREN  */
#line 372 "parser.y"
                                            { (yyval.node) = type_cast_expr((yyvsp[-3].node), (yyvsp[-1].node), ZL); }
#line 5345 "parser.tab.c"
    break;

  case 114: /* postfix_expr: postfix_expr DOT CARET type_  */
#line 373 "parser.y"
                                            { (yyval.node) = type_cast_expr((yyvsp[-3].node), (yyvsp[0].node), ZL); }
#line 5351 "parser.tab.c"
    break;

  case 115: /* postfix_expr: postfix_expr DOT B_OR type_  */
#line 374 "parser.y"
                                            { (yyval.node) = type_cast_expr((yyvsp[-3].node), (yyvsp[0].node), ZL); }
#line 5357 "parser.tab.c"
    break;

  case 116: /* postfix_expr: postfix_expr DOT PERCENT type_  */
#line 375 "parser.y"
                                            { (yyval.node) = type_cast_expr((yyvsp[-3].node), (yyvsp[0].node), ZL); }
#line 5363 "parser.tab.c"
    break;

  case 117: /* postfix_expr: postfix_expr DOT QUESTION type_  */
#line 376 "parser.y"
                                            { (yyval.node) = type_cast_expr((yyvsp[-3].node), (yyvsp[0].node), ZL); }
#line 5369 "parser.tab.c"
    break;

  case 118: /* postfix_expr: postfix_expr LPAREN callParams_opt RPAREN  */
#line 378 "parser.y"
    { (yyval.node) = call_expr((yyvsp[-3].node), (yyvsp[-1].node), ZL); }
#line 5375 "parser.tab.c"
    break;

  case 119: /* postfix_expr: postfix_expr LSQUAREBRACKET expression RSQUAREBRACKET  */
#line 380 "parser.y"
    { (yyval.node) = index_expr((yyvsp[-3].node), (yyvsp[-1].node), ZL); }
#line 5381 "parser.tab.c"
    break;

  case 120: /* postfix_expr: postfix_expr DOTSTAR  */
#line 381 "parser.y"
                                            { (yyval.node) = deref_expr((yyvsp[-1].node), ZL); }
#line 5387 "parser.tab.c"
    break;

  case 121: /* postfix_expr: postfix_expr BANG  */
#line 383 "parser.y"
    { (yyval.node) = errorprop_expr((yyvsp[-1].node), ZL); }
#line 5393 "parser.tab.c"
    break;

  case 122: /* primary_expr: literalExpression  */
#line 387 "parser.y"
                                               { (yyval.node) = (yyvsp[0].node); }
#line 5399 "parser.tab.c"
    break;

  case 123: /* primary_expr: identifier  */
#line 388 "parser.y"
                                               { (yyval.node) = identifier_expr((yyvsp[0].node)->data.identifier.name, ZL); }
#line 5405 "parser.tab.c"
    break;

  case 124: /* primary_expr: LPAREN attribute_opt expression RPAREN  */
#line 389 "parser.y"
                                               { (yyval.node) = grouped_expr((yyvsp[-2].node), (yyvsp[-1].node), ZL); }
#line 5411 "parser.tab.c"
    break;

  case 125: /* primary_expr: DOTLSQUAREBRACKET attribute_opt collectionBody_opt RSQUAREBRACKET  */
#line 391 "parser.y"
    { (yyval.node) = array_literal((yyvsp[-2].node), (yyvsp[-1].node), ZL); }
#line 5417 "parser.tab.c"
    break;

  case 126: /* primary_expr: DOTLPAREN attribute_opt tupleElements_opt RPAREN  */
#line 393 "parser.y"
    { (yyval.node) = tuple_literal((yyvsp[-2].node), (yyvsp[-1].node), ZL); }
#line 5423 "parser.tab.c"
    break;

  case 127: /* primary_expr: structExpression  */
#line 394 "parser.y"
                                               { (yyval.node) = (yyvsp[0].node); }
#line 5429 "parser.tab.c"
    break;

  case 128: /* primary_expr: enumerationVariantExpression  */
#line 395 "parser.y"
                                               { (yyval.node) = (yyvsp[0].node); }
#line 5435 "parser.tab.c"
    break;

  case 129: /* primary_expr: closureExpression  */
#line 396 "parser.y"
                                               { (yyval.node) = (yyvsp[0].node); }
#line 5441 "parser.tab.c"
    break;

  case 130: /* primary_expr: codeExpression  */
#line 397 "parser.y"
                                               { (yyval.node) = (yyvsp[0].node); }
#line 5447 "parser.tab.c"
    break;

  case 131: /* primary_expr: mlirExpression  */
#line 398 "parser.y"
                                               { (yyval.node) = (yyvsp[0].node); }
#line 5453 "parser.tab.c"
    break;

  case 132: /* primary_expr: asmExpression  */
#line 399 "parser.y"
                                               { (yyval.node) = (yyvsp[0].node); }
#line 5459 "parser.tab.c"
    break;

  case 133: /* primary_expr: nullExpression  */
#line 400 "parser.y"
                                               { (yyval.node) = (yyvsp[0].node); }
#line 5465 "parser.tab.c"
    break;

  case 134: /* primary_expr: undefinedExpression  */
#line 401 "parser.y"
                                               { (yyval.node) = (yyvsp[0].node); }
#line 5471 "parser.tab.c"
    break;

  case 135: /* primary_expr: typeLiteralExpr  */
#line 402 "parser.y"
                                               { (yyval.node) = (yyvsp[0].node); }
#line 5477 "parser.tab.c"
    break;

  case 136: /* primary_expr: importExpression  */
#line 403 "parser.y"
                                               { (yyval.node) = (yyvsp[0].node); }
#line 5483 "parser.tab.c"
    break;

  case 137: /* primary_expr: attr_block_expr  */
#line 404 "parser.y"
                                               { (yyval.node) = (yyvsp[0].node); }
#line 5489 "parser.tab.c"
    break;

  case 138: /* primary_expr: UNREACHABLE  */
#line 405 "parser.y"
                                               { (yyval.node) = unreachable_expr(ZL); }
#line 5495 "parser.tab.c"
    break;

  case 139: /* attribute_opt: %empty  */
#line 409 "parser.y"
                 { (yyval.node) = NULL; }
#line 5501 "parser.tab.c"
    break;

  case 140: /* attribute_opt: attribute  */
#line 410 "parser.y"
                 { (yyval.node) = (yyvsp[0].node); }
#line 5507 "parser.tab.c"
    break;

  case 141: /* collectionBody_opt: %empty  */
#line 414 "parser.y"
                     { (yyval.node) = NULL; }
#line 5513 "parser.tab.c"
    break;

  case 142: /* collectionBody_opt: collectionBody  */
#line 415 "parser.y"
                     { (yyval.node) = (yyvsp[0].node); }
#line 5519 "parser.tab.c"
    break;

  case 143: /* tupleElements_opt: %empty  */
#line 419 "parser.y"
                  { (yyval.node) = NULL; }
#line 5525 "parser.tab.c"
    break;

  case 144: /* tupleElements_opt: tupleElements  */
#line 420 "parser.y"
                  { (yyval.node) = (yyvsp[0].node); }
#line 5531 "parser.tab.c"
    break;

  case 145: /* expression_opt: %empty  */
#line 424 "parser.y"
                 { (yyval.node) = NULL; }
#line 5537 "parser.tab.c"
    break;

  case 146: /* expression_opt: expression  */
#line 425 "parser.y"
                 { (yyval.node) = (yyvsp[0].node); }
#line 5543 "parser.tab.c"
    break;

  case 147: /* label_opt: %empty  */
#line 429 "parser.y"
                 { (yyval.node) = NULL; }
#line 5549 "parser.tab.c"
    break;

  case 148: /* label_opt: label  */
#line 430 "parser.y"
                 { (yyval.node) = (yyvsp[0].node); }
#line 5555 "parser.tab.c"
    break;

  case 149: /* callParams_opt: %empty  */
#line 434 "parser.y"
                 { (yyval.node) = NULL; }
#line 5561 "parser.tab.c"
    break;

  case 150: /* callParams_opt: callParams  */
#line 435 "parser.y"
                 { (yyval.node) = (yyvsp[0].node); }
#line 5567 "parser.tab.c"
    break;

  case 151: /* attr_block_expr: attribute_opt_list blocklike_expr  */
#line 441 "parser.y"
    { (yyval.node) = attr_apply((yyvsp[-1].node), (yyvsp[0].node), ZL); }
#line 5573 "parser.tab.c"
    break;

  case 152: /* attribute_opt_list: %empty  */
#line 445 "parser.y"
                                          { (yyval.node) = NULL; }
#line 5579 "parser.tab.c"
    break;

  case 153: /* attribute_opt_list: attribute_opt_list attribute  */
#line 446 "parser.y"
                                          { (yyval.node) = attr_list_append((yyvsp[-1].node), (yyvsp[0].node)); }
#line 5585 "parser.tab.c"
    break;

  case 154: /* blocklike_expr: blockExpression  */
#line 450 "parser.y"
                                       { (yyval.node) = (yyvsp[0].node); }
#line 5591 "parser.tab.c"
    break;

  case 155: /* blocklike_expr: ASYNC blockExpression  */
#line 451 "parser.y"
                                       { (yyval.node) = async_expression((yyvsp[0].node), ZL); }
#line 5597 "parser.tab.c"
    break;

  case 156: /* blocklike_expr: loopExpression  */
#line 452 "parser.y"
                                       { (yyval.node) = (yyvsp[0].node); }
#line 5603 "parser.tab.c"
    break;

  case 157: /* blocklike_expr: ifExpression  */
#line 453 "parser.y"
                                       { (yyval.node) = (yyvsp[0].node); }
#line 5609 "parser.tab.c"
    break;

  case 158: /* blocklike_expr: matchExpression  */
#line 454 "parser.y"
                                       { (yyval.node) = (yyvsp[0].node); }
#line 5615 "parser.tab.c"
    break;

  case 159: /* blocklike_expr: functionExpression  */
#line 455 "parser.y"
                                       { (yyval.node) = (yyvsp[0].node); }
#line 5621 "parser.tab.c"
    break;

  case 160: /* blocklike_expr: procedureExpression  */
#line 456 "parser.y"
                                       { (yyval.node) = (yyvsp[0].node); }
#line 5627 "parser.tab.c"
    break;

  case 161: /* blocklike_expr: COMPTIME blockExpression  */
#line 457 "parser.y"
                                       { (yyval.node) = comptime_expression((yyvsp[0].node), ZL); }
#line 5633 "parser.tab.c"
    break;

  case 162: /* blocklike_expr: COMPTIME expression  */
#line 458 "parser.y"
                                       { (yyval.node) = comptime_expression((yyvsp[0].node), ZL); }
#line 5639 "parser.tab.c"
    break;

  case 163: /* label: COLON NON_KEYWORD_IDENTIFIER  */
#line 462 "parser.y"
                                   { (yyval.node) = label_node((yyvsp[0].str), ZL); }
#line 5645 "parser.tab.c"
    break;

  case 164: /* nullExpression: NULL_KW  */
#line 466 "parser.y"
                                  { (yyval.node) = null_expr(ZL); }
#line 5651 "parser.tab.c"
    break;

  case 165: /* undefinedExpression: UNDEFINED  */
#line 470 "parser.y"
                                  { (yyval.node) = undefined_expr(ZL); }
#line 5657 "parser.tab.c"
    break;

  case 166: /* functionExpression: functionQualifiers FN LPAREN functionParameters_opt RPAREN type_opt blockExpression  */
#line 479 "parser.y"
    { (yyval.node) = function_expression_node((yyvsp[-6].node), (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[0].node), 0, ZL); }
#line 5663 "parser.tab.c"
    break;

  case 167: /* functionExpression: functionQualifiers FN LPAREN functionParameters_opt RPAREN type_opt RAW_ASM_BLOCK  */
#line 481 "parser.y"
    { AstNode* body = asm_expression((yyvsp[0].str), ZL);
      (yyval.node) = function_expression_node((yyvsp[-6].node), (yyvsp[-3].node), (yyvsp[-1].node), body, 1, ZL); }
#line 5670 "parser.tab.c"
    break;

  case 168: /* procedureExpression: functionQualifiers PROC LPAREN functionParameters_opt RPAREN type_opt blockExpression  */
#line 487 "parser.y"
    { (yyval.node) = procedure_expression_node((yyvsp[-6].node), (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[0].node), 0, ZL); }
#line 5676 "parser.tab.c"
    break;

  case 169: /* procedureExpression: functionQualifiers PROC LPAREN functionParameters_opt RPAREN type_opt RAW_ASM_BLOCK  */
#line 489 "parser.y"
    { AstNode* body = asm_expression((yyvsp[0].str), ZL);
      (yyval.node) = procedure_expression_node((yyvsp[-6].node), (yyvsp[-3].node), (yyvsp[-1].node), body, 1, ZL); }
#line 5683 "parser.tab.c"
    break;

  case 170: /* functionQualifiers: ASYNC_opt extern_opt  */
#line 494 "parser.y"
                               { (yyval.node) = func_qualifiers((yyvsp[-1].node), (yyvsp[0].node), ZL); }
#line 5689 "parser.tab.c"
    break;

  case 171: /* ASYNC_opt: %empty  */
#line 498 "parser.y"
                 { (yyval.node) = NULL; }
#line 5695 "parser.tab.c"
    break;

  case 172: /* ASYNC_opt: ASYNC  */
#line 499 "parser.y"
                 { (yyval.node) = async_qualifier(ZL); }
#line 5701 "parser.tab.c"
    break;

  case 173: /* extern_opt: %empty  */
#line 503 "parser.y"
                           { (yyval.node) = NULL; }
#line 5707 "parser.tab.c"
    break;

  case 174: /* extern_opt: EXTERN abi_opt  */
#line 504 "parser.y"
                           { (yyval.node) = extern_qualifier((yyvsp[0].node), ZL); }
#line 5713 "parser.tab.c"
    break;

  case 175: /* abi_opt: %empty  */
#line 508 "parser.y"
                 { (yyval.node) = NULL; }
#line 5719 "parser.tab.c"
    break;

  case 176: /* abi_opt: abi  */
#line 509 "parser.y"
                 { (yyval.node) = (yyvsp[0].node); }
#line 5725 "parser.tab.c"
    break;

  case 177: /* functionParameters_opt: %empty  */
#line 513 "parser.y"
                         { (yyval.node) = NULL; }
#line 5731 "parser.tab.c"
    break;

  case 178: /* functionParameters_opt: functionParameters  */
#line 514 "parser.y"
                         { (yyval.node) = (yyvsp[0].node); }
#line 5737 "parser.tab.c"
    break;

  case 179: /* functionParameters: functionParam_list COMMA_opt  */
#line 518 "parser.y"
                                  { (yyval.node) = (yyvsp[-1].node); }
#line 5743 "parser.tab.c"
    break;

  case 180: /* functionParam_list: functionParam  */
#line 522 "parser.y"
                                            { (yyval.node) = function_parameters_append(NULL, (yyvsp[0].node)); }
#line 5749 "parser.tab.c"
    break;

  case 181: /* functionParam_list: functionParam_list COMMA functionParam  */
#line 523 "parser.y"
                                            { (yyval.node) = function_parameters_append((yyvsp[-2].node), (yyvsp[0].node)); }
#line 5755 "parser.tab.c"
    break;

  case 182: /* functionParam: attribute_opt COMPTIME_opt functionParamPattern  */
#line 528 "parser.y"
    { (yyval.node) = function_param((yyvsp[-2].node), (yyvsp[-1].node), (yyvsp[0].node), ZL); }
#line 5761 "parser.tab.c"
    break;

  case 183: /* functionParam: attribute_opt COMPTIME_opt DOTDOTDOT  */
#line 530 "parser.y"
    { (yyval.node) = function_param((yyvsp[-2].node), (yyvsp[-1].node), new_node(NODE_ELLIPSIS, ZL), ZL); }
#line 5767 "parser.tab.c"
    break;

  case 184: /* functionParam: attribute_opt COMPTIME_opt type_  */
#line 532 "parser.y"
    { (yyval.node) = function_param((yyvsp[-2].node), (yyvsp[-1].node), (yyvsp[0].node), ZL); }
#line 5773 "parser.tab.c"
    break;

  case 185: /* COMPTIME_opt: %empty  */
#line 536 "parser.y"
                { (yyval.node) = NULL; }
#line 5779 "parser.tab.c"
    break;

  case 186: /* COMPTIME_opt: COMPTIME  */
#line 537 "parser.y"
                { (yyval.node) = comptime_qualifier(ZL); }
#line 5785 "parser.tab.c"
    break;

  case 187: /* functionParamPattern: pattern COLON type_ eqExpr_opt  */
#line 542 "parser.y"
    { (yyval.node) = function_param_pattern((yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[0].node), ZL); }
#line 5791 "parser.tab.c"
    break;

  case 188: /* functionParamPattern: pattern COLON DOTDOTDOT eqExpr_opt  */
#line 544 "parser.y"
    { (yyval.node) = function_param_pattern((yyvsp[-3].node), new_node(NODE_ELLIPSIS, ZL), (yyvsp[0].node), ZL); }
#line 5797 "parser.tab.c"
    break;

  case 189: /* eqExpr_opt: %empty  */
#line 548 "parser.y"
                         { (yyval.node) = NULL; }
#line 5803 "parser.tab.c"
    break;

  case 190: /* eqExpr_opt: EQ expression  */
#line 549 "parser.y"
                         { (yyval.node) = eq_expr((yyvsp[0].node), ZL); }
#line 5809 "parser.tab.c"
    break;

  case 191: /* literalExpression: CHAR_LITERAL  */
#line 557 "parser.y"
                                  { (yyval.node) = literal_node(NODE_CHAR_LITERAL, (yyvsp[0].str), ZL); }
#line 5815 "parser.tab.c"
    break;

  case 192: /* literalExpression: STRING_LITERAL  */
#line 558 "parser.y"
                                  { (yyval.node) = literal_node(NODE_STRING_LITERAL, (yyvsp[0].str), ZL); }
#line 5821 "parser.tab.c"
    break;

  case 193: /* literalExpression: RAW_STRING_LITERAL  */
#line 559 "parser.y"
                                  { (yyval.node) = literal_node(NODE_RAW_STRING_LITERAL, (yyvsp[0].str), ZL); }
#line 5827 "parser.tab.c"
    break;

  case 194: /* literalExpression: BYTE_LITERAL  */
#line 560 "parser.y"
                                  { (yyval.node) = literal_node(NODE_BYTE_LITERAL, (yyvsp[0].str), ZL); }
#line 5833 "parser.tab.c"
    break;

  case 195: /* literalExpression: BYTE_STRING_LITERAL  */
#line 561 "parser.y"
                                  { (yyval.node) = literal_node(NODE_BYTE_STRING_LITERAL, (yyvsp[0].str), ZL); }
#line 5839 "parser.tab.c"
    break;

  case 196: /* literalExpression: RAW_BYTE_STRING_LITERAL  */
#line 562 "parser.y"
                                  { (yyval.node) = literal_node(NODE_RAW_BYTE_STRING_LITERAL, (yyvsp[0].str), ZL); }
#line 5845 "parser.tab.c"
    break;

  case 197: /* literalExpression: INTEGER_LITERAL  */
#line 563 "parser.y"
                                  { (yyval.node) = literal_node(NODE_INTEGER_LITERAL, (yyvsp[0].str), ZL); }
#line 5851 "parser.tab.c"
    break;

  case 198: /* literalExpression: FLOAT_LITERAL  */
#line 564 "parser.y"
                                  { (yyval.node) = literal_node(NODE_FLOAT_LITERAL, (yyvsp[0].str), ZL); }
#line 5857 "parser.tab.c"
    break;

  case 199: /* literalExpression: IMAGINARY_LITERAL  */
#line 565 "parser.y"
                                  { (yyval.node) = literal_node(NODE_IMAGINARY_LITERAL, (yyvsp[0].str), ZL); }
#line 5863 "parser.tab.c"
    break;

  case 200: /* literalExpression: TRUE  */
#line 566 "parser.y"
                                  { (yyval.node) = literal_node(NODE_BOOL_LITERAL, strdup("true"), ZL); }
#line 5869 "parser.tab.c"
    break;

  case 201: /* literalExpression: FALSE  */
#line 567 "parser.y"
                                  { (yyval.node) = literal_node(NODE_BOOL_LITERAL, strdup("false"), ZL); }
#line 5875 "parser.tab.c"
    break;

  case 202: /* blockExpression: LCURLYBRACE attribute_opt statements_opt RCURLYBRACE  */
#line 572 "parser.y"
    { (yyval.node) = block_expression((yyvsp[-2].node), (yyvsp[-1].node), ZL); }
#line 5881 "parser.tab.c"
    break;

  case 203: /* statements_opt: %empty  */
#line 576 "parser.y"
                  { (yyval.node) = NULL; }
#line 5887 "parser.tab.c"
    break;

  case 204: /* statements_opt: statements  */
#line 577 "parser.y"
                  { (yyval.node) = (yyvsp[0].node); }
#line 5893 "parser.tab.c"
    break;

  case 205: /* statements: statement_plus expression_opt  */
#line 581 "parser.y"
                                   { (yyval.node) = statement_list_append((yyvsp[-1].node), (yyvsp[0].node)); }
#line 5899 "parser.tab.c"
    break;

  case 206: /* statements: expression  */
#line 582 "parser.y"
                                   { (yyval.node) = statement_list_append(NULL, (yyvsp[0].node)); }
#line 5905 "parser.tab.c"
    break;

  case 207: /* statement_plus: statement  */
#line 586 "parser.y"
                                   { (yyval.node) = statement_list_append(NULL, (yyvsp[0].node)); }
#line 5911 "parser.tab.c"
    break;

  case 208: /* statement_plus: statement_plus statement  */
#line 587 "parser.y"
                                   { (yyval.node) = statement_list_append((yyvsp[-1].node), (yyvsp[0].node)); }
#line 5917 "parser.tab.c"
    break;

  case 209: /* collectionBody: expression collectionTail_opt  */
#line 596 "parser.y"
    { (yyval.node) = collection_body((yyvsp[-1].node), (yyvsp[0].node), ZL); }
#line 5923 "parser.tab.c"
    break;

  case 210: /* collectionTail_opt: %empty  */
#line 600 "parser.y"
                  { (yyval.node) = NULL; }
#line 5929 "parser.tab.c"
    break;

  case 211: /* collectionTail_opt: restOfMap  */
#line 601 "parser.y"
                  { (yyval.node) = (yyvsp[0].node); }
#line 5935 "parser.tab.c"
    break;

  case 212: /* collectionTail_opt: restOfArray  */
#line 602 "parser.y"
                  { (yyval.node) = (yyvsp[0].node); }
#line 5941 "parser.tab.c"
    break;

  case 213: /* restOfMap: COLON expression mapElement_seq_opt  */
#line 607 "parser.y"
    { (yyval.node) = map_tail((yyvsp[-1].node), (yyvsp[0].node), ZL); }
#line 5947 "parser.tab.c"
    break;

  case 214: /* mapElement_seq_opt: %empty  */
#line 611 "parser.y"
                              { (yyval.node) = NULL; }
#line 5953 "parser.tab.c"
    break;

  case 215: /* mapElement_seq_opt: mapElement_seq COMMA_opt  */
#line 612 "parser.y"
                              { (yyval.node) = (yyvsp[-1].node); }
#line 5959 "parser.tab.c"
    break;

  case 216: /* mapElement_seq: mapElement  */
#line 616 "parser.y"
                                      { (yyval.node) = map_element_list_append(NULL, (yyvsp[0].node)); }
#line 5965 "parser.tab.c"
    break;

  case 217: /* mapElement_seq: mapElement_seq COMMA mapElement  */
#line 617 "parser.y"
                                      { (yyval.node) = map_element_list_append((yyvsp[-2].node), (yyvsp[0].node)); }
#line 5971 "parser.tab.c"
    break;

  case 218: /* mapElement: expression COLON expression  */
#line 621 "parser.y"
                                  { (yyval.node) = map_element((yyvsp[-2].node), (yyvsp[0].node), ZL); }
#line 5977 "parser.tab.c"
    break;

  case 219: /* restOfArray: restArr_seq COMMA_opt  */
#line 629 "parser.y"
                                     { (yyval.node) = (yyvsp[-1].node); }
#line 5983 "parser.tab.c"
    break;

  case 220: /* restOfArray: EOS expression  */
#line 630 "parser.y"
                                     { (yyval.node) = array_rest_list_append(NULL, array_rest_element((yyvsp[0].node), ZL)); }
#line 5989 "parser.tab.c"
    break;

  case 221: /* restArr_seq: COMMA expression  */
#line 635 "parser.y"
                                    { (yyval.node) = array_rest_list_append(NULL, array_rest_element((yyvsp[0].node), ZL)); }
#line 5995 "parser.tab.c"
    break;

  case 222: /* restArr_seq: restArr_seq COMMA expression  */
#line 636 "parser.y"
                                    { (yyval.node) = array_rest_list_append((yyvsp[-2].node), array_rest_element((yyvsp[0].node), ZL)); }
#line 6001 "parser.tab.c"
    break;

  case 223: /* tupleElements: tuple_head expression_opt  */
#line 641 "parser.y"
    {
      AstNode* list = (yyvsp[-1].node);
      if ((yyvsp[0].node)) list = tuple_head_list_append(list, tuple_head_element((yyvsp[0].node), ZL));
      (yyval.node) = list;
    }
#line 6011 "parser.tab.c"
    break;

  case 224: /* tuple_head: expression COMMA  */
#line 650 "parser.y"
    { (yyval.node) = tuple_head_list_append(NULL, tuple_head_element((yyvsp[-1].node), ZL)); }
#line 6017 "parser.tab.c"
    break;

  case 225: /* tuple_head: tuple_head expression COMMA  */
#line 652 "parser.y"
    { (yyval.node) = tuple_head_list_append((yyvsp[-2].node),  tuple_head_element((yyvsp[-1].node), ZL)); }
#line 6023 "parser.tab.c"
    break;

  case 226: /* tupleIndex: INTEGER_LITERAL  */
#line 656 "parser.y"
                     { (yyval.node) = literal_node(NODE_INTEGER_LITERAL, (yyvsp[0].str), ZL); }
#line 6029 "parser.tab.c"
    break;

  case 227: /* structExpression: structExprStruct  */
#line 664 "parser.y"
                       { (yyval.node) = (yyvsp[0].node); }
#line 6035 "parser.tab.c"
    break;

  case 228: /* structExprStruct: path LCURLYBRACE attribute_opt structStructTail_opt RCURLYBRACE  */
#line 669 "parser.y"
    {
      AstNode* fields = NULL; AstNode* base = NULL;
      if ((yyvsp[-1].node) && (yyvsp[-1].node)->type == NODE_STRUCT_FIELD_LIST) fields = (yyvsp[-1].node); else base = (yyvsp[-1].node);
      (yyval.node) = struct_expression((yyvsp[-4].node), (yyvsp[-2].node), fields, base, ZL);
    }
#line 6045 "parser.tab.c"
    break;

  case 229: /* structStructTail_opt: %empty  */
#line 677 "parser.y"
                         { (yyval.node) = NULL; }
#line 6051 "parser.tab.c"
    break;

  case 230: /* structStructTail_opt: structExprFields  */
#line 678 "parser.y"
                         { (yyval.node) = (yyvsp[0].node); }
#line 6057 "parser.tab.c"
    break;

  case 231: /* structStructTail_opt: structBase  */
#line 679 "parser.y"
                         { (yyval.node) = (yyvsp[0].node); }
#line 6063 "parser.tab.c"
    break;

  case 232: /* structExprFields: structExprField_list structExprFieldsTail_opt  */
#line 684 "parser.y"
    { (yyval.node) = (yyvsp[-1].node); /* base (if any) is handled in the caller */ }
#line 6069 "parser.tab.c"
    break;

  case 233: /* structExprFieldsTail_opt: %empty  */
#line 688 "parser.y"
                                { (yyval.node) = NULL; }
#line 6075 "parser.tab.c"
    break;

  case 234: /* structExprFieldsTail_opt: COMMA structBase  */
#line 689 "parser.y"
                                { (yyval.node) = (yyvsp[0].node); }
#line 6081 "parser.tab.c"
    break;

  case 235: /* structExprFieldsTail_opt: COMMA_opt  */
#line 690 "parser.y"
                                { (yyval.node) = NULL; }
#line 6087 "parser.tab.c"
    break;

  case 236: /* structExprField_list: structExprField  */
#line 694 "parser.y"
                                                 { (yyval.node) = struct_field_list_append(NULL, (yyvsp[0].node)); }
#line 6093 "parser.tab.c"
    break;

  case 237: /* structExprField_list: structExprField_list COMMA structExprField  */
#line 695 "parser.y"
                                                 { (yyval.node) = struct_field_list_append((yyvsp[-2].node), (yyvsp[0].node)); }
#line 6099 "parser.tab.c"
    break;

  case 238: /* structExprField: attribute_opt identifier  */
#line 700 "parser.y"
    { (yyval.node) = struct_field((yyvsp[-1].node), (yyvsp[0].node), 0, NULL, ZL); }
#line 6105 "parser.tab.c"
    break;

  case 239: /* structExprField: attribute_opt identifier COLON expression  */
#line 702 "parser.y"
    { (yyval.node) = struct_field((yyvsp[-3].node), (yyvsp[-2].node), 0, (yyvsp[0].node), ZL); }
#line 6111 "parser.tab.c"
    break;

  case 240: /* structExprField: attribute_opt tupleIndex COLON expression  */
#line 704 "parser.y"
    { (yyval.node) = struct_field((yyvsp[-3].node), (yyvsp[-2].node), 1, (yyvsp[0].node), ZL); }
#line 6117 "parser.tab.c"
    break;

  case 241: /* structBase: DOTDOT expression  */
#line 708 "parser.y"
                       { (yyval.node) = struct_base((yyvsp[0].node), ZL); }
#line 6123 "parser.tab.c"
    break;

  case 242: /* enumerationVariantExpression: enumExprStruct  */
#line 712 "parser.y"
                    { (yyval.node) = (yyvsp[0].node); }
#line 6129 "parser.tab.c"
    break;

  case 243: /* enumExprStruct: path LCURLYBRACE enumExprField_list COMMA_opt RCURLYBRACE  */
#line 722 "parser.y"
    { (yyval.node) = enum_variant_expression((yyvsp[-4].node), (yyvsp[-2].node), ZL); }
#line 6135 "parser.tab.c"
    break;

  case 244: /* enumExprStruct: path LCURLYBRACE RCURLYBRACE  */
#line 724 "parser.y"
    { (yyval.node) = enum_variant_expression((yyvsp[-2].node), NULL, ZL); }
#line 6141 "parser.tab.c"
    break;

  case 245: /* enumExprField_list: enumExprField  */
#line 728 "parser.y"
                                            { (yyval.node) = enum_variant_field_list_append(NULL, (yyvsp[0].node)); }
#line 6147 "parser.tab.c"
    break;

  case 246: /* enumExprField_list: enumExprField_list COMMA enumExprField  */
#line 729 "parser.y"
                                            { (yyval.node) = enum_variant_field_list_append((yyvsp[-2].node), (yyvsp[0].node)); }
#line 6153 "parser.tab.c"
    break;

  case 247: /* enumExprField: identifier  */
#line 733 "parser.y"
                                  { (yyval.node) = enum_variant_field((yyvsp[0].node), 0, NULL, ZL); }
#line 6159 "parser.tab.c"
    break;

  case 248: /* enumExprField: identifier COLON expression  */
#line 734 "parser.y"
                                  { (yyval.node) = enum_variant_field((yyvsp[-2].node), 0, (yyvsp[0].node), ZL); }
#line 6165 "parser.tab.c"
    break;

  case 249: /* enumExprField: tupleIndex COLON expression  */
#line 735 "parser.y"
                                  { (yyval.node) = enum_variant_field((yyvsp[-2].node), 1, (yyvsp[0].node), ZL); }
#line 6171 "parser.tab.c"
    break;

  case 250: /* callParams: expression_list COMMA_opt  */
#line 739 "parser.y"
                               { (yyval.node) = (yyvsp[-1].node); }
#line 6177 "parser.tab.c"
    break;

  case 251: /* closureExpression: PIPEPIPE expression  */
#line 748 "parser.y"
    { (yyval.node) = closure_expression(NULL, NULL, (yyvsp[0].node), 0, ZL); }
#line 6183 "parser.tab.c"
    break;

  case 252: /* closureExpression: PIPEPIPE type_ blockExpression  */
#line 750 "parser.y"
    { (yyval.node) = closure_expression(NULL, (yyvsp[-1].node), (yyvsp[0].node), 1, ZL); }
#line 6189 "parser.tab.c"
    break;

  case 253: /* closureExpression: B_OR closureParameters_opt B_OR expression  */
#line 752 "parser.y"
    { (yyval.node) = closure_expression((yyvsp[-2].node), NULL, (yyvsp[0].node), 0, ZL); }
#line 6195 "parser.tab.c"
    break;

  case 254: /* closureExpression: B_OR closureParameters_opt B_OR type_ blockExpression  */
#line 754 "parser.y"
    { (yyval.node) = closure_expression((yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[0].node), 1, ZL); }
#line 6201 "parser.tab.c"
    break;

  case 255: /* closureParameters_opt: %empty  */
#line 758 "parser.y"
                        { (yyval.node) = NULL; }
#line 6207 "parser.tab.c"
    break;

  case 256: /* closureParameters_opt: closureParameters  */
#line 759 "parser.y"
                        { (yyval.node) = (yyvsp[0].node); }
#line 6213 "parser.tab.c"
    break;

  case 257: /* closureParameters: closureParam_list COMMA_opt  */
#line 763 "parser.y"
                                 { (yyval.node) = (yyvsp[-1].node); }
#line 6219 "parser.tab.c"
    break;

  case 258: /* closureParam_list: closureParam  */
#line 767 "parser.y"
                                          { (yyval.node) = closure_params_append(NULL, (yyvsp[0].node)); }
#line 6225 "parser.tab.c"
    break;

  case 259: /* closureParam_list: closureParam_list COMMA closureParam  */
#line 768 "parser.y"
                                          { (yyval.node) = closure_params_append((yyvsp[-2].node), (yyvsp[0].node)); }
#line 6231 "parser.tab.c"
    break;

  case 260: /* closureParam: attribute_opt pattern typeAnn_opt  */
#line 773 "parser.y"
    { (yyval.node) = closure_param((yyvsp[-2].node), (yyvsp[-1].node), (yyvsp[0].node), ZL); }
#line 6237 "parser.tab.c"
    break;

  case 261: /* typeAnn_opt: %empty  */
#line 777 "parser.y"
                    { (yyval.node) = NULL; }
#line 6243 "parser.tab.c"
    break;

  case 262: /* typeAnn_opt: COLON type_  */
#line 778 "parser.y"
                    { (yyval.node) = type_annotation((yyvsp[0].node), ZL); }
#line 6249 "parser.tab.c"
    break;

  case 263: /* loopExpression: loopLabel_opt loopBody  */
#line 787 "parser.y"
    { (yyval.node) = (yyvsp[0].node); if ((yyval.node)) (yyval.node)->data.loopExpr.label = (yyvsp[-1].node); }
#line 6255 "parser.tab.c"
    break;

  case 264: /* loopLabel_opt: %empty  */
#line 791 "parser.y"
                { (yyval.node) = NULL; }
#line 6261 "parser.tab.c"
    break;

  case 265: /* loopLabel_opt: loopLabel  */
#line 792 "parser.y"
                { (yyval.node) = (yyvsp[0].node); }
#line 6267 "parser.tab.c"
    break;

  case 266: /* loopBody: infiniteLoopExpression  */
#line 796 "parser.y"
                                       { (yyval.node) = (yyvsp[0].node); }
#line 6273 "parser.tab.c"
    break;

  case 267: /* loopBody: predicateLoopExpression  */
#line 797 "parser.y"
                                       { (yyval.node) = (yyvsp[0].node); }
#line 6279 "parser.tab.c"
    break;

  case 268: /* loopBody: predicatePatternLoopExpression  */
#line 798 "parser.y"
                                       { (yyval.node) = (yyvsp[0].node); }
#line 6285 "parser.tab.c"
    break;

  case 269: /* loopBody: iteratorLoopExpression  */
#line 799 "parser.y"
                                       { (yyval.node) = (yyvsp[0].node); }
#line 6291 "parser.tab.c"
    break;

  case 270: /* infiniteLoopExpression: WHILE blockExpression  */
#line 804 "parser.y"
    { (yyval.node) = loop_expression_infinite(NULL, (yyvsp[0].node), ZL); }
#line 6297 "parser.tab.c"
    break;

  case 271: /* predicateLoopExpression: WHILE expression blockExpression  */
#line 809 "parser.y"
    { (yyval.node) = loop_expression_predicate(NULL, (yyvsp[-1].node), (yyvsp[0].node), ZL); }
#line 6303 "parser.tab.c"
    break;

  case 272: /* predicatePatternLoopExpression: WHILE IS pattern COLONEQ expression blockExpression  */
#line 814 "parser.y"
    { (yyval.node) = loop_expression_predicate_pattern(NULL, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[0].node), ZL); }
#line 6309 "parser.tab.c"
    break;

  case 273: /* iteratorLoopExpression: FOR pattern IN expression blockExpression  */
#line 819 "parser.y"
    { (yyval.node) = loop_expression_iterator(NULL, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[0].node), ZL); }
#line 6315 "parser.tab.c"
    break;

  case 274: /* loopLabel: NON_KEYWORD_IDENTIFIER COLON  */
#line 824 "parser.y"
    { (yyval.node) = identifier_node((yyvsp[-1].str), ZL); }
#line 6321 "parser.tab.c"
    break;

  case 275: /* codeExpression: CODE LCURLYBRACE statements_opt RCURLYBRACE  */
#line 839 "parser.y"
    { (yyval.node) = code_expression((yyvsp[-1].node), ZL); }
#line 6327 "parser.tab.c"
    break;

  case 276: /* mlirExpression: MLIR mlirHead_opt LCURLYBRACE mlirBody_opt RCURLYBRACE  */
#line 845 "parser.y"
    { (yyval.node) = mlir_expression((yyvsp[-3].node), (yyvsp[-1].node), ZL); }
#line 6333 "parser.tab.c"
    break;

  case 277: /* mlirHead_opt: %empty  */
#line 849 "parser.y"
                  { (yyval.node) = NULL; }
#line 6339 "parser.tab.c"
    break;

  case 278: /* mlirHead_opt: TYPE  */
#line 850 "parser.y"
                  { (yyval.node) = type_path(path_single(identifier_node("type", ZL), ZL), ZL); }
#line 6345 "parser.tab.c"
    break;

  case 279: /* mlirHead_opt: identifier  */
#line 851 "parser.y"
                  { (yyval.node) = (yyvsp[0].node); }
#line 6351 "parser.tab.c"
    break;

  case 280: /* mlirBody_opt: %empty  */
#line 855 "parser.y"
                 { (yyval.node) = NULL; }
#line 6357 "parser.tab.c"
    break;

  case 281: /* asmExpression: RAW_ASM_BLOCK  */
#line 859 "parser.y"
                   { (yyval.node) = asm_expression((yyvsp[0].str), ZL); }
#line 6363 "parser.tab.c"
    break;

  case 282: /* importExpression: IMPORT path  */
#line 863 "parser.y"
                   { (yyval.node) = import_expression((yyvsp[0].node), ZL); }
#line 6369 "parser.tab.c"
    break;

  case 283: /* ifExpression: IF expression blockExpression elseTail_opt  */
#line 872 "parser.y"
    { (yyval.node) = if_expression((yyvsp[-2].node), (yyvsp[-1].node), (yyvsp[0].node), ZL); }
#line 6375 "parser.tab.c"
    break;

  case 284: /* elseTail_opt: %empty  */
#line 876 "parser.y"
                          { (yyval.node) = NULL; }
#line 6381 "parser.tab.c"
    break;

  case 285: /* elseTail_opt: ELSE blockExpression  */
#line 877 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 6387 "parser.tab.c"
    break;

  case 286: /* elseTail_opt: ELSE ifExpression  */
#line 878 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 6393 "parser.tab.c"
    break;

  case 287: /* matchExpression: MATCH expression LCURLYBRACE attribute_opt matchArms_opt RCURLYBRACE  */
#line 883 "parser.y"
    { (yyval.node) = match_expression((yyvsp[-4].node), (yyvsp[-2].node), (yyvsp[-1].node), ZL); }
#line 6399 "parser.tab.c"
    break;

  case 288: /* matchArms_opt: %empty  */
#line 887 "parser.y"
                 { (yyval.node) = NULL; }
#line 6405 "parser.tab.c"
    break;

  case 289: /* matchArms_opt: matchArms  */
#line 888 "parser.y"
                 { (yyval.node) = (yyvsp[0].node); }
#line 6411 "parser.tab.c"
    break;

  case 290: /* matchArms: matchArm FATARROW matchRHS COMMA matchArms  */
#line 893 "parser.y"
    { AstNode* arm = match_arm((yyvsp[-4].node)->data.matchArm.attr, (yyvsp[-4].node), (yyvsp[-2].node), ZL); (yyval.node) = match_arm_list_append((yyvsp[0].node), arm); }
#line 6417 "parser.tab.c"
    break;

  case 291: /* matchArms: matchArm FATARROW matchRHS COMMA  */
#line 895 "parser.y"
    { AstNode* arm = match_arm((yyvsp[-3].node)->data.matchArm.attr, (yyvsp[-3].node), (yyvsp[-1].node), ZL); (yyval.node) = match_arm_list_append(NULL, arm); }
#line 6423 "parser.tab.c"
    break;

  case 292: /* matchRHS: expression  */
#line 899 "parser.y"
                     { (yyval.node) = (yyvsp[0].node); }
#line 6429 "parser.tab.c"
    break;

  case 293: /* matchArm: attribute_opt pattern matchArmGuard_opt  */
#line 904 "parser.y"
    { AstNode* head = match_arm_head((yyvsp[-1].node), (yyvsp[0].node), ZL); head->data.matchArm.attr = (yyvsp[-2].node); (yyval.node) = head; }
#line 6435 "parser.tab.c"
    break;

  case 294: /* matchArmGuard_opt: %empty  */
#line 908 "parser.y"
                    { (yyval.node) = NULL; }
#line 6441 "parser.tab.c"
    break;

  case 295: /* matchArmGuard_opt: IF expression  */
#line 909 "parser.y"
                    { (yyval.node) = match_guard((yyvsp[0].node), ZL); }
#line 6447 "parser.tab.c"
    break;

  case 296: /* pattern: patternNoTopAlt patternAltTail_opt  */
#line 918 "parser.y"
    { (yyval.node) = ((yyvsp[0].node) ? binary_expr((yyvsp[-1].node), (yyvsp[0].node), OP_BOR, ZL) : (yyvsp[-1].node)); }
#line 6453 "parser.tab.c"
    break;

  case 297: /* patternAltTail_opt: %empty  */
#line 922 "parser.y"
                                                 { (yyval.node) = NULL; }
#line 6459 "parser.tab.c"
    break;

  case 298: /* patternAltTail_opt: patternAltTail_opt B_OR patternNoTopAlt  */
#line 923 "parser.y"
                                                 { (yyval.node) = ((yyvsp[-2].node) ? binary_expr((yyvsp[-2].node), (yyvsp[0].node), OP_BOR, ZL) : (yyvsp[0].node)); }
#line 6465 "parser.tab.c"
    break;

  case 299: /* patternNoTopAlt: patternWithoutRange  */
#line 927 "parser.y"
                         { (yyval.node) = (yyvsp[0].node); }
#line 6471 "parser.tab.c"
    break;

  case 300: /* patternNoTopAlt: rangePattern  */
#line 928 "parser.y"
                         { (yyval.node) = (yyvsp[0].node); }
#line 6477 "parser.tab.c"
    break;

  case 301: /* patternWithoutRange: literalPattern  */
#line 932 "parser.y"
                         { (yyval.node) = (yyvsp[0].node); }
#line 6483 "parser.tab.c"
    break;

  case 302: /* patternWithoutRange: identifierPattern  */
#line 933 "parser.y"
                         { (yyval.node) = (yyvsp[0].node); }
#line 6489 "parser.tab.c"
    break;

  case 303: /* patternWithoutRange: wildcardPattern  */
#line 934 "parser.y"
                         { (yyval.node) = (yyvsp[0].node); }
#line 6495 "parser.tab.c"
    break;

  case 304: /* patternWithoutRange: restPattern  */
#line 935 "parser.y"
                         { (yyval.node) = (yyvsp[0].node); }
#line 6501 "parser.tab.c"
    break;

  case 305: /* patternWithoutRange: structPattern  */
#line 936 "parser.y"
                         { (yyval.node) = (yyvsp[0].node); }
#line 6507 "parser.tab.c"
    break;

  case 306: /* patternWithoutRange: tupleStructPattern  */
#line 937 "parser.y"
                         { (yyval.node) = (yyvsp[0].node); }
#line 6513 "parser.tab.c"
    break;

  case 307: /* patternWithoutRange: tuplePattern  */
#line 938 "parser.y"
                         { (yyval.node) = (yyvsp[0].node); }
#line 6519 "parser.tab.c"
    break;

  case 308: /* patternWithoutRange: groupedPattern  */
#line 939 "parser.y"
                         { (yyval.node) = (yyvsp[0].node); }
#line 6525 "parser.tab.c"
    break;

  case 309: /* patternWithoutRange: slicePattern  */
#line 940 "parser.y"
                         { (yyval.node) = (yyvsp[0].node); }
#line 6531 "parser.tab.c"
    break;

  case 310: /* patternWithoutRange: pathPattern  */
#line 941 "parser.y"
                         { (yyval.node) = (yyvsp[0].node); }
#line 6537 "parser.tab.c"
    break;

  case 311: /* literalPattern: TRUE  */
#line 945 "parser.y"
                                  { (yyval.node) = pattern_literal(literal_node(NODE_BOOL_LITERAL, strdup("true"), ZL), ZL); }
#line 6543 "parser.tab.c"
    break;

  case 312: /* literalPattern: FALSE  */
#line 946 "parser.y"
                                  { (yyval.node) = pattern_literal(literal_node(NODE_BOOL_LITERAL, strdup("false"), ZL), ZL); }
#line 6549 "parser.tab.c"
    break;

  case 313: /* literalPattern: CHAR_LITERAL  */
#line 947 "parser.y"
                                  { (yyval.node) = pattern_literal(literal_node(NODE_CHAR_LITERAL, (yyvsp[0].str), ZL), ZL); }
#line 6555 "parser.tab.c"
    break;

  case 314: /* literalPattern: BYTE_LITERAL  */
#line 948 "parser.y"
                                  { (yyval.node) = pattern_literal(literal_node(NODE_BYTE_LITERAL, (yyvsp[0].str), ZL), ZL); }
#line 6561 "parser.tab.c"
    break;

  case 315: /* literalPattern: STRING_LITERAL  */
#line 949 "parser.y"
                                  { (yyval.node) = pattern_literal(literal_node(NODE_STRING_LITERAL, (yyvsp[0].str), ZL), ZL); }
#line 6567 "parser.tab.c"
    break;

  case 316: /* literalPattern: RAW_STRING_LITERAL  */
#line 950 "parser.y"
                                  { (yyval.node) = pattern_literal(literal_node(NODE_RAW_STRING_LITERAL, (yyvsp[0].str), ZL), ZL); }
#line 6573 "parser.tab.c"
    break;

  case 317: /* literalPattern: BYTE_STRING_LITERAL  */
#line 951 "parser.y"
                                  { (yyval.node) = pattern_literal(literal_node(NODE_BYTE_STRING_LITERAL, (yyvsp[0].str), ZL), ZL); }
#line 6579 "parser.tab.c"
    break;

  case 318: /* literalPattern: RAW_BYTE_STRING_LITERAL  */
#line 952 "parser.y"
                                  { (yyval.node) = pattern_literal(literal_node(NODE_RAW_BYTE_STRING_LITERAL, (yyvsp[0].str), ZL), ZL); }
#line 6585 "parser.tab.c"
    break;

  case 319: /* literalPattern: MINUS_opt INTEGER_LITERAL  */
#line 954 "parser.y"
    { AstNode* lit = literal_node(NODE_INTEGER_LITERAL, (yyvsp[0].str), ZL); (yyval.node) = (yyvsp[-1].ival) ? pattern_literal(unary_expr(lit, OP_NEG, ZL), ZL) : pattern_literal(lit, ZL); }
#line 6591 "parser.tab.c"
    break;

  case 320: /* literalPattern: MINUS_opt FLOAT_LITERAL  */
#line 956 "parser.y"
    { AstNode* lit = literal_node(NODE_FLOAT_LITERAL, (yyvsp[0].str), ZL); (yyval.node) = (yyvsp[-1].ival) ? pattern_literal(unary_expr(lit, OP_NEG, ZL), ZL) : pattern_literal(lit, ZL); }
#line 6597 "parser.tab.c"
    break;

  case 321: /* literalPattern: IMAGINARY_LITERAL  */
#line 958 "parser.y"
    { (yyval.node) = pattern_literal(literal_node(NODE_IMAGINARY_LITERAL, (yyvsp[0].str), ZL), ZL); }
#line 6603 "parser.tab.c"
    break;

  case 322: /* MINUS_opt: %empty  */
#line 962 "parser.y"
                { (yyval.ival) = 0; }
#line 6609 "parser.tab.c"
    break;

  case 323: /* MINUS_opt: MINUS  */
#line 963 "parser.y"
                { (yyval.ival) = 1; }
#line 6615 "parser.tab.c"
    break;

  case 324: /* identifierPattern: identifier atTail_opt  */
#line 968 "parser.y"
    { (yyval.node) = pattern_identifier((yyvsp[-1].node), (yyvsp[0].node), ZL); }
#line 6621 "parser.tab.c"
    break;

  case 325: /* atTail_opt: %empty  */
#line 972 "parser.y"
                    { (yyval.node) = NULL; }
#line 6627 "parser.tab.c"
    break;

  case 326: /* atTail_opt: AT pattern  */
#line 973 "parser.y"
                    { (yyval.node) = (yyvsp[0].node); }
#line 6633 "parser.tab.c"
    break;

  case 327: /* wildcardPattern: UNDERSCORE  */
#line 977 "parser.y"
                    { (yyval.node) = pattern_wildcard(ZL); }
#line 6639 "parser.tab.c"
    break;

  case 328: /* restPattern: DOTDOT  */
#line 981 "parser.y"
                    { (yyval.node) = pattern_rest(ZL); }
#line 6645 "parser.tab.c"
    break;

  case 329: /* rangePattern: rangePatternBound DOTDOTEQ rangePatternBound  */
#line 986 "parser.y"
    { (yyval.node) = pattern_range(RANGE_CLOSED, (yyvsp[-2].node), (yyvsp[0].node), ZL); }
#line 6651 "parser.tab.c"
    break;

  case 330: /* rangePattern: rangePatternBound DOTDOT rangePatternBound  */
#line 988 "parser.y"
    { (yyval.node) = pattern_range(RANGE_HALF_OPEN, (yyvsp[-2].node), (yyvsp[0].node), ZL); }
#line 6657 "parser.tab.c"
    break;

  case 331: /* rangePattern: rangePatternBound DOTDOT  */
#line 990 "parser.y"
    { (yyval.node) = pattern_range(RANGE_FROM, (yyvsp[-1].node), NULL, ZL); }
#line 6663 "parser.tab.c"
    break;

  case 332: /* rangePattern: DOTDOT rangePatternBound  */
#line 992 "parser.y"
    { (yyval.node) = pattern_range(RANGE_TO, NULL, (yyvsp[0].node), ZL); }
#line 6669 "parser.tab.c"
    break;

  case 333: /* rangePatternBound: CHAR_LITERAL  */
#line 996 "parser.y"
                     { (yyval.node) = literal_node(NODE_CHAR_LITERAL, (yyvsp[0].str), ZL); }
#line 6675 "parser.tab.c"
    break;

  case 334: /* rangePatternBound: BYTE_LITERAL  */
#line 997 "parser.y"
                     { (yyval.node) = literal_node(NODE_BYTE_LITERAL, (yyvsp[0].str), ZL); }
#line 6681 "parser.tab.c"
    break;

  case 335: /* rangePatternBound: MINUS_opt INTEGER_LITERAL  */
#line 999 "parser.y"
    { AstNode* lit = literal_node(NODE_INTEGER_LITERAL, (yyvsp[0].str), ZL); (yyval.node) = (yyvsp[-1].ival) ? unary_expr(lit, OP_NEG, ZL) : lit; }
#line 6687 "parser.tab.c"
    break;

  case 336: /* rangePatternBound: MINUS_opt FLOAT_LITERAL  */
#line 1001 "parser.y"
    { AstNode* lit = literal_node(NODE_FLOAT_LITERAL, (yyvsp[0].str), ZL); (yyval.node) = (yyvsp[-1].ival) ? unary_expr(lit, OP_NEG, ZL) : lit; }
#line 6693 "parser.tab.c"
    break;

  case 337: /* rangePatternBound: pathPattern  */
#line 1002 "parser.y"
                     { (yyval.node) = (yyvsp[0].node); }
#line 6699 "parser.tab.c"
    break;

  case 338: /* structPattern: path LCURLYBRACE structPatternElements_opt RCURLYBRACE  */
#line 1008 "parser.y"
    {
      AstNode *fields = NULL;
      int has_etc = 0;
      if ((yyvsp[-1].node) && (yyvsp[-1].node)->type == NODE_PATTERN_STRUCT_ELEMS) {
        fields = (yyvsp[-1].node)->data.patStructElems.fields;
        has_etc = (yyvsp[-1].node)->data.patStructElems.has_etc;
      }
      (yyval.node) = pattern_struct((yyvsp[-3].node), fields, has_etc, ZL);
    }
#line 6713 "parser.tab.c"
    break;

  case 339: /* structPatternElements_opt: %empty  */
#line 1025 "parser.y"
                           { (yyval.node) = NULL; }
#line 6719 "parser.tab.c"
    break;

  case 340: /* structPatternElements_opt: structPatternElements  */
#line 1026 "parser.y"
                           { (yyval.node) = (yyvsp[0].node); }
#line 6725 "parser.tab.c"
    break;

  case 341: /* structPatternElements: structPatternFields structPatEtcTail_opt  */
#line 1031 "parser.y"
    { int has_etc = ((yyvsp[0].node) != NULL); (yyval.node) = pattern_struct_elems((yyvsp[-1].node), has_etc, ZL); }
#line 6731 "parser.tab.c"
    break;

  case 342: /* structPatternElements: structPatternEtCetera  */
#line 1033 "parser.y"
    { (yyval.node) = pattern_struct_elems(NULL, 1, ZL); }
#line 6737 "parser.tab.c"
    break;

  case 343: /* structPatEtcTail_opt: %empty  */
#line 1037 "parser.y"
                                      { (yyval.node) = NULL; }
#line 6743 "parser.tab.c"
    break;

  case 344: /* structPatEtcTail_opt: COMMA structPatternEtCetera_opt  */
#line 1038 "parser.y"
                                      { (yyval.node) = (yyvsp[0].node); }
#line 6749 "parser.tab.c"
    break;

  case 345: /* structPatternEtCetera_opt: %empty  */
#line 1042 "parser.y"
                         { (yyval.node) = NULL; }
#line 6755 "parser.tab.c"
    break;

  case 346: /* structPatternEtCetera_opt: structPatternEtCetera  */
#line 1043 "parser.y"
                         { (yyval.node) = (yyvsp[0].node); }
#line 6761 "parser.tab.c"
    break;

  case 347: /* structPatternFields: structPatternField_list  */
#line 1047 "parser.y"
                             { (yyval.node) = (yyvsp[0].node); }
#line 6767 "parser.tab.c"
    break;

  case 348: /* structPatternField_list: structPatternField  */
#line 1051 "parser.y"
                                                    { (yyval.node) = pattern_struct_field_list_append(NULL, (yyvsp[0].node)); }
#line 6773 "parser.tab.c"
    break;

  case 349: /* structPatternField_list: structPatternField_list COMMA structPatternField  */
#line 1052 "parser.y"
                                                    { (yyval.node) = pattern_struct_field_list_append((yyvsp[-2].node), (yyvsp[0].node)); }
#line 6779 "parser.tab.c"
    break;

  case 350: /* structPatternField: attribute_opt tupleIndex COLON pattern  */
#line 1057 "parser.y"
    { (yyval.node) = pattern_struct_field((yyvsp[-3].node), (yyvsp[-2].node), 1, (yyvsp[0].node), ZL); }
#line 6785 "parser.tab.c"
    break;

  case 351: /* structPatternField: attribute_opt identifier COLON pattern  */
#line 1059 "parser.y"
    { (yyval.node) = pattern_struct_field((yyvsp[-3].node), (yyvsp[-2].node), 0, (yyvsp[0].node), ZL); }
#line 6791 "parser.tab.c"
    break;

  case 352: /* structPatternField: attribute_opt identifier  */
#line 1061 "parser.y"
    { (yyval.node) = pattern_struct_field((yyvsp[-1].node), (yyvsp[0].node), 0, NULL, ZL); }
#line 6797 "parser.tab.c"
    break;

  case 353: /* structPatternEtCetera: attribute_opt DOTDOT  */
#line 1065 "parser.y"
                          { (void)(yyvsp[-1].node); (yyval.node) = new_node(NODE_PATTERN_REST, ZL); }
#line 6803 "parser.tab.c"
    break;

  case 354: /* tupleStructPattern: path LPAREN tupleStructItems_opt RPAREN  */
#line 1070 "parser.y"
    { (yyval.node) = pattern_tuple_struct((yyvsp[-3].node), (yyvsp[-1].node), ZL); }
#line 6809 "parser.tab.c"
    break;

  case 355: /* tupleStructItems_opt: %empty  */
#line 1074 "parser.y"
                         { (yyval.node) = NULL; }
#line 6815 "parser.tab.c"
    break;

  case 356: /* tupleStructItems_opt: tupleStructItems  */
#line 1075 "parser.y"
                         { (yyval.node) = (yyvsp[0].node); }
#line 6821 "parser.tab.c"
    break;

  case 357: /* tupleStructItems: pattern_list COMMA_opt  */
#line 1079 "parser.y"
                             { (yyval.node) = (yyvsp[-1].node); }
#line 6827 "parser.tab.c"
    break;

  case 358: /* tuplePattern: LPAREN tuplePatternItems_opt RPAREN  */
#line 1084 "parser.y"
    { (yyval.node) = pattern_tuple((yyvsp[-1].node), ZL); }
#line 6833 "parser.tab.c"
    break;

  case 359: /* tuplePatternItems_opt: %empty  */
#line 1088 "parser.y"
                        { (yyval.node) = NULL; }
#line 6839 "parser.tab.c"
    break;

  case 360: /* tuplePatternItems_opt: tuplePatternItems  */
#line 1089 "parser.y"
                        { (yyval.node) = (yyvsp[0].node); }
#line 6845 "parser.tab.c"
    break;

  case 361: /* tuplePatList: pattern  */
#line 1100 "parser.y"
    { (yyval.node) = expr_list_append(NULL, (yyvsp[0].node)); }
#line 6851 "parser.tab.c"
    break;

  case 362: /* tuplePatList: tuplePatList COMMA pattern  */
#line 1102 "parser.y"
    { (yyval.node) = expr_list_append((yyvsp[-2].node), (yyvsp[0].node)); }
#line 6857 "parser.tab.c"
    break;

  case 363: /* tuplePatternItems: tuplePatList COMMA  */
#line 1107 "parser.y"
    { (yyval.node) = (yyvsp[-1].node); }
#line 6863 "parser.tab.c"
    break;

  case 364: /* tuplePatternItems: restPattern  */
#line 1109 "parser.y"
    { (yyval.node) = expr_list_append(NULL, (yyvsp[0].node)); }
#line 6869 "parser.tab.c"
    break;

  case 365: /* groupedPattern: LPAREN patternNoTopAlt_noRest RPAREN  */
#line 1114 "parser.y"
                                          { (yyval.node) = pattern_grouped((yyvsp[-1].node), ZL); }
#line 6875 "parser.tab.c"
    break;

  case 366: /* patternNoTopAlt_noRest: patternWithoutRange_noRest  */
#line 1118 "parser.y"
                                { (yyval.node) = (yyvsp[0].node); }
#line 6881 "parser.tab.c"
    break;

  case 367: /* patternNoTopAlt_noRest: rangePattern  */
#line 1119 "parser.y"
                                { (yyval.node) = (yyvsp[0].node); }
#line 6887 "parser.tab.c"
    break;

  case 368: /* patternWithoutRange_noRest: literalPattern  */
#line 1123 "parser.y"
                           { (yyval.node) = (yyvsp[0].node); }
#line 6893 "parser.tab.c"
    break;

  case 369: /* patternWithoutRange_noRest: identifierPattern  */
#line 1124 "parser.y"
                           { (yyval.node) = (yyvsp[0].node); }
#line 6899 "parser.tab.c"
    break;

  case 370: /* patternWithoutRange_noRest: wildcardPattern  */
#line 1125 "parser.y"
                           { (yyval.node) = (yyvsp[0].node); }
#line 6905 "parser.tab.c"
    break;

  case 371: /* patternWithoutRange_noRest: structPattern  */
#line 1126 "parser.y"
                           { (yyval.node) = (yyvsp[0].node); }
#line 6911 "parser.tab.c"
    break;

  case 372: /* patternWithoutRange_noRest: tupleStructPattern  */
#line 1127 "parser.y"
                           { (yyval.node) = (yyvsp[0].node); }
#line 6917 "parser.tab.c"
    break;

  case 373: /* patternWithoutRange_noRest: tuplePattern  */
#line 1128 "parser.y"
                           { (yyval.node) = (yyvsp[0].node); }
#line 6923 "parser.tab.c"
    break;

  case 374: /* patternWithoutRange_noRest: groupedPattern  */
#line 1129 "parser.y"
                           { (yyval.node) = (yyvsp[0].node); }
#line 6929 "parser.tab.c"
    break;

  case 375: /* patternWithoutRange_noRest: slicePattern  */
#line 1130 "parser.y"
                           { (yyval.node) = (yyvsp[0].node); }
#line 6935 "parser.tab.c"
    break;

  case 376: /* patternWithoutRange_noRest: pathPattern  */
#line 1131 "parser.y"
                           { (yyval.node) = (yyvsp[0].node); }
#line 6941 "parser.tab.c"
    break;

  case 377: /* slicePattern: LSQUAREBRACKET slicePatternItems_opt RSQUAREBRACKET  */
#line 1136 "parser.y"
    { (yyval.node) = pattern_slice((yyvsp[-1].node), ZL); }
#line 6947 "parser.tab.c"
    break;

  case 378: /* slicePatternItems_opt: %empty  */
#line 1140 "parser.y"
                      { (yyval.node) = NULL; }
#line 6953 "parser.tab.c"
    break;

  case 379: /* slicePatternItems_opt: slicePatternItems  */
#line 1141 "parser.y"
                      { (yyval.node) = (yyvsp[0].node); }
#line 6959 "parser.tab.c"
    break;

  case 380: /* slicePatternItems: pattern_list COMMA_opt  */
#line 1145 "parser.y"
                           { (yyval.node) = (yyvsp[-1].node); }
#line 6965 "parser.tab.c"
    break;

  case 381: /* pathPattern: path_ndot  */
#line 1149 "parser.y"
                 { (yyval.node) = pattern_path((yyvsp[0].node), ZL); }
#line 6971 "parser.tab.c"
    break;

  case 384: /* typeAtom: parenthesizedType  */
#line 1172 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 6977 "parser.tab.c"
    break;

  case 385: /* typeAtom: path  */
#line 1173 "parser.y"
                          { (yyval.node) = type_path((yyvsp[0].node), ZL); }
#line 6983 "parser.tab.c"
    break;

  case 386: /* typeAtom: tupleType  */
#line 1174 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 6989 "parser.tab.c"
    break;

  case 387: /* typeAtom: noreturnType  */
#line 1175 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 6995 "parser.tab.c"
    break;

  case 388: /* typeAtom: rawPointerType  */
#line 1176 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 7001 "parser.tab.c"
    break;

  case 389: /* typeAtom: arrayType  */
#line 1177 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 7007 "parser.tab.c"
    break;

  case 390: /* typeAtom: dynamicArrayType  */
#line 1178 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 7013 "parser.tab.c"
    break;

  case 391: /* typeAtom: sliceType  */
#line 1179 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 7019 "parser.tab.c"
    break;

  case 392: /* typeAtom: mapType  */
#line 1180 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 7025 "parser.tab.c"
    break;

  case 393: /* typeAtom: optionalType  */
#line 1181 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 7031 "parser.tab.c"
    break;

  case 394: /* typeAtom: errorType  */
#line 1182 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 7037 "parser.tab.c"
    break;

  case 395: /* typeAtom: simdType  */
#line 1183 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 7043 "parser.tab.c"
    break;

  case 396: /* typeAtom: complexType  */
#line 1184 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 7049 "parser.tab.c"
    break;

  case 397: /* typeAtom: tensorType  */
#line 1185 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 7055 "parser.tab.c"
    break;

  case 398: /* typeAtom: inferredType  */
#line 1186 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 7061 "parser.tab.c"
    break;

  case 399: /* typeAtom: structType  */
#line 1187 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 7067 "parser.tab.c"
    break;

  case 400: /* typeAtom: enumType  */
#line 1188 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 7073 "parser.tab.c"
    break;

  case 401: /* typeAtom: variantType  */
#line 1189 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 7079 "parser.tab.c"
    break;

  case 402: /* typeAtom: unionType  */
#line 1190 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 7085 "parser.tab.c"
    break;

  case 403: /* typeAtom: bareFunctionType  */
#line 1191 "parser.y"
                          { (yyval.node) = (yyvsp[0].node); }
#line 7091 "parser.tab.c"
    break;

  case 404: /* typeAtom: TYPE  */
#line 1192 "parser.y"
                          { (yyval.node) = type_path(path_single(identifier_node("type", ZL), ZL), ZL); }
#line 7097 "parser.tab.c"
    break;

  case 422: /* type_exprable: TYPE  */
#line 1213 "parser.y"
            { (yyval.node) = type_path(path_single(identifier_node("type", ZL), ZL), ZL); }
#line 7103 "parser.tab.c"
    break;

  case 423: /* typeLiteralExpr: type_exprable  */
#line 1217 "parser.y"
                   { (yyval.node) = (yyvsp[0].node); }
#line 7109 "parser.tab.c"
    break;

  case 424: /* parenthesizedType: LPAREN type_ RPAREN  */
#line 1221 "parser.y"
                         { (yyval.node) = type_paren((yyvsp[-1].node), ZL); }
#line 7115 "parser.tab.c"
    break;

  case 425: /* noreturnType: NORETURN  */
#line 1225 "parser.y"
              { (yyval.node) = type_noreturn(ZL); }
#line 7121 "parser.tab.c"
    break;

  case 426: /* tupleType: LPAREN tupleTypeTail_opt RPAREN  */
#line 1230 "parser.y"
    { (yyval.node) = (yyvsp[-1].node) ? (yyvsp[-1].node) : type_tuple_append(NULL, NULL); }
#line 7127 "parser.tab.c"
    break;

  case 427: /* tupleTypeTail_opt: %empty  */
#line 1234 "parser.y"
                                                   { (yyval.node) = NULL; }
#line 7133 "parser.tab.c"
    break;

  case 428: /* tupleTypeTail_opt: type_ COMMA type_list COMMA_opt  */
#line 1236 "parser.y"
    { AstNode* list = type_tuple_append(NULL, (yyvsp[-3].node));
      AstNode* cur = (yyvsp[-1].node);
      if (cur && cur->type == NODE_TYPE_TUPLE) {
        for (size_t i=0;i<cur->data.tTuple.list.count;i++)
          list = type_tuple_append(list, cur->data.tTuple.list.items[i]);
      } else {
        list = type_tuple_append(list, cur);
      }
      (yyval.node) = list;
    }
#line 7148 "parser.tab.c"
    break;

  case 429: /* arrayType: LSQUAREBRACKET expression RSQUAREBRACKET type_  */
#line 1250 "parser.y"
    { (yyval.node) = type_array((yyvsp[-2].node), (yyvsp[0].node), ZL); }
#line 7154 "parser.tab.c"
    break;

  case 430: /* dynamicArrayType: LSQUAREBRACKET DYN RSQUAREBRACKET type_  */
#line 1255 "parser.y"
    { (yyval.node) = type_dynamic_array((yyvsp[0].node), ZL); }
#line 7160 "parser.tab.c"
    break;

  case 431: /* sliceType: LSQUAREBRACKET RSQUAREBRACKET type_  */
#line 1260 "parser.y"
    { (yyval.node) = type_slice((yyvsp[0].node), ZL); }
#line 7166 "parser.tab.c"
    break;

  case 432: /* mapType: LSQUAREBRACKET type_ COLON type_ RSQUAREBRACKET  */
#line 1265 "parser.y"
    { (yyval.node) = type_map((yyvsp[-3].node), (yyvsp[-1].node), ZL); }
#line 7172 "parser.tab.c"
    break;

  case 433: /* optionalType: QUESTION type_  */
#line 1269 "parser.y"
                     { (yyval.node) = type_optional((yyvsp[0].node), ZL); }
#line 7178 "parser.tab.c"
    break;

  case 434: /* errorType: ERROR LCURLYBRACE variantItems_opt declarations_opt RCURLYBRACE  */
#line 1274 "parser.y"
    { (yyval.node) = type_error((yyvsp[-2].node), (yyvsp[-1].node), ZL); }
#line 7184 "parser.tab.c"
    break;

  case 435: /* structType: STRUCT structTypeTail_opt  */
#line 1279 "parser.y"
    { (yyval.node) = (yyvsp[0].node) ? (yyvsp[0].node) : type_struct(NULL, NULL, ZL); }
#line 7190 "parser.tab.c"
    break;

  case 436: /* structTypeTail_opt: %empty  */
#line 1283 "parser.y"
                 { (yyval.node) = NULL; }
#line 7196 "parser.tab.c"
    break;

  case 437: /* structTypeTail_opt: LCURLYBRACE structFields_opt declarations_opt RCURLYBRACE  */
#line 1285 "parser.y"
    { (yyval.node) = type_struct((yyvsp[-2].node), (yyvsp[-1].node), ZL); }
#line 7202 "parser.tab.c"
    break;

  case 438: /* structFields_opt: %empty  */
#line 1289 "parser.y"
                 { (yyval.node) = NULL; }
#line 7208 "parser.tab.c"
    break;

  case 439: /* structFields_opt: structFields  */
#line 1290 "parser.y"
                 { (yyval.node) = (yyvsp[0].node); }
#line 7214 "parser.tab.c"
    break;

  case 440: /* structFields: structField_list COMMA_opt  */
#line 1294 "parser.y"
                                { (yyval.node) = (yyvsp[-1].node); }
#line 7220 "parser.tab.c"
    break;

  case 441: /* structField_list: structField  */
#line 1298 "parser.y"
                                          { (yyval.node) = type_struct_field_list_append(NULL, (yyvsp[0].node)); }
#line 7226 "parser.tab.c"
    break;

  case 442: /* structField_list: structField_list COMMA structField  */
#line 1299 "parser.y"
                                          { (yyval.node) = type_struct_field_list_append((yyvsp[-2].node), (yyvsp[0].node)); }
#line 7232 "parser.tab.c"
    break;

  case 443: /* structField: attribute_opt PUB_opt identifier COLON type_  */
#line 1304 "parser.y"
    { (yyval.node) = type_struct_field((yyvsp[-4].node), (yyvsp[-3].node) ? 1 : 0, (yyvsp[-2].node), (yyvsp[0].node), ZL); }
#line 7238 "parser.tab.c"
    break;

  case 444: /* PUB_opt: %empty  */
#line 1308 "parser.y"
                 { (yyval.node) = NULL; }
#line 7244 "parser.tab.c"
    break;

  case 445: /* PUB_opt: PUB  */
#line 1309 "parser.y"
                 { (yyval.node) = (AstNode*)1; }
#line 7250 "parser.tab.c"
    break;

  case 446: /* enumType: ENUM parenthesizedType_opt LCURLYBRACE enumItems_opt declarations_opt RCURLYBRACE  */
#line 1314 "parser.y"
    { (yyval.node) = type_enum((yyvsp[-4].node), (yyvsp[-2].node), (yyvsp[-1].node), ZL); }
#line 7256 "parser.tab.c"
    break;

  case 447: /* parenthesizedType_opt: %empty  */
#line 1318 "parser.y"
                     { (yyval.node) = NULL; }
#line 7262 "parser.tab.c"
    break;

  case 448: /* parenthesizedType_opt: parenthesizedType  */
#line 1319 "parser.y"
                     { (yyval.node) = (yyvsp[0].node); }
#line 7268 "parser.tab.c"
    break;

  case 449: /* enumItems_opt: %empty  */
#line 1323 "parser.y"
                 { (yyval.node) = NULL; }
#line 7274 "parser.tab.c"
    break;

  case 450: /* enumItems_opt: enumItems  */
#line 1324 "parser.y"
                 { (yyval.node) = (yyvsp[0].node); }
#line 7280 "parser.tab.c"
    break;

  case 451: /* enumItems: enumItem_list COMMA_opt  */
#line 1328 "parser.y"
                             { (yyval.node) = (yyvsp[-1].node); }
#line 7286 "parser.tab.c"
    break;

  case 452: /* enumItem_list: enumItem  */
#line 1332 "parser.y"
                                    { (yyval.node) = type_enum_item_list_append(NULL, (yyvsp[0].node)); }
#line 7292 "parser.tab.c"
    break;

  case 453: /* enumItem_list: enumItem_list COMMA enumItem  */
#line 1333 "parser.y"
                                    { (yyval.node) = type_enum_item_list_append((yyvsp[-2].node), (yyvsp[0].node)); }
#line 7298 "parser.tab.c"
    break;

  case 454: /* enumItem: attribute_opt PUB_opt identifier enumItemTail_opt  */
#line 1338 "parser.y"
    { (yyval.node) = type_enum_item((yyvsp[-3].node), (yyvsp[-2].node)?1:0, (yyvsp[-1].node), (yyvsp[0].node), ZL); }
#line 7304 "parser.tab.c"
    break;

  case 455: /* enumItemTail_opt: %empty  */
#line 1342 "parser.y"
                            { (yyval.node) = NULL; }
#line 7310 "parser.tab.c"
    break;

  case 456: /* enumItemTail_opt: enumItemDiscriminant  */
#line 1343 "parser.y"
                            { (yyval.node) = (yyvsp[0].node); }
#line 7316 "parser.tab.c"
    break;

  case 457: /* variantType: VARIANT LCURLYBRACE variantItems_opt declarations_opt RCURLYBRACE  */
#line 1348 "parser.y"
    { (yyval.node) = type_variant((yyvsp[-2].node), (yyvsp[-1].node), ZL); }
#line 7322 "parser.tab.c"
    break;

  case 458: /* variantItems_opt: %empty  */
#line 1352 "parser.y"
                 { (yyval.node) = NULL; }
#line 7328 "parser.tab.c"
    break;

  case 459: /* variantItems_opt: variantItems  */
#line 1353 "parser.y"
                 { (yyval.node) = (yyvsp[0].node); }
#line 7334 "parser.tab.c"
    break;

  case 460: /* variantItems: variantItem_list COMMA_opt  */
#line 1357 "parser.y"
                                { (yyval.node) = (yyvsp[-1].node); }
#line 7340 "parser.tab.c"
    break;

  case 461: /* variantItem_list: variantItem  */
#line 1361 "parser.y"
                                         { (yyval.node) = type_variant_item_list_append(NULL, (yyvsp[0].node)); }
#line 7346 "parser.tab.c"
    break;

  case 462: /* variantItem_list: variantItem_list COMMA variantItem  */
#line 1362 "parser.y"
                                         { (yyval.node) = type_variant_item_list_append((yyvsp[-2].node), (yyvsp[0].node)); }
#line 7352 "parser.tab.c"
    break;

  case 463: /* variantItem: attribute_opt PUB_opt identifier variantBody_opt  */
#line 1367 "parser.y"
    { (yyval.node) = type_variant_item((yyvsp[-3].node), (yyvsp[-2].node)?1:0, (yyvsp[-1].node), (yyvsp[0].node), ZL); }
#line 7358 "parser.tab.c"
    break;

  case 464: /* variantBody_opt: %empty  */
#line 1371 "parser.y"
                    { (yyval.node) = NULL; }
#line 7364 "parser.tab.c"
    break;

  case 465: /* variantBody_opt: enumItemStruct  */
#line 1372 "parser.y"
                    { (yyval.node) = (yyvsp[0].node); }
#line 7370 "parser.tab.c"
    break;

  case 466: /* variantBody_opt: enumItemTuple  */
#line 1373 "parser.y"
                    { (yyval.node) = (yyvsp[0].node); }
#line 7376 "parser.tab.c"
    break;

  case 467: /* variantBody_opt: enumItemDiscriminant  */
#line 1374 "parser.y"
                         { (yyval.node) = (yyvsp[0].node); }
#line 7382 "parser.tab.c"
    break;

  case 468: /* enumItemTuple: LPAREN tupleFields_opt RPAREN  */
#line 1379 "parser.y"
    { (yyval.node) = (yyvsp[-1].node) ? (yyvsp[-1].node) : type_tuple_append(NULL, NULL); }
#line 7388 "parser.tab.c"
    break;

  case 469: /* enumItemStruct: LCURLYBRACE structFields_opt RCURLYBRACE  */
#line 1384 "parser.y"
    { (yyval.node) = (yyvsp[-1].node); }
#line 7394 "parser.tab.c"
    break;

  case 470: /* enumItemDiscriminant: EQ expression  */
#line 1388 "parser.y"
                    { (yyval.node) = (yyvsp[0].node); }
#line 7400 "parser.tab.c"
    break;

  case 471: /* tupleFields_opt: %empty  */
#line 1392 "parser.y"
                  { (yyval.node) = NULL; }
#line 7406 "parser.tab.c"
    break;

  case 472: /* tupleFields_opt: tupleFields  */
#line 1393 "parser.y"
                  { (yyval.node) = (yyvsp[0].node); }
#line 7412 "parser.tab.c"
    break;

  case 473: /* tupleFields: tupleField_list COMMA_opt  */
#line 1397 "parser.y"
                               { (yyval.node) = (yyvsp[-1].node); }
#line 7418 "parser.tab.c"
    break;

  case 474: /* tupleField_list: tupleField  */
#line 1401 "parser.y"
                                        { (yyval.node) = type_tuple_append(NULL, (yyvsp[0].node)); }
#line 7424 "parser.tab.c"
    break;

  case 475: /* tupleField_list: tupleField_list COMMA tupleField  */
#line 1402 "parser.y"
                                        { (yyval.node) = type_tuple_append((yyvsp[-2].node), (yyvsp[0].node)); }
#line 7430 "parser.tab.c"
    break;

  case 476: /* tupleField: attribute_opt PUB_opt type_  */
#line 1407 "parser.y"
    { (void)(yyvsp[-2].node); (void)(yyvsp[-1].node); (yyval.node) = (yyvsp[0].node); }
#line 7436 "parser.tab.c"
    break;

  case 477: /* unionType: UNION LCURLYBRACE structFields_opt declarations_opt RCURLYBRACE  */
#line 1412 "parser.y"
    { (yyval.node) = type_union((yyvsp[-2].node), (yyvsp[-1].node), ZL); }
#line 7442 "parser.tab.c"
    break;

  case 478: /* simdType: SIMD LPAREN expression COMMA type_ RPAREN  */
#line 1417 "parser.y"
    { (yyval.node) = type_simd((yyvsp[-3].node), (yyvsp[-1].node), ZL); }
#line 7448 "parser.tab.c"
    break;

  case 479: /* complexType: COMPLEX LPAREN type_ RPAREN  */
#line 1422 "parser.y"
    { (yyval.node) = type_complex((yyvsp[-1].node), ZL); }
#line 7454 "parser.tab.c"
    break;

  case 480: /* tensorType: TENSOR LPAREN tensorDims COMMA type_ RPAREN  */
#line 1427 "parser.y"
    { (yyvsp[-3].node)->data.tTensor.elem = (yyvsp[-1].node); (yyval.node) = (yyvsp[-3].node); }
#line 7460 "parser.tab.c"
    break;

  case 481: /* tensorDims: INTEGER_LITERAL  */
#line 1432 "parser.y"
    { AstNode* t = type_tensor_new(NULL, ZL);
      t = type_tensor_dims_append(t, literal_node(NODE_INTEGER_LITERAL, (yyvsp[0].str), ZL));
      (yyval.node) = t;
    }
#line 7469 "parser.tab.c"
    break;

  case 482: /* tensorDims: tensorDims COMMA INTEGER_LITERAL  */
#line 1437 "parser.y"
    { (yyval.node) = type_tensor_dims_append((yyvsp[-2].node), literal_node(NODE_INTEGER_LITERAL, (yyvsp[0].str), ZL)); }
#line 7475 "parser.tab.c"
    break;

  case 483: /* tensorDims: tensorDims COMMA  */
#line 1439 "parser.y"
    { (yyval.node) = (yyvsp[-1].node); }
#line 7481 "parser.tab.c"
    break;

  case 484: /* rawPointerType: STAR CONST_opt type_  */
#line 1444 "parser.y"
    { (yyval.node) = type_raw_pointer((yyvsp[-1].node)?1:0, (yyvsp[0].node), ZL); }
#line 7487 "parser.tab.c"
    break;

  case 485: /* CONST_opt: %empty  */
#line 1448 "parser.y"
                 { (yyval.node) = NULL; }
#line 7493 "parser.tab.c"
    break;

  case 486: /* CONST_opt: CONST  */
#line 1449 "parser.y"
                 { (yyval.node) = (AstNode*)1; }
#line 7499 "parser.tab.c"
    break;

  case 487: /* bareFunctionType: functionTypeQualifiers FN LPAREN functionParametersMaybeNamedVariadic_opt RPAREN type_opt  */
#line 1454 "parser.y"
    { (yyval.node) = type_bare_function((yyvsp[-5].node), (yyvsp[-2].node), (yyvsp[0].node), ZL); }
#line 7505 "parser.tab.c"
    break;

  case 488: /* functionTypeQualifiers: extern_opt  */
#line 1458 "parser.y"
               { (yyval.node) = (yyvsp[0].node); }
#line 7511 "parser.tab.c"
    break;

  case 489: /* abi: STRING_LITERAL  */
#line 1462 "parser.y"
                        { (yyval.node) = abi_node((yyvsp[0].str), ZL); }
#line 7517 "parser.tab.c"
    break;

  case 490: /* abi: RAW_STRING_LITERAL  */
#line 1463 "parser.y"
                        { (yyval.node) = abi_node((yyvsp[0].str), ZL); }
#line 7523 "parser.tab.c"
    break;

  case 491: /* functionParametersMaybeNamedVariadic_opt: %empty  */
#line 1467 "parser.y"
                                        { (yyval.node) = NULL; }
#line 7529 "parser.tab.c"
    break;

  case 492: /* functionParametersMaybeNamedVariadic_opt: functionParametersMaybeNamedVariadic  */
#line 1468 "parser.y"
                                        { (yyval.node) = (yyvsp[0].node); }
#line 7535 "parser.tab.c"
    break;

  case 493: /* functionParametersMaybeNamedVariadic: maybeNamedFunctionParameters  */
#line 1472 "parser.y"
                                            { (yyval.node) = (yyvsp[0].node); }
#line 7541 "parser.tab.c"
    break;

  case 494: /* functionParametersMaybeNamedVariadic: maybeNamedFunctionParametersVariadic  */
#line 1473 "parser.y"
                                            { (yyval.node) = (yyvsp[0].node); }
#line 7547 "parser.tab.c"
    break;

  case 495: /* maybeNamedFunctionParameters: maybeNamedParam_list COMMA_opt  */
#line 1477 "parser.y"
                                    { (yyval.node) = (yyvsp[-1].node); }
#line 7553 "parser.tab.c"
    break;

  case 496: /* maybeNamedParam_list: maybeNamedParam  */
#line 1481 "parser.y"
                                               { (yyval.node) = type_maybe_named_param_list_append(type_maybe_named_param_list_new(ZL), (yyvsp[0].node)); }
#line 7559 "parser.tab.c"
    break;

  case 497: /* maybeNamedParam_list: maybeNamedParam_list COMMA maybeNamedParam  */
#line 1482 "parser.y"
                                               { (yyval.node) = type_maybe_named_param_list_append((yyvsp[-2].node), (yyvsp[0].node)); }
#line 7565 "parser.tab.c"
    break;

  case 498: /* maybeNamedParam: attribute_opt maybeName_opt type_  */
#line 1487 "parser.y"
    { (yyval.node) = type_maybe_named_param((yyvsp[-2].node), (yyvsp[-1].mname).name, (yyvsp[-1].mname).is_underscore, (yyvsp[0].node), ZL); }
#line 7571 "parser.tab.c"
    break;

  case 499: /* maybeName_opt: %empty  */
#line 1491 "parser.y"
                                { (yyval.mname) = (MaybeName){ NULL, 0 }; }
#line 7577 "parser.tab.c"
    break;

  case 500: /* maybeName_opt: identifier COLON  */
#line 1492 "parser.y"
                                { (yyval.mname) = (MaybeName){ (yyvsp[-1].node), 0 }; }
#line 7583 "parser.tab.c"
    break;

  case 501: /* maybeName_opt: UNDERSCORE COLON  */
#line 1493 "parser.y"
                                { (yyval.mname) = (MaybeName){ NULL, 1 }; }
#line 7589 "parser.tab.c"
    break;

  case 502: /* maybeNamedFunctionParametersVariadic: maybeNamedParam_list COMMA attribute_opt DOTDOTDOT  */
#line 1498 "parser.y"
    { AstNode* list = (yyvsp[-3].node) ? (yyvsp[-3].node) : type_maybe_named_param_list_new(ZL);
      (yyval.node) = type_maybe_named_param_list_set_variadic(list, (yyvsp[-1].node));
    }
#line 7597 "parser.tab.c"
    break;

  case 503: /* inferredType: ANY  */
#line 1504 "parser.y"
          { (yyval.node) = type_inferred(ZL); }
#line 7603 "parser.tab.c"
    break;

  case 504: /* path: identifier  */
#line 1512 "parser.y"
                              { (yyval.node) = path_single((yyvsp[0].node), ZL); }
#line 7609 "parser.tab.c"
    break;

  case 505: /* path: path DOT identifier  */
#line 1513 "parser.y"
                              { (yyval.node) = path_append((yyvsp[-2].node), (yyvsp[0].node)); }
#line 7615 "parser.tab.c"
    break;

  case 506: /* path_ndot: identifier DOT identifier  */
#line 1517 "parser.y"
                              { (yyval.node) = path_append(path_single((yyvsp[-2].node), ZL), (yyvsp[0].node)); }
#line 7621 "parser.tab.c"
    break;

  case 507: /* path_ndot: path_ndot DOT identifier  */
#line 1518 "parser.y"
                              { (yyval.node) = path_append((yyvsp[-2].node), (yyvsp[0].node)); }
#line 7627 "parser.tab.c"
    break;

  case 508: /* expression_list: expression  */
#line 1526 "parser.y"
                                        { (yyval.node) = expr_list_append(NULL, (yyvsp[0].node)); }
#line 7633 "parser.tab.c"
    break;

  case 509: /* expression_list: expression_list COMMA expression  */
#line 1527 "parser.y"
                                        { (yyval.node) = expr_list_append((yyvsp[-2].node), (yyvsp[0].node)); }
#line 7639 "parser.tab.c"
    break;

  case 510: /* pattern_list: pattern  */
#line 1531 "parser.y"
                                    { (yyval.node) = expr_list_append(NULL, (yyvsp[0].node)); }
#line 7645 "parser.tab.c"
    break;

  case 511: /* pattern_list: pattern_list COMMA pattern  */
#line 1532 "parser.y"
                                    { (yyval.node) = expr_list_append((yyvsp[-2].node), (yyvsp[0].node)); }
#line 7651 "parser.tab.c"
    break;

  case 512: /* type_list: type_  */
#line 1536 "parser.y"
                               { (yyval.node) = type_tuple_append(NULL, (yyvsp[0].node)); }
#line 7657 "parser.tab.c"
    break;

  case 513: /* type_list: type_list COMMA type_  */
#line 1537 "parser.y"
                               { (yyval.node) = type_tuple_append((yyvsp[-2].node), (yyvsp[0].node)); }
#line 7663 "parser.tab.c"
    break;

  case 514: /* COMMA_opt: %empty  */
#line 1541 "parser.y"
                { (yyval.node) = NULL; }
#line 7669 "parser.tab.c"
    break;

  case 515: /* COMMA_opt: COMMA  */
#line 1542 "parser.y"
                { (yyval.node) = NULL; }
#line 7675 "parser.tab.c"
    break;


#line 7679 "parser.tab.c"

      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", YY_CAST (yysymbol_kind_t, yyr1[yyn]), &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;

  *++yyvsp = yyval;
  *++yylsp = yyloc;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */
  {
    const int yylhs = yyr1[yyn] - YYNTOKENS;
    const int yyi = yypgoto[yylhs] + *yyssp;
    yystate = (0 <= yyi && yyi <= YYLAST && yycheck[yyi] == *yyssp
               ? yytable[yyi]
               : yydefgoto[yylhs]);
  }

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYSYMBOL_YYEMPTY : YYTRANSLATE (yychar);
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
      {
        yypcontext_t yyctx
          = {yyssp, yytoken, &yylloc};
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = yysyntax_error (&yymsg_alloc, &yymsg, &yyctx);
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == -1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = YY_CAST (char *,
                             YYSTACK_ALLOC (YY_CAST (YYSIZE_T, yymsg_alloc)));
            if (yymsg)
              {
                yysyntax_error_status
                  = yysyntax_error (&yymsg_alloc, &yymsg, &yyctx);
                yymsgp = yymsg;
              }
            else
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = YYENOMEM;
              }
          }
        yyerror (yymsgp);
        if (yysyntax_error_status == YYENOMEM)
          YYNOMEM;
      }
    }

  yyerror_range[1] = yylloc;
  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval, &yylloc);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:
  /* Pacify compilers when the user code never invokes YYERROR and the
     label yyerrorlab therefore never appears in user code.  */
  if (0)
    YYERROR;
  ++yynerrs;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  /* Pop stack until we find a state that shifts the error token.  */
  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYSYMBOL_YYerror;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYSYMBOL_YYerror)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;

      yyerror_range[1] = *yylsp;
      yydestruct ("Error: popping",
                  YY_ACCESSING_SYMBOL (yystate), yyvsp, yylsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  yyerror_range[2] = yylloc;
  ++yylsp;
  YYLLOC_DEFAULT (*yylsp, yyerror_range, 2);

  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", YY_ACCESSING_SYMBOL (yyn), yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturnlab;


/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturnlab;


/*-----------------------------------------------------------.
| yyexhaustedlab -- YYNOMEM (memory exhaustion) comes here.  |
`-----------------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  goto yyreturnlab;


/*----------------------------------------------------------.
| yyreturnlab -- parsing is finished, clean up and return.  |
`----------------------------------------------------------*/
yyreturnlab:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval, &yylloc);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  YY_ACCESSING_SYMBOL (+*yyssp), yyvsp, yylsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
  return yyresult;
}

#line 1545 "parser.y"


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

