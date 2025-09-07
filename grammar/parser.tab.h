/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison interface for Yacc-like parsers in C

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

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

#ifndef YY_YY_PARSER_TAB_H_INCLUDED
# define YY_YY_PARSER_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 1
#endif
#if YYDEBUG
extern int yydebug;
#endif
/* "%code requires" blocks.  */
#line 21 "parser.y"

  #include "ast.h"
  typedef struct { AstNode* name; int is_underscore; } MaybeName;

#line 54 "parser.tab.h"

/* Token kinds.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    YYEMPTY = -2,
    YYEOF = 0,                     /* "end of file"  */
    YYerror = 256,                 /* error  */
    YYUNDEF = 257,                 /* "invalid token"  */
    ALIGN = 258,                   /* ALIGN  */
    AND = 259,                     /* AND  */
    ANY = 260,                     /* ANY  */
    AS = 261,                      /* AS  */
    ASM = 262,                     /* ASM  */
    ASYNC = 263,                   /* ASYNC  */
    AWAIT = 264,                   /* AWAIT  */
    BREAK = 265,                   /* BREAK  */
    CATCH = 266,                   /* CATCH  */
    COMPTIME = 267,                /* COMPTIME  */
    CODE = 268,                    /* CODE  */
    COMPLEX = 269,                 /* COMPLEX  */
    CONST = 270,                   /* CONST  */
    CONTINUE = 271,                /* CONTINUE  */
    DYN = 272,                     /* DYN  */
    DEFER = 273,                   /* DEFER  */
    ELSE = 274,                    /* ELSE  */
    ENUM = 275,                    /* ENUM  */
    ERRDEFER = 276,                /* ERRDEFER  */
    ERROR = 277,                   /* ERROR  */
    EXPORT = 278,                  /* EXPORT  */
    EXTERN = 279,                  /* EXTERN  */
    FALSE = 280,                   /* FALSE  */
    FN = 281,                      /* FN  */
    FOR = 282,                     /* FOR  */
    IF = 283,                      /* IF  */
    IN = 284,                      /* IN  */
    IS = 285,                      /* IS  */
    INSERT = 286,                  /* INSERT  */
    IMPORT = 287,                  /* IMPORT  */
    MATCH = 288,                   /* MATCH  */
    MLIR = 289,                    /* MLIR  */
    NORETURN = 290,                /* NORETURN  */
    NULL_KW = 291,                 /* NULL_KW  */
    OPAQUE = 292,                  /* OPAQUE  */
    OR = 293,                      /* OR  */
    ORELSE = 294,                  /* ORELSE  */
    PACKAGE = 295,                 /* PACKAGE  */
    PROC = 296,                    /* PROC  */
    PUB = 297,                     /* PUB  */
    RETURN = 298,                  /* RETURN  */
    LINKSECTION = 299,             /* LINKSECTION  */
    SIMD = 300,                    /* SIMD  */
    STRUCT = 301,                  /* STRUCT  */
    THREADLOCAL = 302,             /* THREADLOCAL  */
    TENSOR = 303,                  /* TENSOR  */
    TEST = 304,                    /* TEST  */
    TRUE = 305,                    /* TRUE  */
    TYPE = 306,                    /* TYPE  */
    TYPEOF = 307,                  /* TYPEOF  */
    UNION = 308,                   /* UNION  */
    UNDEFINED = 309,               /* UNDEFINED  */
    UNREACHABLE = 310,             /* UNREACHABLE  */
    VARIANT = 311,                 /* VARIANT  */
    WHILE = 312,                   /* WHILE  */
    PLUS = 313,                    /* PLUS  */
    MINUS = 314,                   /* MINUS  */
    STAR = 315,                    /* STAR  */
    SLASH = 316,                   /* SLASH  */
    PERCENT = 317,                 /* PERCENT  */
    CARET = 318,                   /* CARET  */
    BANG = 319,                    /* BANG  */
    B_AND = 320,                   /* B_AND  */
    B_OR = 321,                    /* B_OR  */
    SHL = 322,                     /* SHL  */
    SHR = 323,                     /* SHR  */
    PLUSEQ = 324,                  /* PLUSEQ  */
    MINUSEQ = 325,                 /* MINUSEQ  */
    RARROW = 326,                  /* RARROW  */
    STAREQ = 327,                  /* STAREQ  */
    SLASHEQ = 328,                 /* SLASHEQ  */
    PERCENTEQ = 329,               /* PERCENTEQ  */
    CARETEQ = 330,                 /* CARETEQ  */
    ANDEQ = 331,                   /* ANDEQ  */
    OREQ = 332,                    /* OREQ  */
    SHLEQ = 333,                   /* SHLEQ  */
    SHREQ = 334,                   /* SHREQ  */
    SHLPIPE = 335,                 /* SHLPIPE  */
    SHLPIPEEQ = 336,               /* SHLPIPEEQ  */
    PLUSPIPE = 337,                /* PLUSPIPE  */
    PLUSPIPEEQ = 338,              /* PLUSPIPEEQ  */
    MINUSPIPE = 339,               /* MINUSPIPE  */
    MINUSPIPEEQ = 340,             /* MINUSPIPEEQ  */
    STARPIPE = 341,                /* STARPIPE  */
    STARPIPEEQ = 342,              /* STARPIPEEQ  */
    PIPEPIPE = 343,                /* PIPEPIPE  */
    PLUSPERCENT = 344,             /* PLUSPERCENT  */
    PLUSPERCENTEQ = 345,           /* PLUSPERCENTEQ  */
    MINUSPERCENT = 346,            /* MINUSPERCENT  */
    MINUSPERCENTEQ = 347,          /* MINUSPERCENTEQ  */
    STARPERCENT = 348,             /* STARPERCENT  */
    STARPERCENTEQ = 349,           /* STARPERCENTEQ  */
    EQ = 350,                      /* EQ  */
    EQEQ = 351,                    /* EQEQ  */
    NE = 352,                      /* NE  */
    GT = 353,                      /* GT  */
    LT = 354,                      /* LT  */
    GE = 355,                      /* GE  */
    LE = 356,                      /* LE  */
    AT = 357,                      /* AT  */
    UNDERSCORE = 358,              /* UNDERSCORE  */
    DOT = 359,                     /* DOT  */
    DOTDOT = 360,                  /* DOTDOT  */
    DOTSTAR = 361,                 /* DOTSTAR  */
    DOTDOTDOT = 362,               /* DOTDOTDOT  */
    DOTDOTEQ = 363,                /* DOTDOTEQ  */
    DOTLPAREN = 364,               /* DOTLPAREN  */
    DOTLSQUAREBRACKET = 365,       /* DOTLSQUAREBRACKET  */
    DOTLCURLYBRACE = 366,          /* DOTLCURLYBRACE  */
    COMMA = 367,                   /* COMMA  */
    SEMI = 368,                    /* SEMI  */
    COLON = 369,                   /* COLON  */
    COLONCOLON = 370,              /* COLONCOLON  */
    COLONEQ = 371,                 /* COLONEQ  */
    FATARROW = 372,                /* FATARROW  */
    QUESTION = 373,                /* QUESTION  */
    LCURLYBRACE = 374,             /* LCURLYBRACE  */
    RCURLYBRACE = 375,             /* RCURLYBRACE  */
    LSQUAREBRACKET = 376,          /* LSQUAREBRACKET  */
    RSQUAREBRACKET = 377,          /* RSQUAREBRACKET  */
    LPAREN = 378,                  /* LPAREN  */
    RPAREN = 379,                  /* RPAREN  */
    POUND = 380,                   /* POUND  */
    EOS = 381,                     /* EOS  */
    RAW_ASM_BLOCK = 382,           /* RAW_ASM_BLOCK  */
    NON_KEYWORD_IDENTIFIER = 383,  /* NON_KEYWORD_IDENTIFIER  */
    RAW_IDENTIFIER = 384,          /* RAW_IDENTIFIER  */
    CHAR_LITERAL = 385,            /* CHAR_LITERAL  */
    STRING_LITERAL = 386,          /* STRING_LITERAL  */
    RAW_STRING_LITERAL = 387,      /* RAW_STRING_LITERAL  */
    BYTE_LITERAL = 388,            /* BYTE_LITERAL  */
    BYTE_STRING_LITERAL = 389,     /* BYTE_STRING_LITERAL  */
    RAW_BYTE_STRING_LITERAL = 390, /* RAW_BYTE_STRING_LITERAL  */
    INTEGER_LITERAL = 391,         /* INTEGER_LITERAL  */
    FLOAT_LITERAL = 392,           /* FLOAT_LITERAL  */
    IMAGINARY_LITERAL = 393,       /* IMAGINARY_LITERAL  */
    UREF = 394,                    /* UREF  */
    UMINUS_UBANG = 395             /* UMINUS_UBANG  */
  };
  typedef enum yytokentype yytoken_kind_t;
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
union YYSTYPE
{
#line 26 "parser.y"

  char*       str;
  AstNode*    node;
  Op          op;
  int         ival;
  MaybeName   mname;

#line 219 "parser.tab.h"

};
typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif

/* Location type.  */
#if ! defined YYLTYPE && ! defined YYLTYPE_IS_DECLARED
typedef struct YYLTYPE YYLTYPE;
struct YYLTYPE
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
};
# define YYLTYPE_IS_DECLARED 1
# define YYLTYPE_IS_TRIVIAL 1
#endif


extern YYSTYPE yylval;
extern YYLTYPE yylloc;

int yyparse (void);


#endif /* !YY_YY_PARSER_TAB_H_INCLUDED  */
