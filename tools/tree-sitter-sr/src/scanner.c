#include <stdbool.h>
#include <stddef.h>
#include <tree_sitter/parser.h>

enum TokenType {
  BLOCK_COMMENT,
};

void *tree_sitter_sr_external_scanner_create(void) {
  return NULL;
}

void tree_sitter_sr_external_scanner_destroy(void *payload) {
}

void tree_sitter_sr_external_scanner_reset(void *payload) {
}

unsigned tree_sitter_sr_external_scanner_serialize(void *payload, char *buffer) {
  return 0;
}

void tree_sitter_sr_external_scanner_deserialize(void *payload, const char *buffer, unsigned length) {
}

bool tree_sitter_sr_external_scanner_scan(void *payload, TSLexer *lexer, const bool *valid_symbols) {
  if (!valid_symbols[BLOCK_COMMENT]) {
    return false;
  }

  if (lexer->lookahead != '/') {
    return false;
  }
  lexer->advance(lexer, false);
  if (lexer->lookahead != '*') {
    return false;
  }
  lexer->advance(lexer, false);

  unsigned depth = 1;
  for (;;) {
    switch (lexer->lookahead) {
      case '\0':
        return false;
      case '/':
        lexer->advance(lexer, false);
        if (lexer->lookahead == '*') {
          lexer->advance(lexer, false);
          depth++;
        }
        break;
      case '*':
        lexer->advance(lexer, false);
        if (lexer->lookahead == '/') {
          lexer->advance(lexer, false);
          depth--;
          if (depth == 0) {
            lexer->mark_end(lexer);
            lexer->result_symbol = BLOCK_COMMENT;
            return true;
          }
        }
        break;
      case '\n':
        lexer->advance(lexer, true);
        break;
      default:
        lexer->advance(lexer, false);
        break;
    }
  }
}
