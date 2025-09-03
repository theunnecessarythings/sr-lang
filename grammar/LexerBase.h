#pragma once

#include "antlr4-runtime.h"

class LexerBase : public antlr4::Lexer {
  size_t lt1;
  size_t lt2;

public:
  LexerBase(antlr4::CharStream *input)
      : Lexer(input), lt1(antlr4::Token::INVALID_TYPE),
        lt2(antlr4::Token::INVALID_TYPE) {}

  virtual ~LexerBase() {}

  std::unique_ptr<antlr4::Token> nextToken() override {
    std::unique_ptr<antlr4::Token> next = antlr4::Lexer::nextToken();

    if (next->getChannel() == antlr4::Token::DEFAULT_CHANNEL) {
      // Keep track of the last token on the default channel.
      this->lt2 = this->lt1;
      this->lt1 = next->getType();
    }

    return next;
  }

  bool SOF() {
    size_t next = _input->LA(-1);
    return next == 0 || next == antlr4::Token::EOF;
  }

  bool next(char expect) { return _input->LA(1) == expect; }

  bool floatDotPossible() {
    size_t next = _input->LA(1);
    // only block . _ identifier after float
    if (next == '.' || next == '_')
      return false;
    if (next == 'f') {
      // 1.f32
      if (_input->LA(2) == '3' && _input->LA(3) == '2')
        return true;
      // 1.f64
      if (_input->LA(2) == '6' && _input->LA(3) == '4')
        return true;
      return false;
    }
    if (next >= 'a' && next <= 'z')
      return false;
    if (next >= 'A' && next <= 'Z')
      return false;
    return true;
  }

  bool floatLiteralPossible() {
    if (this->lt1 == antlr4::Token::INVALID_TYPE ||
        this->lt2 == antlr4::Token::INVALID_TYPE)
      return true;
    if (this->lt1 != Lexer::DOT)
      return true;
    switch (this->lt2) {
    case Lexer::CHAR_LITERAL:
    case Lexer::STRING_LITERAL:
    case Lexer::RAW_STRING_LITERAL:
    case Lexer::BYTE_LITERAL:
    case Lexer::BYTE_STRING_LITERAL:
    case Lexer::RAW_BYTE_STRING_LITERAL:
    case Lexer::INTEGER_LITERAL:
    case Lexer::DEC_LITERAL:
    case Lexer::HEX_LITERAL:
    case Lexer::OCT_LITERAL:
    case Lexer::BIN_LITERAL:

    case Lexer::GT:
    case Lexer::RCURLYBRACE:
    case Lexer::RSQUAREBRACKET:
    case Lexer::RPAREN:

    case Lexer::NON_KEYWORD_IDENTIFIER:
    case Lexer::RAW_IDENTIFIER:
      return false;
    default:
      return true;
    }
  }
};
