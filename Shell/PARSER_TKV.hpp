
/*
 * File PARSER_TKV.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Parser_TKV.hpp
 * Defines class Parser for generic top-down parsers.
 *
 * @since 17/07/2004 Helsinki airport
 */

#ifndef __Parser__
#define __Parser__

#include "Lib/DHMap.hpp"
#include "Lib/IntNameTable.hpp"
#include "Lib/Exception.hpp"
#include "Lib/XML.hpp"

#include "Token.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;

#define TOKEN_BUFFER_SIZE 3

namespace Shell {

class Lexer;

/**
 * Class ParserException. Implements parser exceptions.
 * @since 17/07/2004 Helsinki airport
 */
class ParserException 
  : public Exception
{
 public:                                
  ParserException (vstring message,const Token&);
  void cry (ostream&);
  XMLElement toXML () const;
  ~ParserException () {}
 protected:
  vstring _message;
}; // ParserException

/**
 * Class Parser, implements a TPTP Parser.
 *
 * @since 17/07/2004 Helsinki airport
 */
class Parser 
{
public:
  Parser(Lexer& lexer);
protected:
  /** The lexer which supplies tokens */
  Lexer& _lexer;
  /** The ring of tokens */
  Token _tokens[TOKEN_BUFFER_SIZE];
  /** cursor to the current token */
  int _tokenCursor;
  /** number of tokens */
  int _noOfTokens;
  /** name table for variable names */
  IntNameTable _vars;

  void consumeToken();
  void consumeToken(TokenType);
  void expectToken(TokenType);
  void expectKeyword(const char* keyword);
  void readToken();
  void readToken(TokenType);
  Token& lookAhead (int lookahead);
  Token& currentToken();
  void consumeToken(TokenType,vstring errorMessage);
  void expectToken(TokenType,vstring errorMessage);
  void readToken(TokenType,vstring errorMessage);
  void terminate(vstring errorMessage) __attribute__((noreturn));
  /**
   * If there are no tokens in the buffer, read one.
   * Then return the current token.
   * @since 31/12/2006 Manchester
   */
  inline
  Token& currentToken1()
  {
    if (_noOfTokens == 0) {
      readToken();
    }

    return currentToken();
  } // currentToken1
  int var(const Token& t);
  static double real(const Token& t);
  static int integer(const Token& t);
  static long long unsigned unsigned64(const Token& t);
}; // class Parser

}

#endif

