/**
 * @file Parser.hpp
 * Defines class Parser for generic top-down parsers.
 *
 * @since 17/07/2004 Helsinki airport
 */

#ifndef __Parser__
#define __Parser__

#include "../Lib/IntNameTable.hpp"
#include "../Lib/Exception.hpp"
#include "../Lib/XML.hpp"

#include "../Kernel/Unit.hpp"

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
  ParserException (string message,const Token&);
  void cry (ostream&);
  XMLElement toXML () const;
  ~ParserException () {}
 protected:
  string _message;
}; // ParserException

/**
 * Class Parser, implements a TPTP Parser.
 *
 * @since 17/07/2004 Helsinki airport
 */
class Parser 
{
public:
  Parser (Lexer& lexer);
  UnitList* units();

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

  void consumeToken ();
  void consumeToken (TokenType);
  void expectToken (TokenType);
  void readToken ();
  Token& lookAhead (int lookahead);
  Token& currentToken ();
  /**
   * If there are no tokens in the buffer, read one.
   * Then return the current token.
   * @since 31/12/2006 Manchester
   */
  inline
  Token& currentToken1 ()
  {
    if (_noOfTokens == 0) {
      readToken();
    }

    return currentToken();
  } // currentToken1
  int var (const Token& t);
  static double real (const Token& t);
  static int integer (const Token& t);
  static long long unsigned unsigned64 (const Token& t);
}; // class Parser

}

#endif

