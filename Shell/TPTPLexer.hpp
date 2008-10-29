/**
 * @file TPTPLexer.hpp
 * Defines class TPTPLexer for lexical analysis of TPTP files.
 *
 * @since 14/07/2004 Turku
 */

#ifndef __TPTPLexer__
#define __TPTPLexer__

#include <iostream>
#include "Lexer.hpp"

using namespace std;

namespace Shell {

/**
 * Class TPTPLexer, implements a TPTP TPTPLexer.
 * @since 14/07/2004 Turku
 * @since 01/08/2004 Torrevieja, made derived from Lexer
 */
class TPTPLexer 
  : public Lexer
{
public:
  TPTPLexer(istream& in);
  void readToken (Token&);
  ~TPTPLexer () {}

private:

  /** Character type */
  enum CharType {
    /** upper-case letter A-Z or _ */
    UPPER_CASE_LETTER,
    /** lower-case letter a-z */
    LOWER_CASE_LETTER,
    /** digit 0-9 */
    DIGIT,
    /** symbolic character */
    SYMBOLIC,
    /** Quote character "'" */
    QUOTE,
    /** whitespace character */
    WHITE,
    /** character that forms a token by itself, one of '()[],' */
    SINGLE,
    /** any other legal character, e.g. '%' */
    OTHER
  };

  void skipWhiteSpacesAndComments();
  CharType currentCharacterType() const;
  void readName(Token&);
  void readSymbolic(Token&);
  void readSingle(Token&);
  void readQuotedString(Token&);
  TokenType detectNameTokenTypeOfLastToken();
  TokenType detectSymbolicTokenTypeOfLastToken();
}; // class TPTPLexer

}

#endif

