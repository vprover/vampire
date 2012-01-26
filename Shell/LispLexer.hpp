/**
 * @file LispLexer.hpp
 * Defines class LispLexer for lexical analysis of LISP files
 *
 * @since 25/08/2009 Redmond
 */

#ifndef __LispLexer__
#define __LispLexer__

#include <iostream>
#include "Lexer.hpp"

using namespace std;

namespace Shell {

/**
 * Class LispLexer, implements a LispLexer.
 * @since 25/08/2009 Redmond
 */
class LispLexer 
  : public Lexer
{
public:
  LispLexer(istream& in);
  void readToken (Token&);
  ~LispLexer () {}

private:
  void skipWhiteSpacesAndComments();
  void readName(Token&);
  void readQuotedString(Token&, char opening, char closing);
}; // class LispLexer

}

#endif

