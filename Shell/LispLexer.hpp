
/*
 * File LispLexer.hpp.
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
  void readQuotedString(Token&, char opening, char closing, char escape);
}; // class LispLexer

}

#endif

