/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
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


namespace Shell {

/**
 * Class LispLexer, implements a LispLexer.
 * @since 25/08/2009 Redmond
 */
class LispLexer 
  : public Lexer
{
public:
  LispLexer(std::istream& in);
  void readToken (Token&);
  ~LispLexer () {}

private:
  void skipWhiteSpacesAndComments();
  void readName(Token&);
  void readQuotedString(Token&, char opening, char closing, char escape);
}; // class LispLexer

}

#endif

