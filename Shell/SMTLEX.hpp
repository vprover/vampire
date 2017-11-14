
/*
 * File SMTLEX.hpp.
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
 * @file SMTLEX.hpp
 * Defines class SMTLexer for lexical analysis of SMT files.
 *
 * @since 20/01/2009 Manchester
 */

#ifndef __SMTLEX__
#define __SMTLEX__

#include <iostream>
#include "Lexer.hpp"

using namespace std;

namespace Shell {

/**
 * Class SMTLexer, implements a SMT SMTLexer.
 * @since 14/07/2004 Turku
 * @since 01/08/2004 Torrevieja, made derived from Lexer
 */
class SMTLexer 
  : public Lexer
{
public:
  SMTLexer(istream& in);
  void readToken (Token&);
  ~SMTLexer () {}

private:

  /** Character type */
  enum CharType {
    /** letter A-Z,a-z,_, and ' */
    LETTER,
    /** digit 0-9 */
    DIGIT,
    /** Dot "." */
    DOT,
    /** Colon ":" */
    COLON,
    /** Brace "{" */
    BRACE,
    /** whitespace character */
    WHITE,
    /** character that forms a token by itself, one of '(){}' */
    PAR,
    /** arithmetic symbols =, &lt;, &gt;, &, @, #, +, -, *, /, %, |, ~ */
    ARITH
  };

  void skipWhiteSpacesAndComments();
  void readName(Token&);
  void readArith(Token&);
//   void readSymbolic(Token&);
  void readPar(Token&);
  void readUserValue(Token&);
//   TokenType detectNameTokenTypeOfLastToken();
//   TokenType detectSymbolicTokenTypeOfLastToken();
  CharType currentCharacterType() const;
}; // class SMTLexer

}

#endif

