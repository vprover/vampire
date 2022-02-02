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
 * @file Shell/Lexer.hpp
 * Defines class Lexer for lexical analysis of KIF files.
 *
 * @since 27/07/2004 Torrevieja
 */

#ifndef __Lexer__
#define __Lexer__

#include <iostream>

#include "Lib/Array.hpp"
#include "Lib/Exception.hpp"

#include "Token.hpp"

using namespace std;
using namespace Lib;


namespace Shell {

class Lexer;

/**
 * Class LexerException. Implements lexer exceptions.
 * @since 14/07/2004 Turku
 */
class LexerException 
  : public Exception
{
 public:                                
  LexerException(vstring message,const Lexer&);
  void cry(ostream&) const;
  ~LexerException() {}
 protected:
  vstring _message;
}; // LexerException


/**
 * Class Lexer, implements a generic lexer.
 * @since 27/07/2004 Torrevieja
 */
class Lexer 
{
public:
  Lexer(istream& in);
  /** True if the lexer is at the end of file */
  bool isAtEndOfFile () const { return _eof; }
  /** Return the last character */
  int lastCharacter () const { return _lastCharacter; }
  /** Return the current line number */
  int lineNumber () const { return _lineNumber; }
  virtual void readToken (Token&) = 0;
  virtual ~Lexer () {}
  int lookAhead();

protected:
  /** Last read character */
  int  _lastCharacter;
  /** Character buffer, used to store currently read token */
  Array<char> _charBuffer;
  /** cursor to the current character */
  int _charCursor;
  /** the input stream */
  std::istream& _stream;
  /** true if end-of-file is reached */
  bool _eof;
  /** current line number, counting from 1 */
  int _lineNumber;
  /** lookahead character. In this implementation there may be only one */
  int _lookAheadChar;

  bool readNextChar();
  void readNumber(Token&);
  void readUnsignedInteger();
  void saveLastChar();
  void saveChar(int character);
  void saveTokenText(Token&);
  /** True if the character with this code is a digit */
  static bool isDigit(int charCode) 
  { return charCode >= '0' && charCode <= '9'; }
  /** True if the character with this code is a letter */
  static bool isLetter(int charCode) 
  { return (charCode >= 'A' && charCode <= 'Z') || 
           (charCode >= 'a' && charCode <= 'z'); }
  void readSequence(const char* chars);
}; // class Lexer

}

#endif

