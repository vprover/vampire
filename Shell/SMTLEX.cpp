
/*
 * File SMTLEX.cpp.
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
 * @file SMTLEX.cpp
 * Implements class SMTLexer
 *
 * @since 20/01/2009 Manchester
 */

#include <cstring>

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"
#include "Lib/Exception.hpp"
#include "SMTLEX.hpp"

using namespace Shell;

/**
 * Initialise the lexer.
 * @since 20/01/2009 Manchester
 */
SMTLexer::SMTLexer (istream& in)
  : Lexer (in)
{
} // SMTLexer::SMTLexer

/**
 * Skip all whitespaces and comments. After this operation either
 * _lastCharacter will be not whitespace or _eof will be set to true.
 * @since 20/01/2009 Manchester, made from TPTPLexer::skipWhiteSpacesAndComments
 */
void SMTLexer::skipWhiteSpacesAndComments()
{
  CALL("SMTLexer::skipWhiteSpacesAndComments");

  int comment = 0;

  for (;;) {
    if (_eof) {
      if (comment == 2) {
	throw LexerException((vstring)"non-terminated comment",
			     *this);
      }
      return;
    }
    switch (_lastCharacter) {
    case ' ':
    case '\t':
    case '\r':
    case '\f':
      readNextChar();
      break;

    case '\n': // end-of-line comment (if any) finished
      if (comment == 1) {
	comment = 0;
      }
      readNextChar();
      break;

    case ';': // SMT comment sign
      comment = 1;
      readNextChar();
      break;

    default:
      if (comment) {
	readNextChar();
	break;
      }
      return;
    }
  }
} // SMTLexer::skipWhiteSpacesAndComments

/**
 * Read the next token. 
 * @since 22/01/2009 Manchester, made from TPTPLexer::readToken
 */
void SMTLexer::readToken (Token& token)
{
  CALL("SMTLexer::readToken");

  skipWhiteSpacesAndComments();
  _charCursor = 0;

  if (_eof) {
    token.tag = TT_EOF;
    token.text = "";
    return;
  }
  token.line = _lineNumber;

  switch (currentCharacterType()) {
  case LETTER:
    readName(token);
    token.tag = TT_NAME;
    return;

  case DIGIT:
    readNumber(token);
    return;

  case COLON:
    readName(token);
    token.tag = TT_ATTRIBUTE;
    return;

  case ARITH:
    readArith(token);
    token.tag = TT_ARITH;
    return;
    
  case PAR:
    readPar(token);
    return;

  case BRACE:
    readUserValue(token);
    token.tag = TT_USER;
    return;

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
} // SMTLexer::readToken


/**
 * Return the character type of _lastCharacter.
 * 
 * @since 15/07/2004 Turku
 * @since 30/09/2004 Manchester, $ added to lower-case characters.
 */
SMTLexer::CharType SMTLexer::currentCharacterType () const
{
  CALL("SMTLexer::currentCharacterType");

  switch (_lastCharacter) {
  case 'A':
  case 'B':
  case 'C':
  case 'D':
  case 'E':
  case 'F':
  case 'G':
  case 'H':
  case 'I':
  case 'J':
  case 'K':
  case 'L':
  case 'M':
  case 'N':
  case 'O':
  case 'P':
  case 'Q':
  case 'R':
  case 'S':
  case 'T':
  case 'U':
  case 'V':
  case 'W':
  case 'X':
  case 'Y':
  case 'Z':
  case 'a':
  case 'b':
  case 'c':
  case 'd':
  case 'e':
  case 'f':
  case 'g':
  case 'h':
  case 'i':
  case 'j':
  case 'k':
  case 'l':
  case 'm':
  case 'n':
  case 'o':
  case 'p':
  case 'q':
  case 'r':
  case 's':
  case 't':
  case 'u':
  case 'v':
  case 'w':
  case 'x':
  case 'y':
  case 'z':
  case '_':
  case '\'':
    return LETTER;
  case '0':
  case '1':
  case '2':
  case '3':
  case '4':
  case '5':
  case '6':
  case '7':
  case '8':
  case '9':
    return DIGIT;
  case '(':
  case ')':
    return PAR;
  case '{':
  case '}':
    return BRACE;
  case '=':
  case '<':
  case '>':
  case '&':
  case '@':
  case '#':
  case '+':
  case '-':
  case '*':
  case '/':
  case '%':
  case '|':
  case '~':
    return ARITH;
  case ':':
    return COLON;
  case '.':
    return DOT;
  case ' ':
  case '\t':
  case '\r':
  case '\f':
  case '\n':
    return WHITE;

  default:
    throw LexerException((vstring)"illegal character " + (char)_lastCharacter,
			 *this);
  }
} // SMTLexer::currentCharacterType()

/**
 * Read a symbolic name.
 * @since 15/07/2004 Turku
 */
void SMTLexer::readArith (Token& token)
{
  CALL("SMTLexer::readArith");

  saveLastChar();

  while (readNextChar()) {
    switch (currentCharacterType()) {
    case ARITH:
      saveLastChar();
      break;
    default:
      // token parsed
      saveTokenText(token);
      return;
    }
  }

  // no more characters, token parsed
  saveTokenText(token);
} // SMTLexer::readSymbolic

/**
 * Read a single-letter token.
 * @since 15/07/2004 Turku
 */
void SMTLexer::readPar (Token& token)
{
  CALL("SMTLexer::readPar");

  switch (_lastCharacter) {
  case '(':
    token.tag = TT_LPAR;
    break;
  case ')':
    token.tag = TT_RPAR;
    break;

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }

  saveLastChar();
  saveTokenText(token);
  readNextChar();
} // SMTLexer::readPar

/**
 * Read a name. No check is made about the current character.
 * @since 15/07/2004 Turku
 */
void SMTLexer::readName (Token& token)
{
  CALL("SMTLexer::readName");

  saveLastChar();

  while (readNextChar()) {
    switch (currentCharacterType()) {
    case LETTER:
    case DIGIT:
    case DOT:
      saveLastChar();
      break;
    default:
      // token parsed
      saveTokenText(token);
      return;
    }
  }

  // no more characters, token parsed
  saveTokenText(token);
} // SMTLexer::readName

/**
 * Read a "user value" in the terminology of SMT LIB. A user value is
 * anything sequence of characters between "{" and "}" with "}" escaped
 * with "\".
 * @since 22/01/2009 Manchester
 */
void SMTLexer::readUserValue (Token& token)
{
  CALL("SMTLexer::readName");

  bool escaped = false;
  while (readNextChar()) {
    switch (_lastCharacter) {
    case '\\':
      if (escaped) {
	saveChar('\\');
      }
      escaped = true;
      break;
    case '}':
      if (escaped) {
	saveLastChar();
	escaped = false;
	break;
      }
      readNextChar();
      // no more characters, token parsed
      saveTokenText(token);
      return;
    default:
      if (escaped) {
	saveChar('\\');
	escaped = false;
      }
      saveLastChar();
      break;
    }
  }
} // SMTLexer::readUserValue
