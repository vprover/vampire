/**
 * @file TPTPLexer.cpp
 * Implements class TPTPLexer
 *
 * @since 14/07/2004 Turku
 */

#include <cstring>

#include "../Debug/Assertion.hpp"
#include "../Debug/Tracer.hpp"

#include "../Lib/Exception.hpp"

#include "TPTPLexer.hpp"

using namespace Shell;

/**
 * Initialise a lexer.
 * @since 14/07/2004 Turku
 * @since 01/08/2004 Torrevieja, changed to inherit from Lexer.
 */
TPTPLexer::TPTPLexer (istream& in)
  : Lexer (in)
{
} // TPTPLexer::TPTPLexer


/**
 * Skip all whitespaces and comments. After this operation either
 * _lastCharacter will be not whitespace or _eof will be set to true.
 * @since 14/07/2004 Turku
 * @since 02/04/2008 Budapest changed to accept the C-style comments
 */
void TPTPLexer::skipWhiteSpacesAndComments ()
{
  CALL("TPTPLexer::skipWhiteSpacesAndComments");

  int comment = 0;

  for (;;) {
    if (_eof) {
      if (comment == 2) {
	throw LexerException((string)"non-terminated comment",
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

    case '%': // TPTP comment sign
      comment = 1;
      readNextChar();
      break;

    case '/':
      readNextChar();
      if (comment) {
	break;
      }
      if (_eof || _lastCharacter != '*') {
	throw LexerException((string)"illegal character after '/' ",
			     *this);
      }
      comment = 2;
      readNextChar();
      break;

    case '*':
      if (! comment) {
	throw LexerException((string)"illegal character '*'",
			     *this);
      }
      readNextChar();
      if (comment == 1) {
	break;
      }
      // comment == 2
      if (_eof) {
	throw LexerException((string)"non-terminated comment",
			     *this);
      }
      if (_lastCharacter == '/') {
	comment = 0;
      }
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
} // TPTPLexer::skipWhiteSpacesAndComments

/**
 * Read the next token.
 * @since 15/07/2004 Turku
 * @since 24/07/2004 Torrevieja, part of this method moved to Parser
 */
void TPTPLexer::readToken (Token& token)
{
  CALL("TPTPLexer::readToken");

  skipWhiteSpacesAndComments();
  _charCursor = 0;

  if (_eof) {
    token.tag = TT_EOF;
    token.text = "";
    return;
  }
  token.line = _lineNumber;

  switch (currentCharacterType()) {
  case UPPER_CASE_LETTER:
    readName(token);
    token.tag = TT_VAR;
    return;

  case LOWER_CASE_LETTER:
    readName(token);
    token.tag = detectNameTokenTypeOfLastToken();
    return;

  case DIGIT:
    readNumber(token);
    return;

  case SINGLE:
    readSingle(token);
    return;

  case SYMBOLIC:
    readSymbolic(token);
    token.tag = detectSymbolicTokenTypeOfLastToken();
    return;

  case QUOTE:
    readQuotedString(token);
    return;

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
} // TPTPLexer::readToken


/**
 * Return the character type of _lastCharacter.
 *
 * @since 15/07/2004 Turku
 * @since 30/09/2004 Manchester, $ added to lower-case characters.
 */
TPTPLexer::CharType TPTPLexer::currentCharacterType () const
{
  CALL("TPTPLexer::currentCharacterType");

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
  case '_':
    return UPPER_CASE_LETTER;
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
  case '$':
    return LOWER_CASE_LETTER;
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
  case '[':
  case ']':
  case ',':
    return SINGLE;
  case '.':
  case '?':
  case '!':
  case '<':
  case '>':
  case '+':
  case '-':
  case '=':
  case ':':
  case '&':
  case '~':
  case '|':
    return SYMBOLIC;
  case '\'':
    return QUOTE;
  case ' ':
  case '\t':
  case '\r':
  case '\f':
  case '\n':
    return WHITE;
  case '%':
    return OTHER;

  default:
    throw LexerException((string)"illegal character " + (char)_lastCharacter,
			 *this);
  }
} // TPTPLexer::currentCharacterType()

/**
 * Read a symbolic name.
 * @since 15/07/2004 Turku
 */
void TPTPLexer::readSymbolic (Token& token)
{
  CALL("TPTPLexer::readSymbolic");

  saveLastChar();

  while (readNextChar()) {
    switch (currentCharacterType()) {
    case SYMBOLIC:
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
} // TPTPLexer::readSymbolic

/**
 * Read a single-letter token.
 * @since 15/07/2004 Turku
 */
void TPTPLexer::readSingle (Token& token)
{
  CALL("TPTPLexer::readSingle");

  switch (_lastCharacter) {
  case '(':
    token.tag = TT_LPAR;
    break;
  case ')':
    token.tag = TT_RPAR;
    break;
  case '[':
    token.tag = TT_LBRA;
    break;
  case ']':
    token.tag = TT_RBRA;
    break;
  case ',':
    token.tag = TT_COMMA;
    break;

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }

  saveLastChar();
  readNextChar();
} // TPTPLexer::readSingle

/**
 * Read a name. No check is made about the current character.
 *
 * @since 15/07/2004 Turku
 */
void TPTPLexer::readName (Token& token)
{
  CALL("TPTPLexer::readName");

  saveLastChar();

  while (readNextChar()) {
    switch (currentCharacterType()) {
    case UPPER_CASE_LETTER:
    case LOWER_CASE_LETTER:
    case DIGIT:
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
} // TPTPLexer::readVariable


/**
 * Search the keyword table to check if the token is a keyword.
 * If it is, then return the corresponding token type, else
 * return TT_NAME.
 *
 * @since 15/07/2004 Turku
 * @since 11/12/2004 Manchester, true and false added
 */
TokenType TPTPLexer::detectNameTokenTypeOfLastToken ()
{
  CALL("TPTPLexer::detectNameTokenTypeOfLastToken");

  if(_charBuffer[0]=='$') {
    if (! strcmp(_charBuffer.content(),"$false")) {
      return TT_FALSE;
    }
    if (! strcmp(_charBuffer.content(),"$true")) {
     return TT_TRUE;
    }
  }
  return TT_NAME;
} // TPTPLexer::detectNameTokenTypeOfLastToken


/**
 * Search the keyword table to check if the token is a keyword.
 * If it is, then return the corresponding token type, else
 * raise an exception.
 *
 * @since 15/07/2004 Turku
 */
TokenType TPTPLexer::detectSymbolicTokenTypeOfLastToken ()
{
  CALL("TPTPLexer::detectSymbolicTokenTypeOfLastToken");

  switch (_charBuffer[0]) {
  case ':':
    if (_charBuffer[1]) {
      break;
    }
    return TT_COLON;

  case '.':
    if (_charBuffer[1]) {
      break;
    }
    return TT_DOT;

  case '&':
    if (_charBuffer[1]) {
      break;
    }
    return TT_AND;

  case '~':
    if (_charBuffer[1]) {
      break;
    }
    return TT_NOT;

  case '|':
    if (_charBuffer[1]) {
      break;
    }
    return TT_OR;

  case '!':
    if (! strcmp(_charBuffer.content()+1,"=")) {
      return TT_NEQ;
    }
    if (_charBuffer[1]) {
      break;
    }
    return TT_FORALL;

  case '?':
    if (_charBuffer[1]) {
      break;
    }
    return TT_EXISTS;

  case '<':
    if (! strcmp(_charBuffer.content()+1,"=>")) {
      return TT_IFF;
    }
    if (! strcmp(_charBuffer.content()+1,"~>")) {
      return TT_XOR;
    }
    if (! strcmp(_charBuffer.content()+1,"=")) {
      return TT_REVERSE_IMP;
    }
    break;

  case '=':
    if (! _charBuffer[1]) {
      return TT_EQUAL;
    }
    if (! strcmp(_charBuffer.content()+1,">")) {
      return TT_IMP;
    }
    break;

  case '+':
    if (! strcmp(_charBuffer.content()+1,"+")) {
      return TT_PP;
    }
    break;

  case '-':
    if (! strcmp(_charBuffer.content()+1,"-")) {
      return TT_MM;
    }
    break;

  default:
    break;
  }

  throw LexerException((string)"illegal symbolic character "
		       + _charBuffer.content(),
		       *this);
} // TPTPLexer::detectSymbolicTokenTypeOfLastToken


/**
 * Read a quoted string.
 * @since 02/05/2005 Manchester
 */
void TPTPLexer::readQuotedString (Token& token)
{
  CALL("TPTPLexer::readQuotedString");

  bool escape=false;

  while (readNextChar()) {
    if (_lastCharacter == '\\' && !escape) {
      escape=true;
    } else if (_lastCharacter == '\'' && !escape) {
      saveTokenText(token);
      readNextChar();
      token.tag = TT_NAME;
      return;
    } else {
      if(escape && _lastCharacter!='\'' && _lastCharacter!='\\') {
	throw LexerException((string)"invalid escape sequence in quoted string ", *this);
      }
      escape=false;
      saveLastChar();
    }
  }
  throw LexerException((string)"file ended while reading quoted string ", *this);
} // TPTPLexer::readQuotedString


