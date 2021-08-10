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
 * Implements class CParser
 *
 * @since 13/01/2011 Manchester
 */

#include <cstring>

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Lib/Int.hpp"
#include "Lib/Exception.hpp"

#include "CParser.hpp"

using namespace Shell;
using namespace Lib;

/**
 * Initialise a parser.
 */
CParser::CParser(const char* input)
  : _input(input)
{
} // CParser::CParser

CParser::~CParser()
{
} // CParser::~CParser


/**
 * Read an integer type suffix identified by the following grammar:
 *   ('u'|'U')? ('l'|'L')
 * | ('u'|'U')  ('l'|'L')?
 * Save in @b tt its token type.
 * @return the end position, if recognized and 0 if not
 */
unsigned CParser::integerTypeSuffix(unsigned pos,LTType& tt)
{
  CALL("CParser::integerTypeSuffix");
  switch (_input[pos]) {
  case 'u':
  case 'U': {
    switch (_input[pos+1]) {
    case 'l':
    case 'L':
      tt = LT_ULONG_CONST;
      return pos+2;
    default:
      tt = LT_UINT_CONST;
      return pos+1;
    }
  }
  case 'l':
  case 'L':
    tt = LT_LONG_CONST;
    return pos+1;
  default:
    tt = LT_INT_CONST;
    return 0;
  }
} // integerTypeSuffix

/**
 * Read a decimal literal and saving its type in @b tt.
 * Decimal literals use the following grammar.
 * DECIMAL_LITERAL : ('0' | '1'..'9' '0'..'9'*) IntegerTypeSuffix?
 * @return the end position, if recognized and 0 if not
 */
unsigned CParser::decimalLiteral(unsigned pos,LTType& tt)
{
  CALL("CParser::decimalLiteral");

  switch (_input[pos]) {
  case '0':
    pos++;
    break;

  case '1':
  case '2':
  case '3':
  case '4':
  case '5':
  case '6':
  case '7':
  case '8':
  case '9':
    for (;;) {
      char n = _input[++pos];
      if (n < '0' || n > '9') {
	break;
      }
    }
    break;
  default:
    return 0;
  }
  unsigned pos1 = integerTypeSuffix(pos,tt);
  return pos1 ? pos1 : pos;
} // decimalLiteral

/**
 * Read an octal literal identified by the following grammar:
 * OCTAL_LITERAL : '0' ('0'..'7')+ IntegerTypeSuffix? ;
 * Save in @b tt its token type
 * @return the end position, if recognized and 0 if not
 */
unsigned CParser::octalLiteral(unsigned pos,LTType& tt)
{
  CALL("CParser::octalLiteral");

  if (_input[pos] != '0') {
    return 0;
  }
  for (;;) {
    char n = _input[++pos];
    if (n < '0' || n > '7') {
      break;
    }
  }
  unsigned pos1 = integerTypeSuffix(pos,tt);
  return pos1 ? pos1 : pos;
} // octalLiteral

/**
 * True if c is a character that can occur in a hex literal.
 * HexDigit : ('0'..'9'|'a'..'f'|'A'..'F') ;
 */
bool CParser::hexDigit(char c)
{
  CALL("CParser::hexDigit");

  switch (c) {
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
  case 'a':
  case 'b':
  case 'c':
  case 'd':
  case 'e':
  case 'f':
  case 'A':
  case 'B':
  case 'C':
  case 'D':
  case 'E':
  case 'F':
    return true;
  default:
    return false;
  }
} // hexDigit

/**
 * Read an octal literal identified by the following grammar:
 * HEX_LITERAL : '0' ('x'|'X') HexDigit+ IntegerTypeSuffix? ;
 * Save in @b tt its token type.
 * @return the end position, if recognized and 0 if not
 */
unsigned CParser::hexLiteral(unsigned pos,LTType& tt)
{
  CALL("CParser::hexLiteral");

  if (_input[pos] != '0' ||
      _input[pos+1] != 'x' ||
      !hexDigit(_input[pos+2])) {
    return 0;
  }
  pos += 2;
  while (hexDigit(_input[++pos])) {}
  unsigned pos1 = integerTypeSuffix(pos,tt);
  return pos1 ? pos1 : pos;
} // hexLiteral

/**
 * Read an exponent.
 * Exponent : ('e'|'E') ('+'|'-')? ('0'..'9')+ ;
 * @return the end position, if recognized and 0 if not
 */
unsigned CParser::exponent(unsigned pos)
{
  CALL("CParser::exponent");

  switch (_input[pos]) {
  case 'e':
  case 'E':
    pos++;
    break;
  default:
    return 0;
  }
  switch (_input[++pos]) {
  case '+':
  case '-':
    pos++;
    break;
  default:
    break;
  }
  if (!digit(_input[pos])) {
    return 0;
  }
  while (digit(_input[++pos])) {}
  return pos;
} // exponent

/** True if the character is a float type suffix and set @b tt
 * to the appropriate type.
 * FloatTypeSuffix : ('f'|'F'|'d'|'D') ;
 */
bool CParser::floatTypeSuffix(char c,LTType& tt)
{
  CALL("CParser::floatTypeSuffix");

  switch (c) {
  case 'f':
  case 'F':
    tt = LT_FLOAT_CONST;
    return true;
  case 'd':
  case 'D':
    tt = LT_DOUBLE_CONST;
    return true;
  default:
    tt = LT_FLOAT_CONST;
    return false;
  }
} // floatTypeSuffix

/**
 * Read a floating point literal.
 * FLOATING_POINT_LITERAL
 *  :   ('0'..'9')+ '.' ('0'..'9')* Exponent? FloatTypeSuffix?
 *  |   '.' ('0'..'9')+ Exponent? FloatTypeSuffix?
 *  |   ('0'..'9')+ Exponent FloatTypeSuffix?
 *  |   ('0'..'9')+ FloatTypeSuffix;
 * @return the end position, if recognized, and 0 if not
 */
unsigned CParser::floatingPointLiteral(unsigned pos,LTType& tt)
{
  CALL("CParser::floatingPointLiteral");

  if (_input[pos] == '.') { // case 2
    if (!digit(_input[++pos])) {
      return 0;
    }
    while (digit(_input[++pos])) {}
    unsigned pos1 = exponent(pos);
    if (pos1) {
      pos = pos1;
    }
    return floatTypeSuffix(_input[pos],tt) ? pos+1 : pos;
  }
  // cases 1,3,4
  if (!digit(_input[pos])) {
    return 0;
  }
  while (digit(_input[++pos])) {}
  if (floatTypeSuffix(_input[pos],tt)) { // case 4
    return pos+1;
  }
  if (_input[pos] != '.') { // case 3
    pos = exponent(pos);
    if (!pos) {
      return 0;
    }
    return floatTypeSuffix(_input[pos],tt) ? pos+1 : pos;
  }
  // case 1
  while (digit(_input[++pos])) {}
  unsigned pos1 = exponent(pos);
  if (pos1) {
    pos = pos1;
  }
  return floatTypeSuffix(_input[pos],tt) ? pos+1 : pos;
} // floatingPointLiteral

/** true of c is a letter: $, _, A-Z, a-z */
bool CParser::letter(char c)
{
  return c == '$'
    || c == '_'
    || (c >= 'A' && c <= 'Z')
    || (c >= 'a' && c <= 'z');
} // letter

/**
 * Read an identifier.
 * IDENTIFIER : LETTER (LETTER|'0'..'9')*
 * @return the end position, if recognized, and 0 if not
 */
unsigned CParser::identifier(unsigned pos)
{
  CALL("CParser::identifier");

  if (!letter(_input[pos])) {
    return 0;
  }
  for (;;) {
    char c = _input[++pos];
    if (letter(c) || digit(c)) continue;
    return pos;
  }
} // identifier

/**
 * Skip whitespace characters, comments, and lines having # as the first
 * non-whitespace character.
 * @return the position of first character after.
 */
unsigned CParser::skipWhiteSpacesAndComments(unsigned pos)
{
  CALL("CParser::skipWhiteSpacesAndComments");

  bool newLine = (pos == 0);
  for (;;) {
    switch (_input[pos]) {
    case ' ':
    case '\t':
      pos++;
      break;
    case '\r':
    case '\n':
      newLine = true;
      pos++;
      break;
    case '#':
      if (!newLine) {
	throw LexerException(*this,pos,"character # not in the beginning of a line");
      }
      pos = skipToEndOfLine(pos+1);
      break;
    case '/':
      switch (_input[pos+1]) {
      case '*':
	newLine = false;
	// skip to the end of comments
	pos = skipToEndOfComment(pos+2);
	break;
      case '/':
	pos = skipToEndOfLine(pos+2);
	newLine = true;
	break;
      default:
	return pos;
      }
      break;
    default:
      return pos;
    }
  }
} // CParser::skipWhiteSpacesAndComments

/**
 * Skip characters to the end of line.
 * @return the position of first character after.
 */
unsigned CParser::skipToEndOfLine(unsigned pos)
{
  CALL("CParser::skipToEndOfLine");

  for (;;) {
    char c = _input[pos];
    switch (c) {
    case 0:
      return pos;
    case '\n':
      return pos+1;
    case '\r':
      return _input[pos+1] == '\n' ? pos+2 : pos+1;
    default:
      pos++;
      break;
    }
  }
} // CParser::skipToEndOfLine

/**
 * Skip characters to the end of comment.
 * @return the position of first character after.
 */
unsigned CParser::skipToEndOfComment(unsigned pos)
{
  CALL("CParser::skipToEndOfComment");

  unsigned start = pos;
  for (;;) {
    char c = _input[pos];
    switch (c) {
    case 0:
      throw LexerException(*this,start-2,"non-terminated comment");
    case '*':
      if (_input[pos+1] == '/') {
	return pos+2;
      }
      pos++;
      break;
    default:
      pos++;
      break;
    }
  }
} // CParser::skipToEndOfComment

/**
 * Create a new lexer exception.
 */
CParser::LexerException::LexerException (const CParser& parser,unsigned pos,vstring message)
{
  _message = message + " at position " + Int::toString(pos) + "\n>>>" + Int::toString(int(parser.input()[pos])) + "<<<" +
    "\n---------------" + (parser.input()+pos) + "\n---------------\n";
} // LexerException::LexerException

/**
 * Write itself to an ostream.
 */
void CParser::LexerException::cry (ostream& out) const
{
  out << "C lexer exception: " << _message << '\n';
} // CParser::LexerException::cry

/**
 * Create a new parser exception.
 */
CParser::ParserException::ParserException (const CParser& parser,unsigned pos,vstring message)
{
  _message = message + " at position " + Int::toString(pos) + "\n>>>" + Int::toString(int(parser.input()[pos])) + "<<<" +
    "\n---------------" + (parser.input()+pos) + "\n---------------\n";
} // ParserException::ParserException

/**
 * Write itself to an ostream.
 */
void CParser::ParserException::cry (ostream& out) const
{
  out << "C parser exception: " << _message << '\n';
} // CParser::ParserException::cry

void CParser::tokenize()
{
  CALL("CParser::parse");

  unsigned pos = 0;
  unsigned end;
  Token token;

  for (;;) {
    pos = skipWhiteSpacesAndComments(pos);
    if (! _input[pos]) {
      token.type = LT_EOF;
      token.start = pos;
      token.end = pos;
      _tokens.push_back(token);
      return;
    }

    token.start = pos;
    switch (_input[pos]) {
    case 'a':
    case 'b':
    case 'c':
    case 'd':
    case 'e':
    case 'f':
    case 'g':
    case 'i':
    case 'l':
    case 'r':
    case 's':
    case 't':
    case 'u':
    case 'v':
    case 'w':
      end = identifier(pos);
      token.type = keyword(pos,end);
      break;
      
    case 'h':
    case 'j':
    case 'k':
    case 'm':
    case 'n':
    case 'o':
    case 'p':
    case 'q':
    case 'x':
    case 'y':
    case 'z':
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
    case '$':
    case '_':
      end = identifier(pos);
      token.type = LT_IDENTIFIER;
      break;

    case '{':
      end = pos+1;
      token.type = LT_LBRACE;
      break;
    case '}':
      end = pos+1;
      token.type = LT_RBRACE;
      break;
    case '(':
      end = pos+1;
      token.type = LT_LPAR;
      break;
    case ')':
      end = pos+1;
      token.type = LT_RPAR;
      break;
    case ';':
      end = pos+1;
      token.type = LT_SEMICOLON;
      break;

    case '=':
      end = pos+1;
      if (_input[end] == '=') {
	end++;
	token.type = LT_EQ_OP;
	break;
      }
      token.type = LT_ASSIGN;
      break;

    case '+':
      end = pos+1;
      if (_input[end] == '=') {
	end++;
	token.type = LT_ADD_ASSIGN;
	break;
      }
      if (_input[end] == '+') {
	end++;
	token.type = LT_INC_OP;
	break;
      }
      token.type = LT_ADD;
      break;

    case '*':
      end = pos+1;
      if (_input[end] == '=') {
	end++;
	token.type = LT_MULT_ASSIGN;
	break;
      }
      token.type = LT_MULT;
      break;

    case '.':
      end = pos+1;
      if (_input[end] == '.') {
	if (_input[end+1] != '.') {
	  throw LexerException(*this,pos,"bad expression");
	}
	end += 2;
	token.type = LT_ELLIPSIS;
	break;
      }
      token.type = LT_DOT;
      break;

    case '>':
      end = pos+1;
      if (_input[end] == '=') {
	end++;
	token.type = LT_GE_OP;
	break;
      }
      if (_input[end] != '>') {
	token.type = LT_GREATER;
	break;
      }
      if (_input[end+1] == '=') {
	end += 2;
	token.type = LT_RIGHT_ASSIGN;
	break;
      }
      end++;
      token.type = LT_RIGHT_OP;
      break;

    case '<':
      end = pos+1;
      if (_input[end] == '=') {
	end++;
	token.type = LT_LE_OP;
	break;
      }
      if (_input[end] == ':') {
	end++;
	token.type = LT_LBRACKET;
	break;
      }
      if (_input[end] == '%') {
	end++;
	token.type = LT_LBRACE;
	break;
      }
      if (_input[end] != '<') {
	token.type = LT_LESS;
	break;
      }
      if (_input[end+1] == '=') {
	end += 2;
	token.type = LT_LEFT_ASSIGN;
	break;
      }
      end++;
      token.type = LT_LEFT_OP;
      break;

    case '-':
      end = pos+1;
      if (_input[end] == '=') {
	end++;
	token.type = LT_SUB_ASSIGN;
	break;
      }
      if (_input[end] == '-') {
	end++;
	token.type = LT_DEC_OP;
	break;
      }
      if (_input[end] == '>') {
	end++;
	token.type = LT_PTR_OP;
	break;
      }
      token.type = LT_MINUS;
      break;

    case '/':
      end = pos+1;
      if (_input[end] == '=') {
	end++;
	token.type = LT_DIV_ASSIGN;
	break;
      }
      token.type = LT_DIV;
      break;

    case '%':
      end = pos+1;
      if (_input[end] == '=') {
	end++;
	token.type = LT_MOD_ASSIGN;
	break;
      }
      if (_input[end] == '>') {
	end++;
	token.type = LT_RBRACE;
	break;
      }
      token.type = LT_MOD;
      break;

    case '&':
      end = pos+1;
      if (_input[end] == '=') {
	end++;
	token.type = LT_AND_ASSIGN;
	break;
      }
      if (_input[end] == '&') {
	end++;
	token.type = LT_AND_OP;
	break;
      }
      token.type = LT_AMP;
      break;

    case '|':
      end = pos+1;
      if (_input[end] == '=') {
	end++;
	token.type = LT_OR_ASSIGN;
	break;
      }
      if (_input[end] == '|') {
	end++;
	token.type = LT_OR_OP;
	break;
      }
      token.type = LT_BAR;
      break;

    case '^':
      end = pos+1;
      if (_input[end] == '=') {
	end++;
	token.type = LT_XOR_ASSIGN;
	break;
      }
      token.type = LT_XOR;
      break;

    case '!':
      end = pos+1;
      if (_input[end] == '=') {
	end++;
	token.type = LT_NE_OP;
	break;
      }
      token.type = LT_EXCLAMATION;
      break;

    case ':':
      end = pos+1;
      if (_input[end] == '>') {
	end++;
	token.type = LT_RBRACKET;
	break;
      }
      token.type = LT_COLON;
      break;

    case '[':
      end = pos+1;
      token.type = LT_LBRACKET;
      break;

    case ']':
      end = pos+1;
      token.type = LT_RBRACKET;
      break;

    case ',':
      end = pos+1;
      token.type = LT_COMMA;
      break;

    case '~':
      end = pos+1;
      token.type = LT_TILDE;
      break;

    case '?':
      end = pos+1;
      token.type = LT_QUESTION;
      break;

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
      end = numericConstant(pos,token.type);
      if (!end) {
	throw LexerException(*this,pos,"bad numeric constant");
      }
      break;

    case '"':
      end = stringConstant(pos);
      if (!end) {
	throw LexerException(*this,pos,"non-terminated vstring constant");
      }
      token.type = LT_STRING_CONST;
      break;

    case '\'':
      end = charConstant(pos);
      if (!end) {
	throw LexerException(*this,pos,"bad character constant");
      }
      token.type = LT_CHAR_CONST;
      break;

    default:
      throw LexerException(*this,pos,(vstring)"unrecognized symbol " + _input[pos] + " in the input");
    }
    // if (end <= pos) {
    //   cout << "ERRRRRRRRRRRRRRRRRRRRRRR\n" << pos << ':' << end << ':' << _input[pos];
    // }
    ASS(end > pos);
    token.end = end;
    _tokens.push_back(token);
    pos = end;
  }
} // CParser::tokenize

/**
 * Return the token type of the identifier substring between the positions
 * pos and end.
 */
CParser::LTType CParser::keyword(unsigned pos,unsigned end)
{
  CALL("CParser::keyword");

  const char* text = _input+pos;
  switch (*text) {
  case 'a':
    if (keyword(text+1,"uto",end-pos-1)) return LT_AUTO;
    break;
  case 'b':
    if (keyword(text+1,"reak",end-pos-1)) return LT_BREAK;
    break;
  case 'c':
    switch (text[1]) {
    case 'a':
      if (keyword(text+2,"se",end-pos-2)) return LT_CASE;
      break;
    case 'h':
      if (keyword(text+2,"ar",end-pos-2)) return LT_CHAR;
    case 'o':
      if (keyword(text+2,"nst",end-pos-2)) return LT_CONST;
      if (keyword(text+2,"ntinue",end-pos-2)) return LT_CONTINUE;
      break;
    default:
      break;
    }
    break;

  case 'd':
    switch (text[1]) {
    case 'e':
      if (keyword(text+2,"fault",end-pos-2)) return LT_DEFAULT;
      break;
    case 'o':
      if (keyword(text+2,"",end-pos-2)) return LT_DO;
      if (keyword(text+2,"uble",end-pos-2)) return LT_DOUBLE;
      break;
    default:
      break;
    }
    break;

  case 'e':
    if (keyword(text+1,"lse",end-pos-1)) return LT_ELSE;
    if (keyword(text+1,"num",end-pos-1)) return LT_ENUM;
    if (keyword(text+1,"xtern",end-pos-1)) return LT_EXTERN;
    break;

  case 'f':
    if (keyword(text+1,"loat",end-pos-1)) return LT_FLOAT;
    if (keyword(text+1,"or",end-pos-1)) return LT_FOR;
    break;

  case 'g':
    if (keyword(text+1,"oto",end-pos-1)) return LT_GOTO;
    break;

  case 'i':
    if (keyword(text+1,"f",end-pos-1)) return LT_IF;
    if (keyword(text+1,"nline",end-pos-1)) return LT_INLINE;
    if (keyword(text+1,"nt",end-pos-1)) return LT_INT;
    break;

  case 'l':
    if (keyword(text+1,"ong",end-pos-1)) return LT_LONG;
    break;

  case 'r':
    if (keyword(text+1,"egister",end-pos-1)) return LT_REGISTER;
    if (keyword(text+1,"estrict",end-pos-1)) return LT_RESTRICT;
    if (keyword(text+1,"eturn",end-pos-1)) return LT_RETURN;
    break;

  case 's':
    if (keyword(text+1,"hort",end-pos-1)) return LT_SHORT;
    if (keyword(text+1,"igned",end-pos-1)) return LT_SIGNED;
    if (keyword(text+1,"izeof",end-pos-1)) return LT_SIZEOF;
    if (keyword(text+1,"truct",end-pos-1)) return LT_STRUCT;
    if (keyword(text+1,"witch",end-pos-1)) return LT_SWITCH;
    break;

  case 't':
    if (keyword(text+1,"ypedef",end-pos-1)) return LT_TYPEDEF;
    break;

  case 'u':
    if (keyword(text+1,"nion",end-pos-1)) return LT_UNION;
    if (keyword(text+1,"nsigned",end-pos-1)) return LT_UNSIGNED;
    break;

  case 'v':
    if (keyword(text+1,"oid",end-pos-1)) return LT_VOID;
    if (keyword(text+1,"olatile",end-pos-1)) return LT_VOLATILE;
    break;

  case 'w':
    if (keyword(text+1,"hile",end-pos-1)) return LT_WHILE;
    break;

  default:
    ASS(false);
  }
  return LT_IDENTIFIER;
} // CParser::keyword

/**
 * True if the first chars characters of txt coincides with the
 * first chars characters of word
 * @pre the first chars characters of txt are non-zero
 */
bool CParser::keyword(const char* txt,const char* word,int chars)
{
  CALL("CParser::keyword/3");

  ASS(chars >= 0);

  while (chars--) {
    ASS(*txt);
    if (*txt++ != *word++) return false;
  }
  return !*word;
} // CParser::keyword/3

/**
 * Read a numeric constant and save the tag to @b tt.
 * NUMERIC_CONSTANT
 * : HEX_LITERAL
 * | OCTAL_LITERAL
 * | DECIMAL_LITERAL
 * | FLOATING_POINT_LITERAL;
 * @warning can be optimised by (1) putting float and integer recognition together and (2) 
 * @return the end position, if recognized, and 0 if not
 */
unsigned CParser::numericConstant(unsigned pos,LTType& tt)
{
  CALL("CParser::numericConstant");

  if (_input[pos] != '0') {
    unsigned end = floatingPointLiteral(pos,tt);
    if (end) {
      return end;
    }
    return decimalLiteral(pos,tt);
  }
  switch (_input[pos+1]) {
  case 'x':
  case 'X':
    return hexLiteral(pos,tt);
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
    return octalLiteral(pos,tt);
  default:
    return decimalLiteral(pos,tt);
  }
} // CParser::numericConstant

/**
 * Read a string constant.
 * @return the end position, if recognized, and 0 if not
 */
unsigned CParser::stringConstant(unsigned pos)
{
  CALL("CParser::stringConstant");

  ASS(_input[pos] == '"');

  for (;;) {
    switch (_input[++pos]) {
    case '"':
      return pos+1;
    case '\\':
      pos++;
      break;
    case 0:
      return 0;
    default:
      break;
    }
  }
} // CParser::stringConstant

/**
 * Read a character constant.
 * @return the end position, if recognized, and 0 if not
 */
unsigned CParser::charConstant(unsigned pos)
{
  CALL("CParser::charConstant");
  ASS(_input[pos] == '\'');

  switch (_input[++pos]) {
  case '\'':
    return 0;
  case '\\':
    pos++;
    break;
  case 0:
    return 0;
  default:
    break;
  }
  if (_input[++pos] == '\'') {
    return pos+1;
  }
  return 0;
} // CParser::charConstant

#if VDEBUG
void CParser::output(ostream& str)
{
  CALL("CParser::output");

  for (unsigned i = 0;;i++) {
    Token& tok = _tokens[i];
    if (tok.type == LT_EOF) {
      return;
    }
    for (unsigned p = tok.start;p < tok.end;p++) {
      str << _input[p];
    }
    str << '\n';
  }
}
#endif

/**
 * Parse a primary expression using the following grammar.
 *  primary_expression
 *   : IDENTIFIER
 *   | CONSTANT
 *   | STRING_LITERAL
 *   | '(' expression ')';
 */
unsigned CParser::primaryExpression(unsigned pos,bool backtrack)
{
  CALL("CParser::primaryExpression");

  Token& tok = _tokens[pos];
  switch (tok.type) {
  case LT_IDENTIFIER:
    _units.push_back(new Identifier(pos,pos+1));
    return pos+1;

  case LT_INT_CONST:
  case LT_LONG_CONST:
  case LT_UINT_CONST:
  case LT_ULONG_CONST:
  case LT_FLOAT_CONST:
  case LT_DOUBLE_CONST:
  case LT_STRING_CONST:
  case LT_CHAR_CONST:
    _units.push_back(new ConstantExpression(pos,pos+1));
    return pos+1;

  case LT_LPAR: {
    unsigned end = expression(pos,backtrack);
    if (!end) return 0;
    if (!consumeToken(LT_RPAR,end+1,backtrack)) return 0;
    return end+2;
  }
  default:
    if (backtrack) return 0;
    throw ParserException(*this,pos,"primary expression expected");
  }
} // primaryExpression


/**
 * Parse a postfix expression using the following grammar.
 * postfix_expression
 *	: primary_expression
 *	| postfix_expression '[' expression ']'
 *	| postfix_expression '(' ')'
 *	| postfix_expression '(' argument_expression_list ')'
 *	| postfix_expression '.' IDENTIFIER
 *	| postfix_expression PTR_OP IDENTIFIER
 *	| postfix_expression INC_OP
 *	| postfix_expression DEC_OP
 *	| '(' type_name ')' '{' initializer_list '}'
 *	| '(' type_name ')' '{' initializer_list ',' '}'
 * @warning the last two cases are not implemented
*/
unsigned CParser::postfixExpression(unsigned pos,bool backtrack)
{
  CALL("CParser::postfixExpression");
  unsigned end = primaryExpression(pos,backtrack);
  if (!end) return 0;

  for (;;) {
    Token& tok = _tokens[end];
    switch (tok.type) {
    case LT_LBRACKET: {
      pos = expression(end+1,backtrack);
      if (!pos) return 0;
      if (!consumeToken(LT_RBRACKET,pos+1,backtrack)) return 0;
      pos += 2;
      Unit* rhs = _units.back();
      _units.pop_back();
      Unit* lhs = _units.back();
      _units.pop_back();
      _units.push_back(new ArrayApplication(lhs->start(),pos,lhs,rhs));
      break;
    }

    case LT_DOT:
    case LT_PTR_OP:
      if (!consumeToken(LT_IDENTIFIER,end+1,backtrack)) return 0;
      pos = end+2;
      break;

    case LT_INC_OP:
    case LT_DEC_OP:
      pos = end+1;
      break;

    case LT_LPAR:
      if (_tokens[end+1].type == LT_RPAR) return end+2;
      pos = argumentExpressionList(pos,backtrack);
      if (!pos) return 0;
      if (!consumeToken(LT_RPAR,pos,backtrack)) return 0;
      pos++;
      break;

    default:
      return end;
    }
  }
} // 

/**
 * If the token type at position pos is t, return true.
 * Otherwise, if backtrack is true, then return 0, otherwise
 * raise an exception.
 */
bool CParser::consumeToken(LTType t,unsigned pos,bool backtrack)
{
  if (_tokens[pos].type == t) return true;
  if (backtrack) return false;
  const char* what;
  switch (t) {
  case LT_RPAR:
    what = "}";
    break;
  case LT_IDENTIFIER:
    what = "identifier";
  default:
    ASS(false);
  }
  throw ParserException(*this,pos,(vstring)what + " expected");
} // consumeToken

/**
 * Parse a unary expression using the following grammar.
 *   unary_expression
 *	: postfix_expression
 *	| INC_OP unary_expression
 *	| DEC_OP unary_expression
 *	| unary_operator cast_expression
 *	| SIZEOF unary_expression
 *	| SIZEOF '(' type_name ')'
 *	;
 *  unary_operator : '&' | '*' | '+' | '-' | '~' | '!'
 * @warning two sizeof cases are not implemented and cast_expression is replaced by unary_expression
*/
unsigned CParser::unaryExpression(unsigned pos,bool backtrack)
{
  CALL("CParser::unaryExpression");

  for (;;) {
    bool done = false;
    switch (_tokens[pos].type) {
    case LT_INC_OP:
    case LT_DEC_OP:
    case LT_AMP:
    case LT_MULT:
    case LT_ADD:
    case LT_MINUS:
    case LT_TILDE:
    case LT_EXCLAMATION:
      pos++;
      break;
    default:
      done = true;
      break;
    }
    if (done) {
      break;
    }
  }
  return postfixExpression(pos,backtrack);
} // unaryExpression

/**
 * Parse a multiplicative expression using the following grammar.
 * multiplicative_expression
 *	: cast_expression
 *	| multiplicative_expression '*' cast_expression
 *	| multiplicative_expression '/' cast_expression
 *	| multiplicative_expression '%' cast_expression
 * @warning since cast_expression is replaced by unary_expression
*/
unsigned CParser::multiplicativeExpression(unsigned pos,bool backtrack)
{
  CALL("CParser::multiplicativeExpression");

  for (;;) {
    unsigned end = unaryExpression(pos,backtrack);
    if (!end) return 0;
    switch (_tokens[end].type) {
    case LT_MULT:
    case LT_DIV:
    case LT_MOD:
      pos = end+1;
      break;
    default:
      return end;
    }
  }
} // CParser::multiplicativeExpression

/**
 * Parse a additive expression using the following grammar.
 * additive_expression
 *	: multiplicative_expression
 *	| additive_expression '+' multiplicative_expression
 *	| additive_expression '-' multiplicative_expression
*/
unsigned CParser::additiveExpression(unsigned pos,bool backtrack)
{
  CALL("CParser::additiveExpression");

  for (;;) {
    unsigned end = multiplicativeExpression(pos,backtrack);
    if (!end) return 0;
    switch (_tokens[end].type) {
    case LT_ADD:
    case LT_MINUS:
      pos = end+1;
      break;
    default:
      return end;
    }
  }
} // CParser::additiveExpression

/**
 * Parse a shift expression using the following grammar.
 * shift_expression
 *	: additive_expression
 *	| shift_expression LEFT_OP additive_expression
 *	| shift_expression RIGHT_OP additive_expression
 */
unsigned CParser::shiftExpression(unsigned pos,bool backtrack)
{
  CALL("CParser::shiftExpression");

  for (;;) {
    unsigned end = additiveExpression(pos,backtrack);
    if (!end) return 0;
    switch (_tokens[end].type) {
    case LT_LEFT_OP:
    case LT_RIGHT_OP:
      pos = end+1;
      break;
    default:
      return end;
    }
  }
} // CParser::shiftExpression


/**
 * Parse a relational expression using the following grammar.
 * relational_expression
 *	: shift_expression
 *	| relational_expression '<' shift_expression
 *	| relational_expression '>' shift_expression
 *	| relational_expression LE_OP shift_expression
 *	| relational_expression GE_OP shift_expression
 */
unsigned CParser::relationalExpression(unsigned pos,bool backtrack)
{
  CALL("CParser::relationalExpression");

  for (;;) {
    unsigned end = shiftExpression(pos,backtrack);
    if (!end) return 0;
    switch (_tokens[end].type) {
    case LT_LESS:
    case LT_GREATER:
    case LT_LE_OP:
    case LT_GE_OP:
      pos = end+1;
      break;
    default:
      return end;
    }
  }
} // CParser::relationalExpression

/**
 * Parse an equality expression using the following grammar.
 * equality_expression
 *	: relational_expression
 *	| equality_expression EQ_OP relational_expression
 *	| equality_expression NE_OP relational_expression
 */
unsigned CParser::equalityExpression(unsigned pos,bool backtrack)
{
  CALL("CParser::equalityExpression");

  for (;;) {
    unsigned end = relationalExpression(pos,backtrack);
    if (!end) return 0;
    switch (_tokens[end].type) {
    case LT_EQ_OP:
    case LT_NE_OP:
      pos = end+1;
      break;
    default:
      return end;
    }
  }
} // CParser::equalityExpression

/**
 * Parse an and expression using the following grammar.
 * and_expression
 * and_expression
 *	: equality_expression
 *	| and_expression '&' equality_expression
 */
unsigned CParser::andExpression(unsigned pos,bool backtrack)
{
  CALL("CParser::andExpression");

  for (;;) {
    unsigned end = equalityExpression(pos,backtrack);
    if (!end) return 0;
    switch (_tokens[end].type) {
    case LT_AMP:
      pos = end+1;
      break;
    default:
      return end;
    }
  }
} // CParser::andExpression


/**
 * Parse an exclusive or expression using the following grammar.
 * exclusive_or_expression
 *	: and_expression
 *	| exclusive_or_expression '^' and_expression
 */
unsigned CParser::xorExpression(unsigned pos,bool backtrack)
{
  CALL("CParser::xorExpression");

  for (;;) {
    unsigned end = andExpression(pos,backtrack);
    if (!end) return 0;
    switch (_tokens[end].type) {
    case LT_XOR:
      pos = end+1;
      break;
    default:
      return end;
    }
  }
} // CParser::xorExpression

/**
 * Parse an inclusive or expression using the following grammar.
 * inclusive_or_expression
 *	: exclusive_or_expression
 *	| inclusive_or_expression '|' exclusive_or_expression
 */
unsigned CParser::orExpression(unsigned pos,bool backtrack)
{
  CALL("CParser::orExpression");

  for (;;) {
    unsigned end = xorExpression(pos,backtrack);
    if (!end) return 0;
    switch (_tokens[end].type) {
    case LT_BAR:
      pos = end+1;
      break;
    default:
      return end;
    }
  }
} // CParser::orExpression

/**
 * Parse a logical and expression using the following grammar.
 * logical_and_expression
 *	: inclusive_or_expression
 *	| logical_and_expression AND_OP inclusive_or_expression
 */
unsigned CParser::logicalAndExpression(unsigned pos,bool backtrack)
{
  CALL("CParser::logicalAndExpression");

  for (;;) {
    unsigned end = orExpression(pos,backtrack);
    if (!end) return 0;
    switch (_tokens[end].type) {
    case LT_AND_OP:
      pos = end+1;
      break;
    default:
      return end;
    }
  }
} // CParser::logicalAndExpression

/**
 * Parse a logical or expression using the following grammar.
 * logical_or_expression
 *	: logical_and_expression
 *	| logical_or_expression OR_OP logical_and_expression
 */
unsigned CParser::logicalOrExpression(unsigned pos,bool backtrack)
{
  CALL("CParser::logicalOrExpression");

  for (;;) {
    unsigned end = logicalAndExpression(pos,backtrack);
    if (!end) return 0;
    switch (_tokens[end].type) {
    case LT_OR_OP:
      pos = end+1;
      break;
    default:
      return end;
    }
  }
} // CParser::logicalOrExpression

/**
 * Parse a conditional expression using the following grammar.
 * conditional_expression
 *	: logical_or_expression
 *	| logical_or_expression '?' expression ':' conditional_expression
 */
unsigned CParser::conditionalExpression(unsigned pos,bool backtrack)
{
  CALL("CParser::conditionalExpression");

  for (;;) {
    unsigned end = logicalOrExpression(pos,backtrack);
    if (!end) return 0;
    switch (_tokens[end].type) {
    case LT_QUESTION:
      pos = end+1;
      end = expression(pos,backtrack);
      if (!end) return 0;
      consumeToken(LT_COLON,end,backtrack);
      pos = end+1;
      break;
    default:
      return end;
    }
  }
} // CParser::conditionalExpression

/**
 * Parse an assignment expression using the following grammar.
 * assignment_expression
 *	: conditional_expression
 *	| unary_expression assignment_operator assignment_expression
 */
unsigned CParser::assignmentExpression(unsigned pos,bool backtrack)
{
  CALL("CParser::assignmentExpression");
  NOT_IMPLEMENTED;
}

/*
assignment_operator
	: '='
	| MUL_ASSIGN
	| DIV_ASSIGN
	| MOD_ASSIGN
	| ADD_ASSIGN
	| SUB_ASSIGN
	| LEFT_ASSIGN
	| RIGHT_ASSIGN
	| AND_ASSIGN
	| XOR_ASSIGN
	| OR_ASSIGN
	;

expression
	: assignment_expression
	| expression ',' assignment_expression
	;

*/

unsigned CParser::expression(unsigned pos,bool backtrack)
{
  return 0;
}

unsigned CParser::argumentExpressionList(unsigned int, bool)
{
  return 0;
}

CParser::Identifier::Identifier(unsigned start, unsigned end)
  : Unit(PT_IDENTIFIER,start,end)
{
}

CParser::ConstantExpression::ConstantExpression(unsigned start, unsigned end)
  : Unit(PT_CONSTANT_EXPRESSION,start,end)
{
}
