/**
 * @file Parse/TPTP.cpp
 * Implements class TPTP for parsing TPTP files
 *
 * @since 08/04/2011 Manchester
 */

#include <fstream>

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Lib/Int.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Indexing/TermSharing.hpp"

#include "TPTP.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Parse;

#define DEBUG_SHOW_TOKENS 0
#define DEBUG_SHOW_TERMS 0
#define DEBUG_SHOW_FORMULAS 0
#define DEBUG_SHOW_UNITS 0

/**
 * Create a parser, parse the input and return the parsed list of units.
 * @since 13/07/2011 Manchester
 */
UnitList* TPTP::parse(istream& input)
{
  Parse::TPTP parser(input);
  parser.parse();
  return parser.units();
}

/**
 * Initialise a lexer.
 * @since 27/07/2004 Torrevieja
 */
TPTP::TPTP(istream& in)
  : _includeDepth(0),
    _containsConjecture(false),
    _allowedNames(0),
    _in(&in)
{
} // Lexer::Lexer

/**
 * The destructor, does nothing.
 * @since 09/07/2012 Manchester
 */
TPTP::~TPTP()
{
#if VDEBUG
  ASS(_allowedNamesStack.isEmpty());
  ASS(_inputs.isEmpty());
  while (!_states.isEmpty()) {
    cout << toString(_states.pop()) << "\n";
  }
  while (!_strings.isEmpty()) {
    cout << _strings.pop() << "\n";
  }
  // ASS(_connectives.isEmpty());
  // ASS(_bools.isEmpty());
  // ASS(_ints.isEmpty());
  // ASS(_varLists.isEmpty());
  // ASS(_tags.isEmpty());
  // ASS(_formulas.isEmpty());
  // ASS(_termLists.isEmpty());
  // ASS(_literals.isEmpty());
#endif
} // TPTP::~TPTP

/**
 * Read all tokens one by one 
 * @since 08/04/2011 Manchester
 */
void TPTP::parse()
{
  CALL("TPTP::parse");

  // bulding tokens one by one
  _gpos = 0;
  _cend = 0;
  _tend = 0;
  _states.push(UNIT_LIST);
  while (!_states.isEmpty()) {
    State s = _states.pop();
#if DEBUG_SHOW_TOKENS
    cout << toString(s) << "\n";
#endif
    switch (s) {
    case UNIT_LIST:
      unitList();
      break;
    case FOF:
      fof(true);
      break;
    case TFF:
      tff();
      break;
    case CNF:
      fof(false);
      break;
    case FORMULA:
      formula();
      break;
    case ATOM:
      atom();
      break;
    case ARGS:
      args();
      break;
    case TERM:
      term();
      break;
    case END_TERM:
      endTerm();
      break;
    case MID_ATOM:
      midAtom();
      break;
    case END_EQ:
      endEquality();
      break;
    case VAR_LIST:
      varList();
      break;
    case TAG:
      tag();
      break;
    case END_FOF:
      endFof();
      break;
    case SIMPLE_FORMULA:
      simpleFormula();
      break;
    case END_FORMULA:
      endFormula();
      break;
    case INCLUDE:
      include();
      break;
    case TYPE:
      type();
      break;
    default:
      cout << "Don't know how to process state " << s << "\n";
      throw ::Exception("");
    }
  }
} // TPTP::parse()

/**
 * Return either the content or the string for this token
 * @since 11/04/2011 Manchester
 */
string TPTP::Token::toString() const
{
  string str = TPTP::toString(tag);
  return str == "" ? content : str;
} // Token::toString

/**
 * Return the string representation of this tag or "" is the representation
 * is not fixed (e.g. for T_NAME)
 * @since 11/04/2011 Manchester
 */
string TPTP::toString(Tag tag)
{
  switch (tag) {
  case T_EOF:
    return "<eof>";
  case T_LPAR:
    return "(";
  case T_RPAR:
    return ")";
  case T_LBRA:
    return "[";
  case T_RBRA:
    return "]";
  case T_COMMA:
    return ",";
  case T_COLON:
    return ":";
  case T_NOT:
    return "~";
  case T_AND:
    return "&";
  case T_EQUAL:
    return "=";
  case T_NEQ:
    return "!=";
  case T_FORALL:
    return "!";
  case T_EXISTS:
    return "?";
  case T_PI:
    return "??";
  case T_SIGMA:
    return "!!";
  case T_IMPLY:
    return "=>";
  case T_XOR:
    return "<~>";
  case T_IFF:
    return "<=>";
  case T_REVERSE_IMP:
    return "<=";
  case T_DOT:
    return ".";
  case T_OR:
    return "|";
  case T_ASS:
    return ":=";
  case T_LAMBDA:
    return "^";
  case T_APP:
    return "@";
  case T_STAR:
    return "*";
  case T_UNION:
    return "+";
  case T_ARROW:
    return ">";
  case T_SUBTYPE:
    return "<<";
  case T_NOT_OR:
    return "~|";
  case T_NOT_AND:
    return "~&";
  case T_SEQUENT:
    return "-->";
  case T_THF_QUANT_ALL:
    return "!>";
  case T_THF_QUANT_SOME:
    return "?*";
  case T_APP_PLUS:
    return "@+";
  case T_APP_MINUS:
    return "@-";
  case T_TRUE:
    return "$true";
  case T_FALSE:
    return "$false";
  case T_TTYPE:
    return "$tType";
  case T_NAME:
  case T_REAL:
  case T_RAT:
  case T_INT:
  case T_VAR:
  case T_STRING:
    return "";
#if VDEBUG
  default:
    ASS(false);
#endif
  }
} // toString(Tag)

/**
 * Read all tokens one by one 
 * @since 08/04/2011 Manchester
 */
bool TPTP::readToken(Token& tok)
{
  CALL("TPTP::readToken");

  skipWhiteSpacesAndComments();
  tok.start = _gpos;
  switch (getChar(0)) {
  case 0:
    tok.tag = T_EOF;
    return false;
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
    tok.tag = T_NAME;
    readName(tok);
    return true;
  case '$':
    readReserved(tok);
    return true;
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
    tok.tag = T_VAR;
    readName(tok);
    return true;
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
    tok.tag = readNumber(tok);
    return true;
  case '"':
    tok.tag = T_STRING;
    readString(tok);
    return true;
  case '\'':
    tok.tag = T_NAME;
    readAtom(tok);
    return true;
  case '(':
    tok.tag = T_LPAR;
    resetChars();
    return true;
  case ')':
    tok.tag = T_RPAR;
    resetChars();
    return true;
  case '[':
    tok.tag = T_LBRA;
    resetChars();
    return true;
  case ']':
    tok.tag = T_RBRA;
    resetChars();
    return true;
  case ',':
    tok.tag = T_COMMA;
    resetChars();
    return true;
  case ':':
    if (getChar(1) == '=') {
      tok.tag = T_ASS;
      resetChars();
      return true;
    }
    tok.tag = T_COLON;
    shiftChars(1);
    return true;
  case '~':
    if (getChar(1) == '&') {
      tok.tag = T_NOT_AND;
      resetChars();
      return true;
    }
    if (getChar(1) == '|') {
      tok.tag = T_NOT_OR;
      resetChars();
      return true;
    }
    tok.tag = T_NOT;
    shiftChars(1);
    return true;
  case '=':
    if (getChar(1) == '>') {
      tok.tag = T_IMPLY;
      resetChars();
      return true;
    }
    tok.tag = T_EQUAL;
    shiftChars(1);
    return true;
  case '&':
    tok.tag = T_AND;
    resetChars();
    return true;
  case '^':
    tok.tag = T_LAMBDA;
    resetChars();
    return true;
  case '@':
    if (getChar(1) == '+') {
      tok.tag = T_APP_PLUS;
      resetChars();
      return true;
    }
    if (getChar(1) == '-') {
      tok.tag = T_APP_MINUS;
      resetChars();
      return true;
    }
    tok.tag = T_APP;
    shiftChars(1);
    return true;
  case '*':
    tok.tag = T_STAR;
    resetChars();
    return true;
  case '>':
    tok.tag = T_ARROW;
    resetChars();
    return true;
  case '!':
    if (getChar(1) == '=') {
      tok.tag = T_NEQ;
      resetChars();
      return true;
    }
    if (getChar(1) == '>') {
      tok.tag = T_THF_QUANT_ALL;
      resetChars();
      return true;
    }
    if (getChar(1) == '!') {
      tok.tag = T_SIGMA;
      resetChars();
      return true;
    }
    tok.tag = T_FORALL;
    shiftChars(1);
    return true;
  case '?':
    if (getChar(1) == '?') {
      tok.tag = T_PI;
      resetChars();
      return true;
    }
    if (getChar(1) == '*') {
      tok.tag = T_THF_QUANT_SOME;
      resetChars();
      return true;
    }
    tok.tag = T_EXISTS;
    shiftChars(1);
    return true;
  case '<':
    if (getChar(1) == '<') {
      tok.tag = T_SUBTYPE;
      resetChars();
      return true;
    }
    if (getChar(1) == '~' && getChar(2) == '>') {
      tok.tag = T_XOR;
      resetChars();
      return true;
    }
    if (getChar(1) != '=') {
      throw Exception("unrecognized symbol",_gpos);
    }
    if (getChar(2) == '>') {
      tok.tag = T_IFF;
      resetChars();
      return true;
    }
    tok.tag = T_REVERSE_IMP;
    shiftChars(2);
    return true;
  case '.':
    tok.tag = T_DOT;
    resetChars();
    return true;
  case '|':
    tok.tag = T_OR;
    resetChars();
    return true;
  case '-':
    if (getChar(1) == '-' && getChar(2) == '>') {
      tok.tag = T_SEQUENT;
      resetChars();
      return true;
    }
    tok.tag = readNumber(tok);
    return true;
  case '+':
    if (getChar(1) < '0' || getChar(1) > '9') {
      tok.tag = T_UNION;
      shiftChars(1);
      return true;
    }
    tok.tag = readNumber(tok);
    return true;
  default:
    throw Exception("Bad character",_gpos);
  }
} // TPTP::readToken()

/**
 * Skip all white spaces and comments in the input file
 * @since 08/04/2011 Manchester
 */
void TPTP::skipWhiteSpacesAndComments()
{
  CALL("TPTP::skipWhiteSpacesAndComments");

  for (;;) {
    switch (getChar(0)) {
    case 0: // end-of-file
      return;

    case ' ':
    case '\t':
    case '\r':
    case '\f':
    case '\n':
      resetChars();
      break;

    case '%': // end-of-line comment
    resetChars();
    for (;;) {
      int c = getChar(0);
      if (c == 0) {
	return;
      }
      resetChars();
      if (c == '\n') {
	break;
      }
    }
    break;

    case '/': // potential comment
      if (getChar(1) != '*') {
	return;
      }
      resetChars();
      // search for the end of this comment
      for (;;) {
	int c = getChar(0);
	if (!c) {
	  return;
	}
	resetChars();
	if (c != '*') {
	  continue;
	}
	// c == '*'
	c = getChar(0);
	resetChars();
	if (c != '/') {
	  continue;
	}
	break;
      }
      break;

    // skip to the end of comment
    default:
      return;
    }
  }
} // TPTP::skipWhiteSpacesAndComments

/**
 * Read the name
 * @since 08/04/2011 Manchester
 */
void TPTP::readName(Token& tok)
{
  CALL("TPTP::readName");
  for (int n = 1;;n++) {
    switch (getChar(n)) {
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
      break;
    default:
      tok.content.assign(_chars.content(),n);
      if (_chars.content()[0] == '$') {
	if (tok.content != "$true" && tok.content != "$false") {
	  throw Exception((string)"I do not know how to handle " + tok.content,tok);
	}
      }
      shiftChars(n);
      return;
    }
  }
} // readName

/**
 * Read a reserved name (starting with a $)
 * @since 10/07/2011 Manchester
 */
void TPTP::readReserved(Token& tok)
{
  CALL("TPTP::readReserved");

  for (int n = 1;;n++) {
    switch (getChar(n)) {
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
      break;
    default:
      tok.content.assign(_chars.content(),n);
      shiftChars(n);
      if (tok.content == "$true") {
	tok.tag = T_TRUE;
	return;
      }
      if (tok.content == "$false") {
	tok.tag = T_FALSE;
	return;
      }
      if (tok.content == "$tType") {
	tok.tag = T_TTYPE;
	return;
      }
      throw Exception((string)"I do not know how to handle " + tok.content,tok);
    }
  }
} // readReserved

/**
 * Read a string
 * @since 08/04/2011 Manchester
 */
void TPTP::readString(Token& tok)
{
  CALL("TPTP::readString");
  for (int n = 1;;n++) {
    int c = getChar(n);
    if (!c) {
      throw Exception("non-terminated string",_gpos);
    }
    if (c == '\\') { // escape
      c = getChar(++n);
      if (!c) {
	throw Exception("non-terminated string",_gpos);
      }
      continue;
    }
    if (c == '"') {
      tok.content.assign(_chars.content()+1,n-1);
      resetChars();
      return;
    }
  }
} // readString

/**
 * Read a quoted atom
 * @since 08/04/2011 Manchester
 */
void TPTP::readAtom(Token& tok)
{
  CALL("TPTP::readAtom");

  for (int n = 1;;n++) {
    int c = getChar(n);
    if (!c) {
      throw Exception("non-terminated quoted atom",_gpos);
    }
    if (c == '\\') { // escape
      c = getChar(++n);
      if (!c) {
	throw Exception("non-terminated quoted atom",_gpos);
      }
      continue;
    }
    if (c == '\'') {
      tok.content.assign(_chars.content()+1,n-1);
      resetChars();
      return;
    }
  }
} // readAtom

TPTP::Exception::Exception(string message,int pos)
{
  _message = message + " at position " + Int::toString(pos);
} // TPTP::Exception::Exception

TPTP::Exception::Exception(string message,Token& tok)
{
  _message = message + " at position " + Int::toString(tok.start) + " (text: " + tok.toString() + ')';
} // TPTP::Exception::Exception

/**
 * Exception printing a message. Currently computing a position is simplified
 * @since 08/04/2011 Manchester
 */
void TPTP::Exception::cry(ostream& str)
{
  str << _message << "\n";
}

/**
 * Read a number
 * @since 08/04/2011 Manchester
 */
TPTP::Tag TPTP::readNumber(Token& tok)
{
  CALL("TPTP::readNumber");

  // skip the sign
  int c = getChar(0);
  ASS(c);
  int pos = decimal((c == '+' || c == '-') ? 1 : 0);
  switch (getChar(pos)) {
  case '/':
    pos = positiveDecimal(pos+1);
    tok.content.assign(_chars.content(),pos-1);
    shiftChars(pos-1);
    return T_RAT;
  case 'E':
  case 'e':
    {
      char c = getChar(pos+1);
      pos = decimal((c == '+' || c == '-') ? pos+1 : pos);
      tok.content.assign(_chars.content(),pos-1);
      shiftChars(pos-1);
    }
    return T_REAL;
  case '.': 
    {
      int c;
      int p = pos;
      do {
	c = getChar(++pos);
      }
      while (c >= '0' && c <= '9');
      if (pos == p+1) {
	throw Exception("wrong number format",_gpos);
      }
      pos = decimal((c == 'e' || c == 'E') ? pos+1 : pos);
      tok.content.assign(_chars.content(),pos-1);
      shiftChars(pos-1);
    }
    return T_REAL;
  default:
    tok.content.assign(_chars.content(),pos);
    shiftChars(pos);
    return T_INT;
  }
} // readNumber

/**
 * Read a decimal starting at position pos (see the TPTP grammar),
 * return the position after the last character in the decimal.
 * @since 08/04/2011 Manchester
 */
int TPTP::decimal(int pos)
{
  CALL("TPTP::decimal");

  switch (getChar(pos)) {
  case '0':
    return pos+1;
  case '1':
  case '2':
  case '3':
  case '4':
  case '5':
  case '6':
  case '7':
  case '8':
  case '9':
    break;
  default:
    throw Exception("wrong number format",_gpos);
  }

  int c;
  do {
    c = getChar(++pos);
  }
  while (c >= '0' && c <= '9');
  return pos;
} // decimal

/**
 * Read a positive decimal starting at position pos (see the TPTP grammar),
 * return the position after the last character in the decimal.
 * @since 08/04/2011 Manchester
 */
int TPTP::positiveDecimal(int pos)
{
  CALL("TPTP::positiveDecimal");
  switch (getChar(pos)) {
  case '1':
  case '2':
  case '3':
  case '4':
  case '5':
  case '6':
  case '7':
  case '8':
  case '9':
    break;
  default:
    throw Exception("wrong number format",_gpos);
  }


  int c;
  do {
    c = getChar(++pos);
  }
  while (c >= '0' && c <= '9');
  return pos;
} // positiveDecimal

/**
 * Process unit list declaration. If end of file is reached, terminates. Otherwise,
 * pushes on the state state UNIT_LIST and one of CNF, FOF, VAMPIRE
 * @since 10/04/2011 Manchester
 */
void TPTP::unitList()
{
  CALL("TPTP::unitList");
  if (env.timeLimitReached()) {
    // empty states to avoid infinite loop
    while (!_states.isEmpty()) {
      _states.pop();
    }
    return;
  }

  Token& tok = getTok(0);
  if (tok.tag == T_EOF) {
    resetToks();
    if (_inputs.isEmpty()) {
      return;
    }
    resetChars();
    delete _in;
    _in = _inputs.pop();
    delete _allowedNames;
    _allowedNames = _allowedNamesStack.pop();
    _states.push(UNIT_LIST);
    return;
  }
  if (tok.tag != T_NAME) {
    throw Exception("cnf(), fof(), vampire() or include() expected",tok);
  }
  string name(tok.content);
  _states.push(UNIT_LIST);
  if (name == "cnf") {
    _states.push(CNF);
    resetToks();
    return;
  }
  if (name == "fof") {
    _states.push(FOF);
    resetToks();
    return;
  }
  if (name == "tff") {
    _states.push(TFF);
    resetToks();
    return;
  }
  if (name == "vampire") {
    _states.push(VAMPIRE);
    resetToks();
    return;
  }
  if (name == "include") {
    _states.push(INCLUDE);
    resetToks();
    return;
  }
  throw Exception("cnf(), fof(), vampire() or include() expected",tok);
}

/**
 * Process fof() or cnf() declaration. Does the following:
 * <ol>
 *  <li>add 0 to _formulas</li>
 *  <li>save the input type to _lastInputType</li>
 *  <li>add unit name to _strings</li>
 *  <li>add to _states END_FOF,FORMULA</li>
 *  <li>adds to _bools true, if fof and false, if cnf</li>
 * </ol>
 * @since 10/04/2011 Manchester
 */
void TPTP::fof(bool fo)
{
  CALL("TPTP::fof");

  _bools.push(fo);
  consumeToken(T_LPAR);
  // save the name of this unit
  Token& tok = getTok(0);
  switch(tok.tag) {
  case T_NAME:
    _strings.push(tok.content);
    resetToks();
    break;
  case T_INT:
    _strings.push(tok.content);
    resetToks();
    break;
  default:
    throw Exception("Unit name expected",tok);
  }
  
  consumeToken(T_COMMA);
  tok = getTok(0);
  int start = tok.start;
  string tp = name();
  if (tp == "axiom" || tp == "plain") {
    _lastInputType = Unit::AXIOM;
  }
  else if (tp == "definition") {
    _lastInputType = Unit::AXIOM;
  }
  else if (tp == "conjecture") {
    _containsConjecture = true;
    _lastInputType = Unit::CONJECTURE;
  }
  else if (tp == "negated_conjecture") {
    _containsConjecture = true;
    _lastInputType = Unit::NEGATED_CONJECTURE;
  }
  else if (tp == "hypothesis") {
    _lastInputType = Unit::ASSUMPTION;
  }
  else if (tp == "claim") {
    _lastInputType = Unit::CLAIM;
  }
  else if (tp == "lemma") {
    _lastInputType = Unit::LEMMA;
  }
  else {
    throw Exception((string)"unit type, such as axiom or definition expected but " + tp + " found",
		    start);
  }
  consumeToken(T_COMMA);
  _states.push(END_FOF);
  _states.push(FORMULA);
} // fof()

/**
 * Process fof() or cnf() declaration. Does the following:
 * <ol>
 *  <li>add 0 to _formulas</li>
 *  <li>save the input type to _lastInputType</li>
 *  <li>add unit name to _strings</li>
 *  <li>add to _states END_FOF,FORMULA</li>
 *  <li>adds to _bools true, if fof and false, if cnf</li>
 * </ol>
 * @since 10/04/2011 Manchester
 */
void TPTP::tff()
{
  CALL("TPTP::tff");

  consumeToken(T_LPAR);
  // save the name of this unit
  Token& tok = getTok(0);
  switch(tok.tag) {
  case T_NAME:
    _strings.push(tok.content);
    resetToks();
    break;
  case T_INT:
    _strings.push(tok.content);
    resetToks();
    break;
  default:
    throw Exception("Unit name expected",tok);
  }
  
  consumeToken(T_COMMA);
  tok = getTok(0);
  int start = tok.start;
  string tp = name();
  if (tp == "type") {
    // type declaration
    consumeToken(T_COMMA);
    // TPTP syntax allows for an arbitrary number of parentheses around a type
    // declaration
    int lpars = 0;
    for (;;) {
      tok = getTok(0);
      if (tok.tag != T_LPAR) {
	break;
      }
      lpars++;
      resetToks();
    }
    string nm = name();
    consumeToken(T_COLON);
    tok = getTok(0);
    if (tok.tag == T_TTYPE) {
      bool added;
      env.sorts->addSort(nm,added);
      if (!added) {
	throw Exception("Sort name must be unique",tok);
      }
      resetToks();
      while (lpars--) {
	consumeToken(T_RPAR);
      }
      consumeToken(T_RPAR);
      consumeToken(T_DOT);
      return;
    }
    _ints.push(lpars);
    _strings.push(nm);
    _states.push(END_TFF);
    _states.push(TYPE);
    return;
  }

  if (tp == "axiom" || tp == "plain") {
    _lastInputType = Unit::AXIOM;
  }
  else if (tp == "definition") {
    _lastInputType = Unit::AXIOM;
  }
  else if (tp == "conjecture") {
    _containsConjecture = true;
    _lastInputType = Unit::CONJECTURE;
  }
  else if (tp == "negated_conjecture") {
    _containsConjecture = true;
    _lastInputType = Unit::NEGATED_CONJECTURE;
  }
  else if (tp == "hypothesis") {
    _lastInputType = Unit::ASSUMPTION;
  }
  else if (tp == "claim") {
    _lastInputType = Unit::CLAIM;
  }
  else if (tp == "lemma") {
    _lastInputType = Unit::LEMMA;
  }
  else {
    throw Exception((string)"unit type, such as axiom or definition expected but " + tp + " found",
		    start);
  }
  consumeToken(T_COMMA);
  _states.push(END_FOF);
  _states.push(FORMULA);
} // fof()

/**
 * Process include() declaration
 * @since 07/07/2011 Manchester
 */
void TPTP::include()
{
  CALL("TPTP::include");

  consumeToken(T_LPAR);
  Token& tok = getTok(0);
  if (tok.tag != T_NAME) {
    throw Exception((string)"file name expected",tok);
  }
  string relativeName=tok.content;
  resetToks();
  bool ignore = _forbiddenIncludes.contains(relativeName);
  if (!ignore) {
    _allowedNamesStack.push(_allowedNames);
    _allowedNames = 0;
    _inputs.push(_in);
  }

  tok = getTok(0);
  if (tok.tag == T_COMMA) {
    if (!ignore) {
      _allowedNames = new Set<string>;
    }
    resetToks();
    consumeToken(T_LBRA);
    for(;;) {
      tok = getTok(0);
      if (tok.tag == T_RBRA) {
	resetToks();
	break;
      }
      if (tok.tag != T_NAME) {
	throw Exception((string)"formula name expected",tok);
      }
      string axName=tok.content;
      resetToks();
      if (!ignore) {
	_allowedNames->insert(axName);
      }
      consumeToken(T_COMMA);
    }
  }
  consumeToken(T_RPAR);
  consumeToken(T_DOT);

  if (ignore) {
    return;
  }
  string fileName(env.options->includeFileName(relativeName));
  _in = new ifstream(fileName.c_str());
  if (!*_in) {
    USER_ERROR((string)"cannot open file " + fileName);
  }
} // include

/**
 * Read the next token that must be a name.
 * @since 10/04/2011 Manchester
 */
string TPTP::name()
{
  CALL("TPTP::name");
  Token& tok = getTok(0);
  if (tok.tag != T_NAME) {
    throw Exception("name expected",tok);
  }
  string nm = tok.content;
  resetToks();
  return nm;
} // name

/**
 * Read the next token that must have a given name.
 * @since 10/04/2011 Manchester
 */
void TPTP::consumeToken(Tag t)
{
  CALL("TPTP::consumeToken");

  Token& tok = getTok(0);
  if (tok.tag != t) {
    string expected = toString(t);
    throw Exception(expected + " expected",tok);
  }
  resetToks();
} // consumeToken

/**
 * Read a formula and save it on the stack of formulas.
 * Adds to _states END_SIMPLE_FORMULA,SIMPLE_FORMULA
 * @since 10/04/2011 Manchester
 */
void TPTP::formula()
{
  CALL("TPTP::formula");

  _connectives.push((Connective)-1);
  _states.push(END_FORMULA);
  _states.push(SIMPLE_FORMULA);
} // formula

/**
 * Read a formula and save it on the stack of formulas.
 * Adds to _states END_SIMPLE_FORMULA,SIMPLE_FORMULA
 * @since 10/04/2011 Manchester
 */
void TPTP::type()
{
  CALL("TPTP::type");

  _connectives.push((Connective)-1);
  _states.push(END_FORMULA);
  _states.push(SIMPLE_FORMULA);
} // type

/**
 * Read an atom and save the resulting literal
 * @since 10/04/2011 Manchester
 */
void TPTP::atom()
{
  CALL("TPTP::atom");
  Token& tok = getTok(0);
  switch (tok.tag) {
  case T_NAME:
    _strings.push(tok.content);
    _states.push(MID_ATOM);
    resetToks();
    tok = getTok(0);
    if (tok.tag != T_LPAR) {
      // this is just a constant or a propositional atom
      _ints.push(0); // 0 arguments read;
      return;
    }
    resetToks();
    _states.push(ARGS);
    _ints.push(1); // number of next argument
    return;

  case T_REAL:
    throw Exception("reading reals is not supported",tok);
    
  case T_INT:
    throw Exception("reading integers is not supported",tok);
  default:
    throw Exception("atom expected",tok);
  }
  // throw Exception(*this,"atom() is undefined");
} // atom()

/**
 * Read a non-empty sequence of arguments, including the right parentheses
 * and save the resulting sequence of TermList and their number
 * @since 10/04/2011 Manchester
 */
void TPTP::args()
{
  CALL("TPTP::args");

  _states.push(END_TERM);
  _states.push(TERM);
} // args

/**
 * Read a non-empty sequence of variable, including the right bracket
 * and save the resulting sequence of TermList and their number
 * @since 07/07/2011 Manchester
 */
void TPTP::varList()
{
  CALL("TPTP::varList");

  Stack<int> vars;
  for (;;) {
    Token& tok = getTok(0);
    if (tok.tag != T_VAR) {
      throw Exception("variable expected",tok);
    }
    vars.push(_vars.insert(tok.content));
    resetToks();
    tok = getTok(0);
    switch (tok.tag) {
    case T_COMMA:
      resetToks();
      break;
    case T_RBRA:
      {
	resetToks();
	Formula::VarList* vs = Formula::VarList::empty();
	while (!vars.isEmpty()) {
	  vs = new Formula::VarList(vars.pop(),vs);
	}
	_varLists.push(vs);
	return;
      }

    default:
      throw Exception("] or , expected after a variable name",tok);
    }
  }
} // varList

/**
 * Read a term and save the resulting TermList
 * @since 10/04/2011 Manchester
 */
void TPTP::term()
{
  CALL("TPTP::term");

  Token& tok = getTok(0);
  switch (tok.tag) {
  case T_NAME:
    _strings.push(tok.content);
    resetToks();
    tok = getTok(0);
    if (tok.tag == T_LPAR) {
      resetToks();
      _states.push(ARGS);
      _ints.push(1); // number of next argument
      return;
    }
    // this is just a constant or a propositional atom
    _ints.push(0); // this term has 0 arguments
    return;
  case T_VAR:
    _ints.push(_vars.insert(tok.content));
    _ints.push(-1); // this term is a variable
    resetToks();
    return;
  case T_STRING:
    _ints.push(env.signature->addStringConstant(tok.content));
    _ints.push(-2); // this term is a constant
    resetToks();
    return;
  case T_INT:
    _ints.push(env.signature->addIntegerConstant(tok.content));
    _ints.push(-2); // this term is a constant
    resetToks();
    return;
  case T_REAL:
    throw Exception("reading reals is not supported",tok);
  default:
    throw Exception("term expected",tok);
  }
} // term

/**
 * Build a term assembled by term() 
 * @since 09/07/2011 Manchester
 */
void TPTP::buildTerm()
{
  CALL("TPTP::buildTerm");

  int arity = _ints.pop();
  TermList ts;
  switch (arity) {
  case -1: // variable
    ts.makeVar(_ints.pop());
    break;
  case -2: // constant: string or integer
    {
      Term* t = new(0) Term;
      t->makeSymbol(_ints.pop(),0);
      t = env.sharing->insert(t);
      ts.setTerm(t);
    }
    break;
  default: // compound term
    {
      ASS(arity >= 0);
      unsigned fun = env.signature->addFunction(_strings.pop(),arity);
      Term* t = new(arity) Term;
      t->makeSymbol(fun,arity);
      bool safe = true;
      for (int i = arity-1;i >= 0;i--) {
	TermList ss = _termLists.pop();
	*(t->nthArgument(i)) = ss;
	safe = safe && ss.isSafe();
      }
      if (safe) {
	t = env.sharing->insert(t);
      }
      ts.setTerm(t);
    }
    break;
  }
  _termLists.push(ts);
}

/**
 * Read after an end of term
 * @since 10/04/2011 Manchester
 */
void TPTP::endTerm()
{
  CALL("TPTP::endTerm");

  // first, build the term
  buildTerm();

  // check if there is any other term in the argument list
  Token tok = getTok(0);
  switch (tok.tag) {
  case T_COMMA:
    resetToks();
    _states.push(ARGS);
    _ints.push(_ints.pop()+1);
    return;
  case T_RPAR:
    resetToks();
    return;
  default:
    throw Exception(", or ) expected after an end of a term",tok);
  }
} // endTerm

/**
 * Read after an end of atom or after lhs of an equality or inequality
 * @since 10/04/2011 Manchester
 */
void TPTP::midAtom()
{
  CALL("TPTP::midAtom");

  Token tok = getTok(0);
  switch (tok.tag) {
  case T_EQUAL:
  case T_NEQ:
    buildTerm();
    resetToks();
    _bools.push(tok.tag == T_EQUAL);
    _states.push(END_EQ);
    _states.push(TERM);
    return;
  default:
    {
      int arity = _ints.pop();
      unsigned pred = env.signature->addPredicate(_strings.pop(),arity);
      Literal* a = new(arity) Literal(pred,arity,true,false);
      bool safe = true;
      for (int i = arity-1;i >= 0;i--) {
	TermList ts = _termLists.pop();
	safe = safe && ts.isSafe();
	*(a->nthArgument(i)) = ts;
      }
      if (safe) {
	a = env.sharing->insert(a);
      }
#if DEBUG_SHOW_TERMS
      cout << "Atom: " << a->toString() << "\n";
#endif
      _formulas.push(new AtomicFormula(a));
      return;
    }
  }
} // midAtom

/**
 * Read after an end of equality or inequality and save the (in)equality formula.
 * @since 09/07/2011 Manchester
 */
void TPTP::endEquality()
{
  CALL("TPTP::endEquality");

  buildTerm();
  TermList rhs = _termLists.pop();
  TermList lhs = _termLists.pop();

  Literal* l = Literal::equality(_bools.pop());
  TermList* args = l->args();
  *args = lhs;
  args = args->next();
  *args = rhs;
  if (lhs.isSafe() && rhs.isSafe()) {
    l = env.sharing->insert(l);
  }
  _formulas.push(new AtomicFormula(l));
} // endEquality

/**
 * Build a formula from previousy built subformulas
 * @since 10/04/2011 Manchester
 */
void TPTP::endFormula()
{
  CALL("TPTP::endFormula");

  Connective con = _connectives.pop();
  Formula* f;
  bool conReverse;
  switch (con) {
  case IMP:
    conReverse = _bools.pop();
    break;
  case AND:
  case OR:
  case IFF:
  case XOR:
  case (Connective)-1:
    break;
  case NOT:
    f = _formulas.pop();
    _formulas.push(new NegatedFormula(f));
    _states.push(END_FORMULA);
    return;
  case FORALL:
  case EXISTS:
    f = _formulas.pop();
    _formulas.push(new QuantifiedFormula(con,_varLists.pop(),f));
    _states.push(END_FORMULA);
    return;
  case LITERAL:
  default:
    throw ::Exception((string)"tell me how to handle connective " + Int::toString(con));
  }

  Token& tok = getTok(0);
  Tag tag = tok.tag;
  Connective c;
  bool cReverse;
  switch (tag) {
  case T_AND:
    c = AND;
    break;
  case T_OR:
    c = OR;
    break;
  case T_XOR:
    c = XOR;
    break;
  case T_IFF:
    c = IFF;
    break;
  case T_IMPLY:
    cReverse = false;
    c = IMP;
    break;
  case T_REVERSE_IMP:
    cReverse = true;
    c = IMP;
    break;
  default:
    // the formula does not end at a binary connective, build the formula and terminate
    switch (con) {
    case IMP:
      f = _formulas.pop();
      if (conReverse) {
	f = new BinaryFormula(con,f,_formulas.pop());
      }
      else {
	f = new BinaryFormula(con,_formulas.pop(),f);
      }
#if DEBUG_SHOW_FORMULAS
      cout << f->toString() << "\n";
#endif
      _formulas.push(f);
      _states.push(END_FORMULA);
      return;

    case IFF:
    case XOR:
      f = _formulas.pop();
      f = new BinaryFormula(con,_formulas.pop(),f);
#if DEBUG_SHOW_FORMULAS
      cout << f->toString() << "\n";
#endif
      _formulas.push(f);
      _states.push(END_FORMULA);
      return;
      
    case AND:
    case OR:
      f = _formulas.pop();
      f = makeJunction(con,_formulas.pop(),f);
#if DEBUG_SHOW_FORMULAS
      cout << f->toString() << "\n";
#endif
      _formulas.push(f);
      _states.push(END_FORMULA);
      return;

    case (Connective)-1:
      return;
#if VDEBUG
    default:
      ASSERTION_VIOLATION;
#endif
    }
  }

  // con and c are binary connectives
  if (higherPrecedence(con,c)) {
    f = _formulas.pop();
    Formula* g = _formulas.pop();
    if (con == AND || c == OR) {
      f = makeJunction(con,g,f);
    }
    else if (con == IMP && conReverse) {
      f = new BinaryFormula(con,f,g);
    }
    else {
      f = new BinaryFormula(con,g,f);
    }
#if DEBUG_SHOW_FORMULAS
    cout << f->toString() << "\n";
#endif
    _formulas.push(f);
    _states.push(END_FORMULA);
    return;
  }

  // c is a binary connective
  _connectives.push(con);
  if (con == IMP) {
    _bools.push(conReverse);
  }
  _connectives.push(c);
  if (c == IMP) {
    _bools.push(cReverse);
  }
  resetToks();
  _states.push(END_FORMULA);
  _states.push(SIMPLE_FORMULA);
} // endFormula

/**
 * Skip a tag.
 * @since 10/04/2011 Manchester
 */
void TPTP::tag()
{
  CALL("TPTP::tag");
  consumeToken(_tags.pop());
} // tag

/**
 * Process the end of the fof() definition and build the corresponding unit.
 * @since 10/04/2011 Manchester
 */
void TPTP::endFof()
{
  CALL("TPTP::endFof");
  consumeToken(T_RPAR);
  consumeToken(T_DOT);

  _bools.pop(); // ignoring whether the input was cnf() or fof()
  Formula* f = _formulas.pop();
  string nm = _strings.pop(); // unit name
  if (_allowedNames && !_allowedNames->contains(nm)) {
    return;
  }
  env.statistics->inputFormulas++;
  Unit* unit = new FormulaUnit(f,new Inference(Inference::INPUT),_lastInputType);
#if DEBUG_SHOW_UNITS
  cout << "Unit: " << unit->toString() << "\n";
#endif
  if (_includeDepth) {
    unit->markIncluded();
  }

  switch (_lastInputType) {
  case Unit::CONJECTURE:
    {
      Formula::VarList* vs = f->freeVariables();
      if (vs->isEmpty()) {
	f = new NegatedFormula(f);
      }
      else {
	f = new NegatedFormula(new QuantifiedFormula(FORALL,vs,f));
      }
      unit = new FormulaUnit(f,
			     new Inference1(Inference::NEGATED_CONJECTURE,unit),
			     Unit::CONJECTURE);
    }
    break;

  case Unit::CLAIM:
    {
      bool added;
      unsigned pred = env.signature->addPredicate(nm,0,added);
      if(!added) {
	USER_ERROR("Names of claims must be unique: "+nm);
      }
      env.signature->getPredicate(pred)->markCFName();
      Literal* a = new(0) Literal(pred,0,true,false);
      a = env.sharing->insert(a);
      Formula* claim = new AtomicFormula(a);
      Formula::VarList* vs = f->freeVariables();
      if (!vs->isEmpty()) {
	f = new QuantifiedFormula(FORALL,vs,f);
      }
      f = new BinaryFormula(IFF,claim,f);
      unit = new FormulaUnit(f,
			     new Inference1(Inference::CLAIM_DEFINITION,unit),
			     Unit::ASSUMPTION);
    }
    break;

  default:
    break;
  }
  _units.push(unit);
} // tag

/**
 * Read a simple formula (quantified formula, negation,
 * formula in parentheses, true or false).
 * @since 10/04/2011 Manchester
 */
void TPTP::simpleFormula()
{
  CALL("TPTP::simpleFormula");

  Token& tok = getTok(0);
  Tag tag = tok.tag;
  switch (tag) {
  case T_NOT:
    resetToks();
    _connectives.push(NOT);
    _states.push(SIMPLE_FORMULA);
    return;

  case T_FORALL:
  case T_EXISTS:
    resetToks();
    consumeToken(T_LBRA);
    _connectives.push(tag == T_FORALL ? FORALL : EXISTS);
    _states.push(SIMPLE_FORMULA);
    _states.push(TAG);
    _tags.push(T_COLON);
    _states.push(VAR_LIST); 
    return;

  case T_LPAR:
    resetToks();
    _states.push(TAG);
    _tags.push(T_RPAR);
    _states.push(FORMULA);
    return;

  case T_STRING:
  case T_INT:
  case T_VAR:
    {
      Token after = getTok(1);
      bool polarity;
      switch (after.tag) {
      case T_EQUAL:
	polarity = true;
	break;
      case T_NEQ:
	polarity = false;
	break;
      default:
	throw Exception("= or != expected",after);
      }
      TermList ts;
      makeTerm(ts,tok);
      _termLists.push(ts);
      resetToks();
      _bools.push(polarity);
      _states.push(END_EQ);
      _states.push(TERM);
    }
    return;

  case T_TRUE:
    resetToks();
    _formulas.push(new Formula(true));
    return;

  case T_FALSE:
    resetToks();
    _formulas.push(new Formula(false));
    return;

  case T_NAME:
    _states.push(ATOM);
    return;

  default:
    throw Exception("formula expected",tok);
  }
} // simpleFormula

/**
 * Make a non-compound term, that is, a string constant, a variable,
 * or a number
 */
void TPTP::makeTerm(TermList& ts,Token& tok)
{
  CALL("TPTP::makeTerm");

  switch (tok.tag) {
  case T_STRING:
    {
      unsigned fun = env.signature->addStringConstant(tok.content);
      Term* t = new(0) Term;
      t->makeSymbol(fun,0);
      t = env.sharing->insert(t);
      ts.setTerm(t);
    }
    return;
  case T_VAR:
    ts.makeVar(_vars.insert(tok.content));
    return;
  case T_INT:
    {
      unsigned fun = env.signature->addIntegerConstant(tok.content);
      Term* t = new(0) Term;
      t->makeSymbol(fun,0);
      t = env.sharing->insert(t);
      ts.setTerm(t);
    }
    return;
#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
} // makeTerm

/**
 * True if c1 has a strictly higher priority than c2.
 * @since 07/07/2011 Manchester
 */
bool TPTP::higherPrecedence(Connective c1,Connective c2)
{
  if (c1 == c2) return false;
  if (c1 == (Connective)-1) return false;
  if (c2 == IFF) return true;
  if (c1 == IFF) return false;
  if (c2 == XOR) return true;
  if (c1 == XOR) return false;
  if (c2 == IMP) return true;
  if (c1 == IMP) return false;
  if (c2 == OR) return true;
  if (c1 == OR) return false;
  ASSERTION_VIOLATION;
} // higherPriority

/**
 * Create an and- or or-formula flattening its lhs and rhs if necessary.
 * @since 07/07/2011 Manchester
 */
Formula* TPTP::makeJunction (Connective c,Formula* lhs,Formula* rhs)
{
  if (lhs->connective() == c) {
    FormulaList* largs = lhs->args();

    if (rhs->connective() == c) {
      FormulaList::concat(largs,rhs->args());
      delete static_cast<JunctionFormula*>(rhs);
      return lhs;
    }

    // only lhs has c as the main connective
    FormulaList::concat(largs,new FormulaList(rhs));
    return lhs;
  }

  // lhs' connective is not c
  if (rhs->connective() == c) {
    static_cast<JunctionFormula*>(rhs)->setArgs(new FormulaList(lhs,
								rhs->args()));
    return rhs;
  }

  // both connectives are not c
  return new JunctionFormula(c,
			     new FormulaList(lhs,
					     new FormulaList(rhs)));
} // makeJunction

#if VDEBUG
// void TPTP::printStates(string extra)
// {
//   CALL("TPTP::printStates");
//   cout << ">>>>> states\n" << extra;
//   for (unsigned i = 0;i < _states.length(); i++) {
//     cout << ' ' << toString(_states[i]) << "\n";
//   }
//   cout << "<<<<< states\n";
// } // printStates

// void TPTP::printInts(string extra)
// {
//   CALL("TPTP::printInts");
//   cout << ">>>>> ints\n" << extra;
//   for (unsigned i = 0;i < _ints.length(); i++) {
//     cout << ' ' << _ints[i] << "\n";
//   }
//   cout << "<<<<< ints\n";
// } // printInts

const char* TPTP::toString(State s)
{
  switch (s) {
  case UNIT_LIST:
    return "UNIT_LIST";
  case CNF:
    return "CNF";
  case FOF:
    return "FOF";
  case VAMPIRE:
    return "VAMPIRE";
  case FORMULA:
    return "FORMULA";
  case END_FOF:
    return "END_FOF";
  case SIMPLE_FORMULA:
    return "SIMPLE_FORMULA";
  case END_FORMULA:
    return "END_FORMULA";
  case VAR_LIST:
    return "VAR_LIST";
  case ATOM:
    return "ATOM";
  case MID_ATOM:
    return "MID_ATOM";
  case ARGS:
    return "ARGS";
  case TERM:
    return "TERM";
  case END_TERM:
    return "END_TERM";
  case TAG:
    return "TAG";
  case INCLUDE:
    return "INCLUDE";
  case END_EQ:
    return "END_EQ";
  case TFF:
    return "TFF";
  case TYPE:
    return "TYPE";
  case END_TFF:
    return "END_TFF";
  default:
    cout << (int)s << "\n";
    ASS(false);
  }
}
#endif

/*
$let
$itef
$real
$rat
$int
$
$oType
$o
$iType
$i
$tType
$$
$equal
$distinct
$less
$lesseq
$greater
$greatereq
$evaleq
$is_int
$is_rat
$itett
$itetf
$uminus
$sum
$difference
$product
$to_int
$to_rat
$to_real
$thf
$tff
$fof
$cnf
$fot
*/
