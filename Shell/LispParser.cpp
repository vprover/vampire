/**
 * @file LispParser.cpp
 * Implements class LispParser
 *
 * @since 26/08/2009 Redmond
 */

#include <fstream>

#include "../Lib/List.hpp"
#include "LispLexer.hpp"
#include "LispParser.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

LispParser::LispParser(LispLexer& lexer)
  : Parser(lexer),
    _balance(0)
{}

/**
 * @since 26/08/2009 Redmond
 */
LispParser::Expression* LispParser::parse()
{
  CALL("LispParser::parse/0");

  Expression* result = new Expression(LIST);
  parse(&result->list);
  return result;
} // parse()

/**
 * @since 26/08/2009 Redmond
 */
void LispParser::parse(List** expr)
{
  CALL("LispParser::parse/1");

  Token t;
  for (;;) {
    _lexer.readToken(t);
    switch (t.tag) {
    case TT_RPAR:
      if (_balance == 0) {
	throw ParserException("unmatched right parenthesis",t);
      }
      _balance--;
      return;
    case TT_LPAR:
      _balance++;
      {
	Expression* subexpr = new Expression(LIST);
	parse(&subexpr->list);
	List* sub = new List(subexpr);
	*expr = sub;
	expr = sub->tailPtr();
      }
      break;
    case TT_NAME:
    case TT_INTEGER:
    case TT_REAL:
    {
      Expression* subexpr = new Expression(ATOM,t.text);
      List* sub = new List(subexpr);
      *expr = sub;
      expr = sub->tailPtr();
      break;
    }
    case TT_EOF:
      if (_balance == 0) {
	return;
      }
      throw ParserException("unmatched left parenthesis",t);
#if VDEBUG
    default:
      ASS(false);
#endif
    }
  }
} // parse()

/**
 * Return a LISP string corresponding to this expression
 * @since 26/08/2009 Redmond
 */
string LispParser::Expression::toString() const
{
  CALL("LispParser::Expression::toString");

  switch (tag) {
  case ATOM:
    return str;
  case LIST:
    {
      string result = "(";
      for (List* l = list;l;l = l->tail()) {
	result += l->head()->toString();
	if (l->tail()) {
	  result += ' ';
	}
      }
      result += ')';
      return result;
    }
  }
} // LispParser::Expression::toString
