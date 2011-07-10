/**
 * @file LispParser.cpp
 * Implements class LispParser
 *
 * @since 26/08/2009 Redmond
 */

#include <fstream>

#include "Lib/Stack.hpp"

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

///**
// * @since 26/08/2009 Redmond
// */
//void LispParser::parse(List** expr)
//{
//  CALL("LispParser::parse/1");
//
//  Token t;
//  for (;;) {
//    _lexer.readToken(t);
//    switch (t.tag) {
//    case TT_RPAR:
//      if (_balance == 0) {
//	throw ParserException("unmatched right parenthesis",t);
//      }
//      _balance--;
//      return;
//    case TT_LPAR:
//      _balance++;
//      {
//	Expression* subexpr = new Expression(LIST);
//	parse(&subexpr->list);
//	List* sub = new List(subexpr);
//	*expr = sub;
//	expr = sub->tailPtr();
//      }
//      break;
//    case TT_NAME:
//    case TT_INTEGER:
//    case TT_REAL:
//    {
//      Expression* subexpr = new Expression(ATOM,t.text);
//      List* sub = new List(subexpr);
//      *expr = sub;
//      expr = sub->tailPtr();
//      break;
//    }
//    case TT_EOF:
//      if (_balance == 0) {
//	return;
//      }
//      throw ParserException("unmatched left parenthesis",t);
//#if VDEBUG
//    default:
//      ASS(false);
//#endif
//    }
//  }
//} // parse()

/**
 * @since 26/08/2009 Redmond
 */
void LispParser::parse(List** expr0)
{
  CALL("LispParser::parse/1");

  static Stack<List**> stack;
  stack.reset();

  stack.push(expr0);

  Token t;

  List** expr = expr0;
  for(;;) {
  new_parsing_level:
    for (;;) {
      _lexer.readToken(t);
      switch (t.tag) {
      case TT_RPAR:
        if (_balance == 0) {
          throw ParserException("unmatched right parenthesis",t);
        }
        _balance--;
        goto parsing_level_done;
      case TT_LPAR:
        _balance++;
        {
	  Expression* subexpr = new Expression(LIST);
	  List* sub = new List(subexpr);
	  *expr = sub;
	  expr = sub->tailPtr();
	  stack.push(expr);
	  expr = &subexpr->list;
	  goto new_parsing_level;
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
        ASSERTION_VIOLATION;
  #endif
      }
    }

  parsing_level_done:
    ASS(stack.isNonEmpty());
    expr = stack.pop();
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

/**
 * If expression corresponds to a unary function named @c funcionName,
 * return true and assign its argument to @c arg. Otherwise return false.
 */
bool LispParser::Expression::get1Arg(string functionName, Expression*& arg)
{
  CALL("LispParser::Expression::get1Arg");

  if(!isList()) {
    return false;
  }

  List::Iterator args(list);
  if(!args.hasNext()) { return false; }
  string name = args.next()->str;
  if(name!=functionName) { return false; }

  if(!args.hasNext()) { return false; }
  Expression* tmpArg = args.next();

  if(args.hasNext()) { return false; }

  arg = tmpArg;
  return true;
}

/**
 * If expression corresponds to a binary function named @c funcionName,
 * return true and assign its arguments to @c arg1 and @c arg2. Otherwise
 * return false.
 */
bool LispParser::Expression::get2Args(string functionName, Expression*& arg1, Expression*& arg2)
{
  CALL("LispParser::Expression::get2Args");

  if(!isList()) {
    return false;
  }

  List::Iterator args(list);
  if(!args.hasNext()) { return false; }
  string name = args.next()->str;
  if(name!=functionName) { return false; }

  if(!args.hasNext()) { return false; }
  Expression* tmpArg1 = args.next();

  if(!args.hasNext()) { return false; }
  Expression* tmpArg2 = args.next();

  if(args.hasNext()) { return false; }

  arg1 = tmpArg1;
  arg2 = tmpArg2;
  return true;
}

/**
 * If expression is a list of two elements, return true and assign them
 * into @c el1 and @c el2.
 */
bool LispParser::Expression::getPair(Expression*& el1, Expression*& el2)
{
  CALL("LispParser::Expression::getPair");

  if(!isList()) {
    return false;
  }

  List::Iterator args(list);
  if(!args.hasNext()) { return false; }
  Expression* tmpEl1 = args.next();

  if(!args.hasNext()) { return false; }
  Expression* tmpEl2 = args.next();

  if(args.hasNext()) { return false; }

  el1 = tmpEl1;
  el2 = tmpEl2;
  return true;
}

bool LispParser::Expression::getSingleton(Expression*& el)
{
  CALL("LispParser::Expression::getSingleton");

  if(!isList()) {
    return false;
  }

  List::Iterator args(list);
  if(!args.hasNext()) { return false; }
  Expression* tmpEl = args.next();

  if(args.hasNext()) { return false; }

  el = tmpEl;
  return true;
}
