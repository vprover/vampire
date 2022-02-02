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
 * @file LispParser.cpp
 * Implements class LispParser
 *
 * @since 26/08/2009 Redmond
 */

#include <fstream>

#include "Lib/Stack.hpp"
#include "Lib/Int.hpp"

#include "LispLexer.hpp"
#include "LispParser.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

LispParser::LispParser(LispLexer& lexer)
  : _lexer(lexer),
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
          throw Exception("unmatched right parenthesis",t);
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
        throw Exception("unmatched left parenthesis",t);
      default:
        ASSERTION_VIOLATION;
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
vstring LispParser::Expression::toString(bool outerParentheses) const
{
  CALL("LispParser::Expression::toString");

  switch (tag) {
  case ATOM:
    return str;
  case LIST:
    {
      vstring result;
      if(outerParentheses) {
	result = "(";
      }
      for (List* l = list;l;l = l->tail()) {
	result += l->head()->toString();
	if (l->tail()) {
	  result += outerParentheses ? ' ' : '\n';
	}
      }
      if(outerParentheses) {
	result += ')';
      }
      return result;
    }
  }
  ASSERTION_VIOLATION;
} // LispParser::Expression::toString

/**
 * If expression corresponds to a unary function named @c funcionName,
 * return true and assign its argument to @c arg. Otherwise return false.
 */
bool LispParser::Expression::get1Arg(vstring functionName, Expression*& arg)
{
  CALL("LispParser::Expression::get1Arg");

  if(!isList()) {
    return false;
  }

  List::Iterator args(list);
  if(!args.hasNext()) { return false; }
  vstring name = args.next()->str;
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
bool LispParser::Expression::get2Args(vstring functionName, Expression*& arg1, Expression*& arg2)
{
  CALL("LispParser::Expression::get2Args");

  if(!isList()) {
    return false;
  }

  List::Iterator args(list);
  if(!args.hasNext()) { return false; }
  vstring name = args.next()->str;
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

/**
 * Create a new parser exception.
 * @since 17/07/2004 Turku
 */
LispParser::Exception::Exception(vstring message,const Token& token)
  : _message (message)
{
  _message += " in line ";
  _message += Int::toString(token.line);
  _message += " at ";
  _message += token.text;
} // LispParser::Exception::Exception

/**
 * Write itself to an ostream.
 * @since 17/07/2004 Helsinki Airport
 */
void LispParser::Exception::cry(ostream& out) const
{
  out << "Parser exception: " << _message << '\n';
} // Exception::cry

///////////////////////
// LispListReader
//

void LispListReader::lispError(LExpr* expr, vstring reason)
{
  CALL("LispListReader::lispError");

  if(expr) {
    USER_ERROR(reason+": "+expr->toString());
  }
  else {
    USER_ERROR(reason+": <eol>");
  }
}

/**
 * Report error with the current lisp element
 */
void LispListReader::lispCurrError(vstring reason)
{
  CALL("LispListReader::lispCurrError");

  if(hasNext()) {
    lispError(peekAtNext(), reason);
  }
  else {
    lispError(0, reason);
  }
}

LExpr* LispListReader::peekAtNext()
{
  CALL("LispListReader::peekAtNext");
  ASS(hasNext());

  return it.peekAtNext();
}

LExpr* LispListReader::readNext()
{
  CALL("LispListReader::readNext");
  ASS(hasNext());

  return it.next();
}

bool LispListReader::tryReadAtom(vstring& atom)
{
  CALL("LispListReader::tryReadAtom");

  if(!hasNext()) { return false; }

  LExpr* next = peekAtNext();
  if(next->isAtom()) {
    atom = next->str;
    ALWAYS(readNext()==next);
    return true;
  }
  return false;
}

vstring LispListReader::readAtom()
{
  CALL("LispListReader::readAtom");

  vstring atm;
  if(!tryReadAtom(atm)) {
    lispCurrError("atom expected");
  }
  return atm;
}

bool LispListReader::tryAcceptAtom(vstring atom)
{
  CALL("SMTLIBConcat::tryAcceptAtom");

  if(!hasNext()) { return false; }

  LExpr* next = peekAtNext();
  if(next->isAtom() && next->str==atom) {
    ALWAYS(readNext()==next);
    return true;
  }
  return false;
}

void LispListReader::acceptAtom(vstring atom)
{
  CALL("SMTLIBConcat::acceptAtom");

  if(!tryAcceptAtom(atom)) {
    lispCurrError("atom \""+atom+"\" expected");
  }
}

bool LispListReader::tryReadListExpr(LExpr*& e)
{
  CALL("LispListReader::tryReadListExpr");

  if(!hasNext()) { return false; }

  LExpr* next = peekAtNext();
  if(next->isList()) {
    e = next;
    ALWAYS(readNext()==next);
    return true;
  }
  return false;
}

LExpr* LispListReader::readListExpr()
{
  CALL("LispListReader::readListExpr");

  LExpr* list;
  if(!tryReadListExpr(list)) {
    lispCurrError("list expected");
  }
  return list;
}

bool LispListReader::tryReadList(LExprList*& list)
{
  CALL("LispListReader::tryReadList");

  LExpr* lstExpr;
  if(tryReadListExpr(lstExpr)) {
    list = lstExpr->list;
    return true;
  }
  return false;
}

LExprList* LispListReader::readList()
{
  CALL("LispListReader::readList");

  return readListExpr()->list;
}

bool LispListReader::tryAcceptList()
{
  CALL("LispListReader::tryAcceptList");
  LExprList* lst;
  return tryReadList(lst);
}
void LispListReader::acceptList()
{
  CALL("LispListReader::acceptList");
  readList();
}

void LispListReader::acceptEOL()
{
  CALL("LispListReader::acceptEOL");

  if(hasNext()) {
    lispCurrError("<eol> expected");
  }
}

bool LispListReader::lookAheadAtom(vstring atom)
{
  CALL("LispListReader::lookAheadAtom");

  if(!hasNext()) { return false; }
  LExpr* next = peekAtNext();
  return next->isAtom() && next->str==atom;
}

bool LispListReader::tryAcceptCurlyBrackets()
{
  CALL("LispListReader::tryAcceptCurlyBrackets");

  LExpr* next = peekAtNext();
  if(!next->isAtom() || next->str!="{") {
    return false;
  }
  unsigned depth = 1;
  readNext();
  while(depth!=0 && hasNext()) {
    next = readNext();

    if(!next->isAtom()) {
      continue;
    }
    if(next->str=="{") {
      depth++;
    }
    else if(next->str=="}") {
      depth--;
    }
  }
  if(depth!=0) {
    lispCurrError("unpaired opening curly bracket");
  }
  return true;
}

}
