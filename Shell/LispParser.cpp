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

#include "Lib/Stack.hpp"
#include "Lib/Int.hpp"

#include "LispLexer.hpp"
#include "LispParser.hpp"

namespace Shell {

using namespace std;
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
  Expression* result = new Expression(LIST);
  parse(&result->list);
  return result;
} // parse()

/**
 * @since 26/08/2009 Redmond
 */
void LispParser::parse(EList** expr0)
{
  static Stack<EList**> stack;
  stack.reset();

  stack.push(expr0);

  Token t;

  EList** expr = expr0;
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
	  Expression* subexpr = new Expression(LIST, t.line, t.col);
	  EList* sub = new EList(subexpr);
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
        Expression* subexpr = new Expression(ATOM, t.text, t.line, t.col);
        EList* sub = new EList(subexpr);
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
std::string LispParser::Expression::toString(bool outerParentheses) const
{
  switch (tag) {
  case ATOM:
    return str;
  case LIST:
    {
      std::string result;
      if(outerParentheses) {
	result = "(";
      }
      for (EList* l = list;l;l = l->tail()) {
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

string LispParser::Expression::highlightSubexpression(Expression* se) const
{
  ASS_EQ(tag, LIST);

  static Expression space(ATOM, " ");
  string res1;
  string res2;
  Stack<const Expression*> todo;
  todo.push(this);

  while (todo.isNonEmpty()) {
    auto expr = todo.pop();
    if (!expr) {
      res1 += ')';
      res2 += ' ';
      continue;
    }
    if (expr == se) {
      auto sres = expr->toString();
      res1 += sres;
      res2 += string(sres.size(), '^');
      continue;
    }
    switch (expr->tag) {
      case ATOM: {
        res1 += expr->str;
        res2 += string(expr->str.size(), ' ');
        break;
      }
      case LIST: {
        res1 += '(';
        res2 += ' ';
        Stack<const Expression*> inner;
        for (EList* l = expr->list; l; l = l->tail()) {
          inner.push(l->head());
          if (l->tail()) {
            inner.push(&space);
          }
        }
        inner.push(nullptr);
        todo.loadFromIterator(inner.iter());
        break;
      }
    }
  }
  return res1 + "\n" + res2;
} // LispParser::Expression::highlightSubexpression

string LispParser::Expression::getPosition() const
{
  ASS(line != -1 && col != -1);
  return "line " + Int::toString(line) + " col " + Int::toString(col);
}

/**
 * Create a new parser exception.
 * @since 17/07/2004 Turku
 */
LispParser::Exception::Exception(std::string message,const Token& token)
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
void LispParser::Exception::cry(std::ostream& out) const
{
  out << "Parser exception: " << _message << '\n';
} // Exception::cry

///////////////////////
// ErrorThrowingLispListReader
//

LExpr* ErrorThrowingLispListReader::readExpr()
{
  if (!it.hasNext()) {
    USER_ERROR("Unexpected end of list at " + e->getPosition() + "\n" + root->highlightSubexpression(e));
  }
  return it.next();
}

string ErrorThrowingLispListReader::readAtom()
{
  auto exp = readExpr();
  if (!exp->isAtom()) {
    USER_ERROR("Expected atom at " + exp->getPosition() + "\n" + root->highlightSubexpression(exp));
  }
  return exp->str;
}

LExpr* ErrorThrowingLispListReader::readList()
{
  auto exp = readExpr();
  if (!exp->isList()) {
    USER_ERROR("Expected list at " + exp->getPosition() + "\n" + root->highlightSubexpression(exp));
  }
  return exp;
}

bool ErrorThrowingLispListReader::tryAcceptAtom(std::string atom)
{
  if (!it.hasNext()) { return false; }

  auto n = it.peekAtNext();
  if(n->isAtom() && n->str==atom) {
    ALWAYS(it.next()==n);
    return true;
  }
  return false;
}

void ErrorThrowingLispListReader::acceptEOL()
{
  if (it.hasNext()) {
    USER_ERROR("Expected end of list at " + e->getPosition() + "\n" + root->highlightSubexpression(e));
  }
}

}
