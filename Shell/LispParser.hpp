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
 * @file LispParser.hpp
 * Defines class LispParser for parsing Lisp files.
 *
 * @since 26/08/2009 Redmond
 */

#ifndef __LispParser__
#define __LispParser__

#include "Forwards.hpp"
#include "Token.hpp"

#include "Lib/Exception.hpp"
#include "Lib/List.hpp"
#include "Lib/Portability.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VString.hpp"

namespace Shell {

using namespace std;
using namespace Lib;

class LispLexer;

/**
 * Class LispParser, implements a Lisp Parser.
 * @since 26/08/2009 Redmond
 */
class LispParser
{
public:
  /** Tags of Lisp expressions */
  enum Tag {
    /** atom */
    ATOM = 0,
    /** list */
    LIST = 1
  };

  /** expressions */
  struct Expression {
    CLASS_NAME(LispParser::Expression);
    USE_ALLOCATOR(Expression);

    /** type of the expression */
    Tag tag;
    /** the value (for atoms and numbers) */
    vstring str;
    /** list of expressions */
    List<Expression*>* list;
    /** build a list expressions with the list initially empty */
    explicit Expression(Tag t)
      : tag(t),
	str("?"),
	list(0)
    {}
    /** build a string-values expression */
    Expression(Tag t,vstring s)
      : tag(t),
	str(s),
	list(0)
    {}
    vstring toString(bool outerParentheses=true) const;

    bool isList() const { return tag==LIST; }
    bool isAtom() const { return tag==ATOM; }

    bool get2Args(vstring functionName, Expression*& arg1, Expression*& arg2);
    bool get1Arg(vstring functionName, Expression*& arg);
    bool getPair(Expression*& el1, Expression*& el2);
    bool getSingleton(Expression*& el);
  };

  typedef Lib::List<Expression*> List;

  explicit LispParser(LispLexer& lexer);
  Expression* parse();
  void parse(List**);

  /**
   * Class Exception. Implements parser exceptions.
   * @since 17/07/2004 Helsinki airport
   */
  class Exception 
    : public Lib::Exception
  {
  public:                                
    Exception (vstring message,const Token&);
    void cry (ostream&) const;
    ~Exception () {}
  protected:
    vstring _message;
  }; // Exception

private:
  /** lexer supplying tokens */
  LispLexer& _lexer;
  /** balance of parenthesis */
  int _balance;
}; // class LispParser

typedef LispParser::Expression LExpr;
typedef List<LExpr*> LExprList;


class LispListReader {
public:
  explicit LispListReader(LExpr* e)
  {
    CALL("LispListReader::LispListReader(LExpr*)");
    if(!e->isList()) {
      lispError(e, "list expected");
    }
    it = LExprList::Iterator(e->list);
  }
  explicit LispListReader(LExprList* list) : it(list) {}

  [[noreturn]] void lispError(LExpr* expr, vstring reason="error");
  [[noreturn]] void lispCurrError(vstring reason="error");

  bool hasNext() { return it.hasNext(); }
  LExpr* peekAtNext();
  LExpr* readNext();
  LExpr* next() { return readNext(); }

  bool tryReadAtom(vstring& atom);
  vstring readAtom();

  bool tryReadListExpr(LExpr*& e);
  LExpr* readListExpr();

  bool tryReadList(LExprList*& list);
  LExprList* readList();

  bool tryAcceptAtom(vstring atom);
  void acceptAtom(vstring atom);
  void acceptAtom() { readAtom(); }

  bool tryAcceptList();
  void acceptList();

  void acceptEOL();

  bool lookAheadAtom(vstring atom);

  bool tryAcceptCurlyBrackets();
private:
  LExprList::Iterator it;
};

class LispListWriter
{
public:
  LispListWriter()
  {
#if VDEBUG
    _destroyed = false;
#endif
  }

#if VDEBUG
  ~LispListWriter()
  {
    _destroyed = true;
  }
#endif

  LispListWriter& operator<<(vstring s)
  {
    _elements.push(new LExpr(LispParser::ATOM, s));
    return *this;
  }

  LispListWriter& operator<<(LExpr* e)
  {
    _elements.push(e);
    return *this;
  }

  LispListWriter& operator<<(const LispListWriter& e)
  {
    _elements.push(e.get());
    return *this;
  }

  LispListWriter& append(LExprList* lst)
  {
    _elements.loadFromIterator(LExprList::Iterator(lst));
    return *this;
  }

  LExprList* getList() const
  {
    CALL("LispListWriter::getList");
    ASS(!_destroyed);

    LExprList* res = 0;
    LExprList::pushFromIterator(Stack<LExpr*>::TopFirstIterator(_elements), res);
    return res;
  }

  LExpr* get() const
  {
    CALL("LispListWriter::get");

    LExpr* res = new LExpr(LispParser::LIST);
    res->list = getList();
    return res;
  }

private:
#if VDEBUG
  bool _destroyed;
#endif
  Stack<LExpr*> _elements;
};

}

#endif

