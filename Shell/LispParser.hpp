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

namespace Shell {


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
    USE_ALLOCATOR(Expression);

    /** type of the expression */
    Tag tag;
    /** the value (for atoms and numbers) */
    std::string str;
    /** list of expressions */
    Lib::List<Expression*>* list;
    /** build a list expressions with the list initially empty */
    explicit Expression(Tag t)
      : tag(t),
	str("?"),
	list(0)
    {}
    /** build a string-values expression */
    Expression(Tag t,std::string s)
      : tag(t),
	str(s),
	list(0)
    {}
    std::string toString(bool outerParentheses=true) const;

    bool isList() const { return tag==LIST; }
    bool isAtom() const { return tag==ATOM; }

    bool get2Args(std::string functionName, Expression*& arg1, Expression*& arg2);
    bool get1Arg(std::string functionName, Expression*& arg);
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
    : public Lib::ParsingRelatedException
  {
  public:
    Exception (std::string message,const Token&);
    void cry (std::ostream&) const;
    ~Exception () {}
  protected:
    std::string _message;
  }; // Exception

private:
  /** lexer supplying tokens */
  LispLexer& _lexer;
  /** balance of parenthesis */
  int _balance;
}; // class LispParser

typedef LispParser::Expression LExpr;
typedef Lib::List<LExpr*> LExprList;


class LispListReader {
public:
  explicit LispListReader(LExpr* e) : it(nullptr)
  {
    if(!e->isList()) {
      lispError(e, "list expected");
    }
    it = LExprList::Iterator(e->list);
  }
  explicit LispListReader(LExprList* list) : it(list) {}

  [[noreturn]] void lispError(LExpr* expr, std::string reason="error");
  [[noreturn]] void lispCurrError(std::string reason="error");

  bool hasNext() { return it.hasNext(); }
  LExpr* peekAtNext();
  LExpr* readNext();
  LExpr* next() { return readNext(); }

  bool tryReadAtom(std::string& atom);
  std::string readAtom();

  bool tryReadListExpr(LExpr*& e);
  LExpr* readListExpr();

  bool tryReadList(LExprList*& list);
  LExprList* readList();

  bool tryAcceptAtom(std::string atom);
  void acceptAtom(std::string atom);
  void acceptAtom() { readAtom(); }

  bool tryAcceptList();
  void acceptList();

  void acceptEOL();

  bool lookAheadAtom(std::string atom);

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

  LispListWriter& operator<<(std::string s)
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
    ASS(!_destroyed);

    LExprList* res = 0;
    LExprList::pushFromIterator(Lib::Stack<LExpr*>::TopFirstIterator(_elements), res);
    return res;
  }

  LExpr* get() const
  {
    LExpr* res = new LExpr(LispParser::LIST);
    res->list = getList();
    return res;
  }

private:
#if VDEBUG
  bool _destroyed;
#endif
  Lib::Stack<LExpr*> _elements;
};

}

#endif

