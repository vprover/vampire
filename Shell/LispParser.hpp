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

namespace Shell {

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
    USE_ALLOCATOR(Expression);

    /** type of the expression */
    Tag tag;
    /** the value (for atoms and numbers) */
    std::string str;
    /** list of expressions */
    List<Expression*>* list;
    int line;
    int col;
    /** build a list expressions with the list initially empty */
    explicit Expression(Tag t, int line = -1, int col = -1)
      : tag(t), str("?"), list(0), line(line), col(col) {}
    /** build a string-values expression */
    Expression(Tag t, std::string s, int line = -1, int col = -1)
      : tag(t), str(s), list(0), line(line), col(col) {}
    std::string toString(bool outerParentheses=true) const;
    std::string highlightSubexpression(Expression* expr) const;
    std::string getPosition() const;

    bool isList() const { return tag==LIST; }
    bool isAtom() const { return tag==ATOM; }
  };

  typedef Lib::List<Expression*> EList;

  explicit LispParser(LispLexer& lexer);
  Expression* parse();
  void parse(EList**);

  /**
   * Class Exception. Implements parser exceptions.
   * @since 17/07/2004 Helsinki airport
   */
  class Exception
    : public Lib::ParsingRelatedException
  {
  public:
    Exception (std::string message,const Token&);
    void cry (std::ostream&) const override;
    ~Exception () override {}
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
typedef List<LExpr*> LExprList;


class ErrorThrowingLispListReader {
public:
  ErrorThrowingLispListReader(LExpr* e, LExpr* root)
    : e(e), root(root), it(LExprList::Iterator(e->list))
  { ASS(e->isList()); }

  bool hasNext() { return it.hasNext(); }

  LExpr* readExpr();
  std::string readAtom();
  LExpr* readList();

  bool tryAcceptAtom(std::string atom);
  void acceptEOL();

private:
  LExpr* e;
  LExpr* root;
  LExprList::Iterator it;
};

}

#endif

