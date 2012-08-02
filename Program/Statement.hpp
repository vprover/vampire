/**
 * @file Statement.hpp
 * Defines class Program::Statement
 *
 * @since 20/08/2010, Torrevieja
 */

#ifndef __ProgramStatement__
#define __ProgramStatement__

#include "Lib/Map.hpp"
#include "Lib/Stack.hpp"

using namespace std;
using namespace Lib;

namespace Program {

class Variable;
class Expression;
class WhileDo;
class Statement;

/**
 * Statements used in programs
 * @since 20/08/2010, Torrevieja
 */
class Statement
{
public:
  /**
   * Class for iterating over all sub-statements of a statement. It is
   * guaranteed that a statement is always returned before any of
   * its proper sub-statements.
   */
  class SubstatementIterator {
  public:
    /** create a substatement iterator for an statement @b expr */
    explicit SubstatementIterator(Statement* expr)
    {
      _stack.push(expr);
    }
    /** true if there is at least one substatement left */
    bool hasNext() const
    {
      return ! _stack.isEmpty();
    }
    Statement* next();
  protected:
    Stack<Statement*> _stack;
  };
  
  /** Kinds of statement */
  enum Kind {
    /** assignment */
    ASSIGNMENT,
    /** block (a sequence of statements) */
    BLOCK,
    /* if-then-else */
    ITE,
    /**if then statement*/
    ITS,
    /** while-do */
    WHILE_DO,
    /** expression, e.g., function call */
    EXPRESSION
  };
  /** main constructor */
  explicit Statement(Kind kind)
    : _kind(kind),
      _containingStatement(0),
      _nextStatement(0),
      _containingLoop(0)
  {}
  /** the kind of this statement */
  Kind kind() const { return _kind; }
  /** the containing statement */
  Statement* containingStatement() const { return _containingStatement; }
  /** the next (in the normal data flow) statement */
  Statement* nextStatement() const { return _nextStatement; }
  /** the containing loop */
  WhileDo* containingLoop() const { return _containingLoop; }
  /** set the containing statement */
  void setContainingStatement(Statement* st)
  {
    ASS(! _containingStatement);
    _containingStatement = st;
  }
  /** set the next statement */
  void setNextStatement(Statement* st) { _nextStatement = st; }
  /** set the containing loop */
  void setContainingLoop(WhileDo* loop) { _containingLoop = loop; }
  /** the map from variables to booleans: true if the variable is updated */
  Map<Variable*,bool>* variables() {return &_variables;}
  
  /** pretty-print the statement */
  virtual void prettyPrint(ostream& str,unsigned indent = 0) = 0;
protected:
  /** the kind */
  Kind _kind;
  /** containing statement */
  Statement* _containingStatement;
  /** the next (in the normal data flow) statement */
  Statement* _nextStatement;
  /** containing loop for analysis */
  WhileDo* _containingLoop;
  /** map from variables of this statement to boolean values: true if the variable is updated */
  Map<Variable*,bool> _variables;
}; // class Statement

/**
 * Assignment
 * @since 20/08/2010, Torrevieja
 */
class Assignment
  : public Statement
{
public:
  Assignment(Expression* lhs,Expression* rhs);
  /** the lhs of the assignment */
  Expression* lhs() const {return _lhs;}
  /** the rhs of the assignment */
  Expression* rhs() const {return _rhs;}
  Variable* variable() const;
  virtual void prettyPrint(ostream& str,unsigned indent=0);
protected:
  /** the lhs of the assignment */
  Expression* _lhs;
  /** the rhs of the assignment */
  Expression* _rhs;
}; // class Assignment

/**
 * Block of statements
 * @since 21/08/2010, Torrevieja
 */
class Block
  : public Statement
{
public:
  explicit Block(unsigned length);
  void setStatement(unsigned number,Statement* st);
  /** return the length (the number of statements) */
  unsigned length() { return _length; }
  /** return the statement number n */
  Statement* getStatement(unsigned n)
  {
    ASS(n < _length);
    ASS(_statements[n]);
    return _statements[n];
  }
  virtual void prettyPrint(ostream& str,unsigned indent=0);
protected:
  /** the length (number of statements) */
  unsigned _length;
  /** the sequence of statements */
  Statement** _statements;
}; // class Block

/**
 * if-then-else
 * @since 21/08/2010, Torrevieja
 */
class IfThenElse
  : public Statement
{
public:
  /** constructor */
  IfThenElse(Expression* condition,Statement* thenPart,Statement* elsePart)
    : Statement(ITE),
      _condition(condition),
      _thenPart(thenPart),
      _elsePart(elsePart)
  {}
  /** the condition */
  Expression* condition() const {return _condition;}
  /** the then-part */
  Statement* thenPart() const {return _thenPart;}
  /** the else-part */
  Statement* elsePart() const {return _elsePart;}
  virtual void prettyPrint(ostream& str,unsigned indent=0);
protected:
  /** the condition */
  Expression* _condition;
  /** the then-part */
  Statement* _thenPart;
  /** the else-part */
  Statement* _elsePart;
}; // class IfThenElse


/**
 * if-then statement
 * @since 07.2012, Vienna
 */
class IfThen
  : public Statement
{
public:
    IfThen(Expression* condition, Statement* thenPart)
      :Statement(ITS),
       _condition(condition),
       _thenPart(thenPart)
    {}
    /**the condition*/
    Expression* condition() const{return _condition;}
    /**the then-part*/
    Statement* thenPart() const {return _thenPart;}
    virtual void prettyPrint(ostream& str, unsigned indent=0);
protected:
     /**the condition*/
    Expression* _condition;
    /**the then-part*/
    Statement* _thenPart;
};//class IfThen

/**
 * while-do
 * @since 21/08/2010, Torrevieja
 */
class WhileDo
  : public Statement
{
public:
  /** constructor */
  WhileDo(Expression* condition,Statement* body)
    : Statement(WHILE_DO),
      _condition(condition),
      _body(body)
  {}
  /** the condition of the loop */
  Expression* condition() const {return _condition;}
  /** the body of the loop */
  Statement* body() const {return _body;}
  virtual void prettyPrint(ostream& str,unsigned indent=0);
protected:
  /** the condition */
  Expression* _condition;
  /** the body */
  Statement* _body;
}; // class WhileDo

}
#endif // __ProgramStatement__
