/**
 * @file Statement.hpp
 * Defines class Program::Statement
 *
 * @since 20/08/2010, Torrevieja
 */

#ifndef __ProgramStatement__
#define __ProgramStatement__

#include "Expression.hpp"

using namespace std;

namespace Program {

/**
 * Statements used in programs
 * @since 20/08/2010, Torrevieja
 */
class Statement
{
public:
	/** Kinds of statement */
	enum Kind {
		/** assignment */
		ASSIGNMENT,
		/** block (a sequence of statements) */
		BLOCK,
		/* if-then-else */
		ITE,
		/** while-do */
		WHILE_DO,
		/** expression, e.g., function call */
		EXPRESSION
	};
	/** main constructor */
	explicit Statement(Kind kind) : _kind(kind) {}
protected:
	/** the kind */
	Kind _kind;
}; // class Statement

/**
 * Assignment
 * @since 20/08/2010, Torrevieja
 */
class Assignment
	: public Statement
{
public:
	Assignment(const Expression* lhs,const Expression* rhs);
protected:
	/** the lhs of the assignment */
	const Expression* _lhs;
	/** the rhs of the assignment */
	const Expression* _rhs;
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
protected:
	/** the length (number of statements) */
	int _length;
	/** the sequence of statements */
	const Statement** _statements;
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
	IfThenElse(const Expression* condition,const Statement* thenPart,const Statement* elsePart)
		: Statement(ITE),
			_condition(condition),
			_thenPart(thenPart),
			_elsePart(elsePart)
	{}
protected:
	/** the condition */
	const Expression* _condition;
	/** the then-part */
	const Statement* _thenPart;
	/** the else-part */
	const Statement* _elsePart;
}; // class IfThenElse

/**
 * while-do
 * @since 21/08/2010, Torrevieja
 */
class WhileDo
	: public Statement
{
public:
	/** constructor */
	WhileDo(const Expression* condition,const Statement* body)
		: Statement(WHILE_DO),
			_condition(condition),
			_body(body)
	{}
protected:
	/** the condition */
	const Expression* _condition;
	/** the body */
	const Statement* _body;
}; // class WhileDo

}
#endif // __ProgramStatement__
