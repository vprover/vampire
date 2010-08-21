/**
 *  @file Statement.cpp
 *  Implements class Program::Statement
 *
 * @since 20/08/2010, Torrevieja
 */

#include "Debug/Tracer.hpp"
#include "Statement.hpp"

using namespace Program;

Assignment::Assignment(const Expression* lhs,const Expression* rhs)
	: Statement(ASSIGNMENT),
		_lhs(lhs),
		_rhs(rhs)
{
	CALL("Assignment::Assignment");
	ASS(lhs->lvalue());
	ASS(lhs->etype()->equals(rhs->etype()));
}


Block::Block(unsigned length)
	: Statement(BLOCK),
		_length(length)
{
	CALL("Block::Block");
	ASS(length > 0);

	_statements = new const Statement*[length];
#if VDEBUG
	for (int i = length-1;i >= 0;i--) {
		_statements[i] = 0;
	}
#endif
}

void Block::setStatement(unsigned number,Statement* st)
{
	CALL("Block::setStatement");

	ASS(number < _length);
	ASS(! _statements[number]);
	_statements[number] = st;
}
