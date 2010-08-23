/**
 *  @file Statement.cpp
 *  Implements class Program::Statement
 *
 * @since 20/08/2010, Torrevieja
 */

#include "Debug/Tracer.hpp"
#include "Expression.hpp"
#include "Type.hpp"
#include "Statement.hpp"

using namespace Program;

Assignment::Assignment(Expression* lhs,Expression* rhs)
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

	_statements = new Statement*[length];
#if VDEBUG
	for (int i = length-1;i >= 0;i--) {
		_statements[i] = 0;
	}
#endif
}

/** set the statement number @b n to @b st */
void Block::setStatement(unsigned n,Statement* st)
{
	CALL("Block::setStatement");

	ASS(n < _length);
	ASS(! _statements[n]);
	_statements[n] = st;
}

/** the variable updated by this assignment */
Variable* Assignment::variable() const
{
	CALL("Assignment::variable");
	switch (_lhs->kind()) {
	case Expression::VARIABLE:
		return static_cast<VariableExpression*>(_lhs)->variable();

  case Expression::ARRAY_APPLICATION:
		{
			Expression* arr = static_cast<ArrayApplicationExpression*>(_lhs)->array();
			return static_cast<VariableExpression*>(arr)->variable();
		}

	default:
		cout << _lhs->kind() << "\n";
		ASS(false);
	}
}

/** pretty-print the assignment to a stream with a given indentation */
void Assignment::prettyPrint(ostream& str,unsigned indent)
{
	for (int i = indent;i > 0;i--) str << ' ';
	str << _lhs->toString() << " = " << _rhs->toString() << ";\n";
}

/** pretty-print the block to a stream with a given indentation */
void Block::prettyPrint(ostream& str,unsigned indent)
{
	for (int i = indent;i > 0;i--) str << ' ';
	str << "{\n";
	for (unsigned n = 0;n < _length;n++) {
		_statements[n]->prettyPrint(str,indent+2);
	}
	for (int i = indent;i > 0;i--) str << ' ';
	str << "}\n";
}

/** pretty-print the statement to a stream with a given indentation */
void IfThenElse::prettyPrint(ostream& str,unsigned indent)
{
	for (int i = indent;i > 0;i--) str << ' ';
	str << "if (" << _condition->toString() <<  ")\n";
	_thenPart->prettyPrint(str,indent+2);
	for (int i = indent;i > 0;i--) str << ' ';
	str << "else\n";
	_elsePart->prettyPrint(str,indent+2);
}

/** pretty-print the statement to a stream with a given indentation */
void WhileDo::prettyPrint(ostream& str,unsigned indent)
{
	for (int i = indent;i > 0;i--) str << ' ';
	str << "while (" << _condition->toString() << ")\n";
	_body->prettyPrint(str,indent+2);
}

/** return the next substatement */
Statement* Statement::SubstatementIterator::next()
{
	CALL("Statement::SubstatementIterator::next");
	Statement* stat = _stack.pop();

	switch (stat->kind()) {
	case ASSIGNMENT:
	case EXPRESSION:
		break;
	case BLOCK:
		{
			Block* block = static_cast<Block*>(stat);
			for (unsigned n = 0;n < block->length();n++) {
				_stack.push(block->getStatement(n));
			}
		}
		break;
	case ITE:
		{
			IfThenElse* ite = static_cast<IfThenElse*>(stat);
			_stack.push(ite->thenPart());
			_stack.push(ite->elsePart());
		}
		break;
	case WHILE_DO:
		{
			WhileDo* loop = static_cast<WhileDo*>(stat);
			_stack.push(loop->body());
		}
		break;
	}

	return stat;
} // next

