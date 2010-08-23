/**
 *  @file Analyze.cpp
 *  Simple Program analysis
 *
 * @since 22/08/2010, Torrevieja
 */

#include "Lib/Stack.hpp"
#include "Variable.hpp"
#include "Expression.hpp"
#include "Statement.hpp"
#include "Analyze.hpp"

using namespace Program;

Analyze::Analyze(Statement* program)
	: _program(program)
{}

void Analyze::analyze()
{
	CALL("Analyze::analyze/0");
	_program->setContainingStatement(0);
	_program->setContainingLoop(0);
	analyze(_program);
	cout << "Loops found: " << _loops.numberOfElements() << "\n";
	Set<WhileDo*>::Iterator loops(_loops);
	int cnt = 0;
	while (loops.hasNext()) {
		cnt++;
		cout << "Loop " << cnt << "\n";
		WhileDo* loop = loops.next();
		cout << "---------------------\n";
		loop->prettyPrint(cout);
		cout << "---------------------\n";
		Map<Variable*,bool>::Iterator vars(*loop->variables());
		while (vars.hasNext()) {
			Variable* var;
			bool updated;
			vars.next(var,updated);
			cout << "Variable: " << var->name() << ": " << (updated ? "(updated)" : "constant") << "\n";
		}
	}
}

void Analyze::analyze(Statement* statement)
{
	CALL("Analyze::analyze/1");

	Stack<Statement*> stack;
	stack.push(statement);

	while (! stack.isEmpty()) {
		statement = stack.pop();
		switch (statement->kind()) {
		case Statement::ASSIGNMENT:
			{
				Assignment* ass = static_cast<Assignment*>(statement);
				// find the variable of this assignment
				Variable* v = ass->variable();
				for (Statement* st = statement;st;st = st->containingStatement()) {
					if (st->variables()->replaceOrInsert(v,true)) {
						break;
					}
				}
				addExpressionVariables(ass->lhs(),ass);
				addExpressionVariables(ass->rhs(),ass);
			}
			break;

		case Statement::BLOCK:
			{
				Block* block = static_cast<Block*>(statement);
				for (unsigned i = 0;i < block->length(); i++) {
					Statement* st = block->getStatement(i);
					stack.push(st);
					st->setContainingStatement(statement);
					st->setContainingLoop(statement->containingLoop());
				}
			}
			break;
		case Statement::ITE:
			{
				IfThenElse* ite = static_cast<IfThenElse*>(statement);
				Statement* thenPart = ite->thenPart();
				stack.push(thenPart);
				thenPart->setContainingStatement(statement);
				thenPart->setContainingLoop(statement->containingLoop());
				Statement* elsePart = ite->elsePart();
				stack.push(elsePart);
				elsePart->setContainingStatement(statement);
				elsePart->setContainingLoop(statement->containingLoop());
				addExpressionVariables(ite->condition(),ite);
			}
			break;

		case Statement::WHILE_DO:
			{
				// WhileDo* loop = static_cast<WhileDo*>(statement); // to please my EMACS
				WhileDo* loop = (WhileDo*)statement;
			  Statement* body = loop->body();
				stack.push(body);
				body->setContainingStatement(statement);
				body->setContainingLoop(loop);
				_loops.insert(loop);
				addExpressionVariables(loop->condition(),loop);
		  }
		  break;
	
	  case Statement::EXPRESSION:
			// cannot yet handle procedure calls
			ASS(false);
		}
	}
}

/**
 * Add all variables of exp to the variable list of st and all
 * statements in which st occurs.
 * 
 */
void Analyze::addExpressionVariables(Expression* exp,Statement* statement)
{
	Expression::SubexpressionIterator it(exp);
	while (it.hasNext()) {
		exp = it.next();
		if (exp->kind() != Expression::VARIABLE) {
			continue;
		}
		VariableExpression* var = static_cast<VariableExpression*>(exp);
		// find the variable of this assignment
		Variable* v = var->variable();
		for (Statement* st = statement;st;st = st->containingStatement()) {
			if (st->variables()->find(v)) {
				break;
			}
			st->variables()->insert(v,false);
		}
	}
}
