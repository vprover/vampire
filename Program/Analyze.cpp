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

/** Constructor, just saves the program */
Analyze::Analyze(Statement* program)
	: _program(program)
{}

/**
 * Simple program analysis. Does the following:
 * <ol>
 *   <li></li>
 *   <li></li>
 *   <li></li>
 * </ol>
 */
void Analyze::analyze()
{
	CALL("Analyze::analyze/0");

	_program->setContainingStatement(0);
	_program->setContainingLoop(0);
	analyzeSubstatements(_program);
	cout << "Loops found: " << _loops.size() << "\n";
	Set<WhileDo*>::Iterator loops(_loops);
	int cnt = 0;
	while (loops.hasNext()) {
		cnt++;
		cout << "Analyzing loop " << cnt << "\n";
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
		analyzeLoop(loop);
	}
}

/**
 * Part of program analysis. Does the following with the input statement:
 * <ol>
 *   <li>save all loops in _loops.</li>
 *   <li>with every substatement @b s:
 *     <ol>
 *       <li>save variables of @b s;</li>
 *       <li>save the containing statement and the containing loop of @b s</li>
 *     </ol></li>
 * </ol>
 */
void Analyze::analyzeSubstatements(Statement* statement)
{
	CALL("Analyze::analyze/1");

	Statement::SubstatementIterator sit(statement);
	while (sit.hasNext()) {
		statement = sit.next();
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
					st->setContainingStatement(statement);
					st->setContainingLoop(statement->containingLoop());
				}
			}
			break;
		case Statement::ITE:
			{
				IfThenElse* ite = static_cast<IfThenElse*>(statement);
				Statement* thenPart = ite->thenPart();
				thenPart->setContainingStatement(statement);
				thenPart->setContainingLoop(statement->containingLoop());
				Statement* elsePart = ite->elsePart();
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
} // analyzeSubstatements

/**
 * Add all variables of exp to the variable list of st and all
 * statements in which st occurs.
 * 
 */
void Analyze::addExpressionVariables(Expression* exp,Statement* statement)
{
	CALL("Analyze::addExpressionVariables");

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

/**
 * If the assignment has the form x = x + c, where x is an integer variable
 * and c an integer constant, return c. Otherwise, return 0.
 */
int Analyze::isScalarIncrement(const Assignment* ass)
{
	CALL("Analyze::isScalarIncrement");

	if (ass->lhs()->kind() != Expression::VARIABLE) {
		return 0;
	}
	Variable* x = static_cast<VariableExpression*>(ass->lhs())->variable();
	Expression* rhs = ass->rhs();
	if (rhs->kind() != Expression::FUNCTION_APPLICATION) {
		return 0;
	}
	FunctionApplicationExpression* app = static_cast<FunctionApplicationExpression*>(rhs);
	bool plus = (app->function() == ConstantFunctionExpression::integerPlus());
	if (! plus) {
		if (app->function() != ConstantFunctionExpression::integerMinus()) {
			return 0;
		}
	}
	// the expression is either s+t or s-t
	Expression* e1 = app->getArgument(0);
	Expression* e2 = app->getArgument(1);
	switch (e1->kind()) {
	case Expression::VARIABLE:
		if (e2->kind() != Expression::CONSTANT_INTEGER) {
			return 0;
		}
		break;
	case Expression::CONSTANT_INTEGER:
		if (e2->kind() != Expression::VARIABLE) {
			return 0;
		}
		else {
			Expression* e = e2;
			e2 = e1;
			e1 = e;
		}
		break;

	default:
		return 0;
	}
	// e1 is a variable and e2 is an integer constant
	if (static_cast<VariableExpression*>(e1)->variable() != x) {
		return 0;
	}
	return static_cast<ConstantIntegerExpression*>(e2)->value();
}

/**
 * If the statement is a scalar assignment to a variable x,
 * return this variable. Otherwise, return 0
 */
Variable* Analyze::isScalarAssignment(const Statement* st)
{	
	CALL("Analyze::isScalarAssignment");
	if (st->kind() != Statement::ASSIGNMENT) {
		return 0;
	}
	Expression* lhs = static_cast<const Assignment*>(st)->lhs();
	if (lhs->kind() != Expression::VARIABLE) {
		return 0;
	}
	return static_cast<VariableExpression*>(lhs)->variable();
}

/**
 * Procedure for analyzing loops. Does the following:
 * <ol>
 * <li></li>
 * </ol>
 */
void Analyze::analyzeLoop(WhileDo* loop)
{
	Map<Variable*,bool>::Iterator vars(*loop->variables());
	Set<Variable*> updatedVariables;
	Set<Variable*> counters;
	while (vars.hasNext()) {
		Variable* var;
		bool updated;
		vars.next(var,updated);
		if (updated) {
			updatedVariables.insert(var);
			if (var->vtype()->kind() == Type::INT) {
				counters.insert(var);
			}
		}
	}
	Statement::SubstatementIterator sit (loop->body());
	while (sit.hasNext()) {
		Statement* stat = sit.next();
		Variable* var = isScalarAssignment(stat);
		if (! var) {
			continue;
		}
		if (! isScalarIncrement(static_cast<Assignment*>(stat))) {
			// counters.remove(var);
		}
	}
}
