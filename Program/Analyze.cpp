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
#include "LoopAnalyzer.hpp"

using namespace Program;

/** Constructor, just saves the program */
Analyze::Analyze(Statement* program)
  : _program(program)
{}

/**
 * Simple program analysis. Does the following:
 * <ol>
 *   <li>save all loops in _loops.</li>
 *   <li>with every substatement @b s:
 *     <ol>
 *       <li>save variables of @b s;</li>
 *       <li>save the containing statement and the containing loop of @b s</li>
 *     </ol></li>
 *   <li>Analyzes all loops using LoopAnalyzer</li>
 * </ol>
 */
void Analyze::analyze()
{
  CALL("Analyze::analyze/0");

  analyzeSubstatements(_program);
  cout << "Loops found: " << _loops.size() << "\n";
  Set<WhileDo*>::Iterator loops(_loops);
  while (loops.hasNext()) {
    WhileDo* loop = loops.next();
    LoopAnalyzer lan(loop);
    lan.analyze();
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
	unsigned length = block->length();
	for (unsigned i = 0;i < length; i++) {
	  Statement* st = block->getStatement(i);
	  st->setNextStatement(i == length-1 ?
			       block->nextStatement() :
			       block->getStatement(i+1));
	  st->setContainingStatement(statement);
	  st->setContainingLoop(statement->containingLoop());
	}
	block->setNextStatement(block->getStatement(0));
      }
      break;
    case Statement::ITE:
      {
	IfThenElse* ite = static_cast<IfThenElse*>(statement);
	Statement* thenPart = ite->thenPart();
	thenPart->setNextStatement(ite->nextStatement());
	thenPart->setContainingStatement(statement);
	thenPart->setContainingLoop(statement->containingLoop());
	Statement* elsePart = ite->elsePart();
	elsePart->setNextStatement(ite->nextStatement());
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
	body->setNextStatement(loop);
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
