/**
 *  @file Analyze.cpp
 *  Simple Program analysis
 *
 * @since 22/08/2010, Torrevieja
 */

#include "Lib/Stack.hpp"
#include "Lib/List.hpp"
#include "Variable.hpp"
#include "Expression.hpp"
#include "Statement.hpp"
#include "Analyze.hpp"
#include "LoopAnalyzer.hpp"

using namespace Program;
namespace Kernel{
  class Unit;
}
using namespace Kernel;
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
    lan.runSEI();
  }
}

/**
 * AV: somethings is wrong with this function. It iterates over loops, but uses only the
 * first loop. Also, in the previous version it did not return if there were no loops.
 */
List<Unit* >* Analyze::getUnits()
{
  CALL("Analyze::getUnits");
  analyzeSubstatements(_program);
  cout << "Loops found: " << _loops.size() << "\n";
  Set<WhileDo*>::Iterator loops(_loops);
  while (loops.hasNext()) {
    WhileDo* loop = loops.next();
    LoopAnalyzer lan(loop);
    lan.analyze();
    return lan.getUnits();
  }
  return 0;
} // getUnits

bool Analyze::checkForIf(Statement* statement)
{
  CALL("Analyze::checkForIf");

  Statement::SubstatementIterator sit(statement);
  while(sit.hasNext())
  {
    switch((sit.next())->kind())
    {
    case Statement::ITE :
    case Statement::ITS :
      return true;
      break;
    default:
      break;
    }
  }

  return false;
}

Statement* Analyze::concatenateStatements(Statement* block, List<Statement* >* list){
  CALL("Analyze::concatenateStatements");
  Block* orig = static_cast<Block* >(block);
  unsigned length = list->length() + orig->length();
  Block* finalStatement = new Block(length);
  unsigned n = 0 ;
  List<Statement* >::Iterator ite(list);
  while(ite.hasNext())
    finalStatement->setStatement(n++, ite.next());

  unsigned start = list->length();
  for(unsigned i = start ; i < length ; i++)
    finalStatement->setStatement(i, orig->getStatement(i - start));

  return static_cast<Statement* >(finalStatement);

}
/**
 * should introduce the updated values into the condition.
 * TODO implement the actual rewriting of
 * of the condition
 */
Expression* Analyze::treatCondition(Expression* condition, List<Statement* >* list)
{
  CALL("Analyze::treatCondition");

  // List<Variable* >* variableList(0);
  // List<Statement* >::Iterator ite(list);
  // while(ite.hasNext())
  // {
  //   Statement* s = ite.next();
  //   switch(s->kind()){
  //   case Statement::ASSIGNMENT:
  //     {
  // 	Assignment* ass = static_cast<Assignment* >(s);
  // 	Expression* lhs = ass->lhs();
  //     }
  //     break;
  //   default:
  //     ASS(false);
  //     break;

  //   }
  // }
  return condition;
}
/**
 * IMPORTANT! the preprocessing of a statement is not fully implemented, hence cannot be used yet.
 * Instead we handle this into the LoopAnalyzer. This is still under consideration if is needed or not.
 *
 * This does the preprocessing needed in order for the loop analyzer to function correctly.
 * Does the following: retrieve the loop body and check if it starts with an if structure.
 * If this is the case, then nothing is done. Otherwise, we rewrite the body such that it
 * starts with a if statement -- in case it containes one --( take all statements which
 * appear before the if, and place them in the if body, and modify the condition of the
 * if so that it uses the updated value)
 */
void Analyze::preprocessStatement(Statement* statement)
{
  CALL("Analyze::preprocessStatement");
  
  if (statement->kind() == Statement::WHILE_DO) {
    WhileDo* wh = static_cast<WhileDo*>(statement);
    Statement* body = wh->body();
    switch (body->kind()) {
    case Statement::BLOCK: { //aici trebuie sa muncim!
      Block* block = static_cast<Block* >(body);
      if (!checkForIf(static_cast<Statement* >(body)))
	break;
      unsigned length = block->length();
      if (length == 1) {
	break;
      }
      List<Statement* >* statements(0);
      unsigned ifPosition = 0; // MS: added initialization to silence a warning (could be hiding a bug?)
      for (unsigned i = 0; i < length; i++) {
	Statement* s = block->getStatement(i);
	if (s->kind() == Statement::ITE || s->kind() == Statement::ITS) {
	  ifPosition = i;
	  break;
	}
	else {
	  statements = statements->addLast(s);
	}
      }

      // get the if and rewrite it so that it comply with what we want
      // TODO this can be written as a separate function!
      Statement* ifS = block->getStatement(ifPosition);
      switch (ifS->kind()) {
      case Statement::ITE:
	{
	  IfThenElse* ite = static_cast<IfThenElse* >(ifS);
	  Statement* then,* els;
	  then = ite->thenPart();
	  els = ite->elsePart();
	  then = concatenateStatements(then, statements);
	  els = concatenateStatements(els, statements);
	  Expression* condition = ite->condition();
	  condition = treatCondition(condition, statements);
	}
	break;
      case Statement::ITS:
	break;
      default:
	ASSERTION_VIOLATION;
      }
    }
      break;
    default:
      break;
    }
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
	Statement* st = statement;
	if (!st->variables()->replaceOrInsert(v, true)) {
	  while (st->containingStatement()) {
	    st = st->containingStatement();
	    if (st->variables()->replaceOrInsert(v, true)) {
	      break;
	    }
	  }
	}
	//Add the variable to the containigLoop as well
	//in case we don't add this we mess up for mixed statements (ex: ass, if, ass)
	if (statement->containingLoop()) {
	  statement->containingLoop()->variables()->replaceOrInsert(v, true);
	}
	addExpressionVariables(ass->lhs(), ass);
	addExpressionVariables(ass->rhs(), ass);
      }
      break;

    case Statement::BLOCK: 
      {
	Block* block = static_cast<Block*>(statement);
	unsigned length = block->length();
	for (unsigned i = 0; i < length; i++) {
	  Statement* st = block->getStatement(i);
	  st->setNextStatement(i == length - 1
			         ? block->nextStatement()
			         : block->getStatement(i + 1));
	st->setContainingStatement(statement);
	st->setContainingLoop(statement->containingLoop());
	}
	block->setNextStatement(block->getStatement(0));
      }
      break;
    case Statement::ITE: {
      IfThenElse* ite = static_cast<IfThenElse*>(statement);
      Statement* thenPart = ite->thenPart();
      thenPart->setNextStatement(ite->nextStatement());
      thenPart->setContainingStatement(statement);
      thenPart->setContainingLoop(statement->containingLoop());
      Statement* elsePart = ite->elsePart();
      // Block* block = static_cast<Block*>(elsePart);
      elsePart->setNextStatement(ite->nextStatement());
      elsePart->setContainingStatement(statement);
      elsePart->setContainingLoop(statement->containingLoop());
      addExpressionVariables(ite->condition(), ite);
    }
      break;
      //TODO: try to get rid of the if-then statements -- should be able to rewrite into if-then-else
    case Statement::ITS: {
      IfThen* it = static_cast<IfThen*>(statement);
      Statement* thenPart = it->thenPart();
      thenPart->setNextStatement(it->nextStatement());
      thenPart->setContainingStatement(statement);
      thenPart->setContainingLoop(statement->containingLoop());
      addExpressionVariables(it->condition(), it);
    }
      break;

    case Statement::WHILE_DO: {
      WhileDo* loop = static_cast<WhileDo*>(statement); // to please my EMACS
      //WhileDo* loop = (WhileDo*)statement;
      Statement* body = loop->body();
      body->setNextStatement(loop);
      body->setContainingStatement(statement);
      body->setContainingLoop(loop);
      _loops.insert(loop);
      addExpressionVariables(loop->condition(), loop);
    }
      break;

    case Statement::EXPRESSION:
      // cannot yet handle procedure calls
      ASS(false);
    }
  }
} // analyzeSubstatements

/**
 * Add all variables of exp to the variable list of statement and all
 * statements in which statement occurs.
 * 
 */
void Analyze::addExpressionVariables(Expression* exp, Statement* statement)
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
    for (Statement* st = statement; st; st = st->containingStatement()) {
      //if the variable is already in the list break
      if (st->variables()->find(v)) {
	break;
      }
      //insert the variable as not bein updated
      st->variables()->insert(v, false);
    }
  }
}
