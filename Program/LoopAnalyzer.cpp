/**
 *  @file LoopAnalyzer.cpp
 *  Simple Loop analysis
 *
 * @since 23/08/2010, Torrevieja
 */

#include "Debug/Tracer.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"

#include "Variable.hpp"
#include "Expression.hpp"
#include "Statement.hpp"
#include "Path.hpp"
#include "LoopAnalyzer.hpp"

using namespace Kernel;
using namespace Program;

/** Constructor, just saves the program */
LoopAnalyzer::LoopAnalyzer(WhileDo* loop)
  : _loop(loop)
{}

/**
 * Simple loop analysis. Does the following:
 * <ol>
 *   <li></li>
 *   <li></li>
 *   <li></li>
 * </ol>
 */
void LoopAnalyzer::analyze()
{
  CALL("LoopAnalyzer::analyze");

  cout << "Analyzing loop...\n";
  cout << "---------------------\n";
  _loop->prettyPrint(cout);
  cout << "---------------------\n";

  analyzeVariables();
  collectPaths();
  // output paths
  Stack<Path*>::Iterator it(_paths);
  while (it.hasNext()) {
    it.next()->prettyPrint(cout);
  }
  generateAxiomsForCounters();
}

/**
 * If the assignment has the form x = x + c, where x is an integer variable
 * and c an integer constant, return c. Otherwise, return 0.
 */
int LoopAnalyzer::isScalarIncrement(const Assignment* ass)
{
  CALL("LoopAnalyzer::isScalarIncrement");

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
Variable* LoopAnalyzer::isScalarAssignment(const Statement* st)
{	
  CALL("LoopAnalyzer::isScalarAssignment");
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
 * Analyze all variables in the loop:
 * <ol>
 * <li>Collect all updated variables into _updated</li>
 * <li>Collect all counters into _counters</li>
 * </ol>
 */
void LoopAnalyzer::analyzeVariables()
{
  CALL("LoopAnalyzer::analyzeVariables()");

  // find counters
  Map<Variable*,bool>::Iterator vars(*_loop->variables());
  // iterate over variables
  while (vars.hasNext()) {
    Variable* var;
    bool updated;
    vars.next(var,updated);
    cout << "Variable: " << var->name() << ": " << (updated ? "(updated)" : "constant") << "\n";
    if (updated) {
      _updatedVariables.insert(var);
      if (var->vtype()->kind() == Type::INT) {
	_counters.insert(var);
      }
    }
  }
  Statement::SubstatementIterator sit (_loop->body());
  while (sit.hasNext()) {
    Statement* stat = sit.next();
    Variable* var = isScalarAssignment(stat);
    if (! var) {
      continue;
    }
    if (! isScalarIncrement(static_cast<Assignment*>(stat))) {
      _counters.remove(var);
    }
  }
  Set<Variable*>::Iterator vit(_counters);
  while (vit.hasNext()) {
    cout << "Counter: " << vit.next()->name() << "\n";
  }
} 

/**
 * Collect all paths in the loop into _paths;
 */
void LoopAnalyzer::collectPaths()
{
  CALL("LoopAnalyzer::collectPaths");

  Stack<Path*> paths; // partial paths
  // statements corresponding to this path, normally then-parts of IfThenElse
  Stack<Statement*> statements;
  Path* path = Path::empty();
  Statement* stat = _loop->body();
  for (;;) {
    switch (stat->kind()) {
    case Statement::ASSIGNMENT:
      path = path->add(stat);
      stat = stat->nextStatement();
      break;
    case Statement::BLOCK:
      stat = stat->nextStatement();
      break;
    case Statement::ITE:
      {
	path = path->add(stat);
	IfThenElse* ite = static_cast<IfThenElse*>(stat);
	// save the else-path for further processing
	paths.push(path->add(ite->elsePart()));
	statements.push(ite->elsePart());
	// continue with the then-path
	stat = ite->thenPart();
	path = path->add(stat);
	stat = stat->nextStatement();
      }
      break;

    case Statement::WHILE_DO:
      ASS(false); // cannot yet work with embedded loops
    case Statement::EXPRESSION:
      ASS(false); // cannot yet work with procedure calls
    }
    if (stat != _loop) { // end of the body not reached
      continue;
    }
    _paths.push(path);
    if (paths.isEmpty()) {
      return;
    }
    path = paths.pop();
    stat = statements.pop();
  }
}

/**
 * Generate axioms for counters.
 */
void LoopAnalyzer::generateAxiomsForCounters()
{
  CALL("LoopAnalyzer::generateAxiomsForCounters");
  unsigned length = _paths.length();
  if (length == 0) {
    return;
  }
  DArray<int> increments(length);
  Set<Variable*>::Iterator vit(_counters);
  while (vit.hasNext()) {
    Variable* v = vit.next();
    for (int i = length-1;i >= 0;i--) {
      increments[i] = 0;
    }
    int pathNumber = 0;
    Stack<Path*>::Iterator pit(_paths);
    while (pit.hasNext()) {
      int inc = 0;
      Path* path = pit.next();
      Path::Iterator sit(path);
      while (sit.hasNext()) {
	Statement* stat = sit.next();
	if (v != isScalarAssignment(stat)) {
	  continue;
	}
	inc += isScalarIncrement(static_cast<Assignment*>(stat));
      }
      increments[pathNumber++] = inc;
    }
    int max = increments[length-1];
    int min = max;
    int gcd = max > 0 ? max : -max;
    for (int i = length-2;i >= 0;i--) {
      int inc = increments[i];
      if (inc > max) {
	max = inc;
      }
      if (inc < min) {
	min = inc;
      }
      if (inc > 0) {
	gcd = Int::gcd(gcd,inc);
      }
      else if (inc < 0) {
	gcd = Int::gcd(gcd,-inc);
      }
      cout << "Counter " << v->name() << ": " << min << " min, " << max << " max, " << gcd << " gcd\n";
      generateCounterAxiom(v->name(),min,max,gcd);
    }
  }
}

/**
 * Generate the axioms for a counter for the purpose of symbol elimination.
 * @param name the counter name
 * @param min the minimal increment of the counter over all paths
 * @param max the maximal increment of the counter over all paths
 */
void LoopAnalyzer::generateCounterAxiom(const string& name,int min,int max,int gcd)
{
  // value of the counter at position 0
  TermList c(Term::createConstant(name));
  unsigned fun = env.signature->addFunction(name,1);
  // term x0
  TermList x0;
  x0.makeVar(0);
  // term c(x0)
  TermList cx0(Term::create(fun,1,&x0));
  Theory* theory = Theory::instance();
  if (min == max) {
    if (gcd == 1 || gcd == -1) {
      // c + x0 or c - x0
      TermList sum(theory->fun2(gcd == 1 ? Theory::PLUS : Theory::MINUS,c,x0));
      // create c(x0) = c + x_0
      Literal* eq = Literal::createEquality(true,cx0,sum);
      Formula* f = new AtomicFormula(eq);
      cout << f->toString() << "\n";
      Clause c(1,Unit::ASSUMPTION,new Inference(Inference::PROGRAM_ANALYSIS));
      cout << c.toString() << "\n";
    }
  }
  // term c(
  
  // TermList 
  // Term* c0 = Term::create(cnt,0,
  // c0->makeSymbol(fun,arity);

  // // function of the loop counter

}
