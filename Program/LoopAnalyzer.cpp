/**
 *  @file LoopAnalyzer.cpp
 *  Simple Loop analysis
 *
 * @since 23/08/2010, Torrevieja
 */

#include "Debug/Tracer.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Int.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
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
  : _loop(loop),
    _units(0)
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
  UnitList::Iterator units(_units);
  while (units.hasNext()) {
    cout << units.next()->toString() << "\n";
  }
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
    VariableInfo* vinfo = new VariableInfo;
    _variableInfo.insert(var,vinfo);
    cout << "Variable: " << var->name() << ": " << (updated ? "(updated)" : "constant") << "\n";
    bool scalar = (var->vtype()->kind() == Type::INT);
    vinfo->scalar = scalar;
    if (updated) {
      vinfo->updated = true;
      vinfo->counter = scalar;
    }
    else {
      vinfo->updated = true;
      vinfo->counter = false;
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
      _variableInfo.get(var)->counter = false;
    }
  }
  VariableMap::Iterator vit(_variableInfo);
  while (vit.hasNext()) {
    Variable* v;
    VariableInfo* vinfo;
    vit.next(v,vinfo);

    // adding the symbol to the signature
    unsigned arity = vinfo->scalar ? 0 : 1;
    string name(v->name());
    vinfo->signatureNumber = env.signature->addFunction(name,arity);
    if (arity == 0) {
      vinfo->constant = Term::create(vinfo->signatureNumber,0,0);
    }
    if (vinfo->updated) {
      vinfo->extraSignatureNumber = env.signature->addFunction(name,arity+1);
    }
    
    if (vinfo->counter) {
      cout << "Counter: " << v->name() << "\n";
    }
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

  VariableMap::Iterator vit(_variableInfo);
  while (vit.hasNext()) {
    Variable* v;
    VariableInfo* vinfo;
    vit.next(v,vinfo);
    if (! vinfo->counter) {
      continue;
    }
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
    Clause* cls = new(1) Clause(1,Unit::ASSUMPTION,new Inference(Inference::PROGRAM_ANALYSIS));
    Literal* eq;
    if (gcd == 1 || gcd == -1) {
      // c +- x0
      TermList sum(theory->fun2(gcd == 1 ? Theory::PLUS : Theory::MINUS,c,x0));
      // create c(x0) = c + x_0
      eq = Literal::createEquality(true,cx0,sum);
    }
    else {
      // gcd != 1
      // term gcd*x0
      TermList c_gcd(theory->getRepresentation(gcd));
      TermList gcd_x0(theory->fun2(Theory::MULTIPLY,c_gcd,x0));
      // c +- gcd*x0
      TermList sum(theory->fun2(gcd > 0 ? Theory::PLUS : Theory::MINUS,c,gcd_x0));
      // create c(x0) = c + gcd*x_0
      eq = Literal::createEquality(true,cx0,sum);
    }
    (*cls)[0] = eq;
    _units = _units->cons(cls);
    return;
  }

  // min != max
  // Generate the upper bound axiom c(x0) <= c + max*x_0
  if (max == 0) { // c(x0) <= c
    Literal* ineq = theory->pred2(Theory::INT_LESS_EQUAL,true,cx0,c);
    Clause* cls = new(1) Clause(1,Unit::ASSUMPTION,new Inference(Inference::PROGRAM_ANALYSIS));
    (*cls)[0] = ineq;
    _units = _units->cons(cls);
  }
  else if (max == 1 || max == -1) { // c(x0) <= c +- x_0
    TermList sum(theory->fun2(max == 1 ? Theory::PLUS : Theory::MINUS,c,x0));
    Literal* ineq = theory->pred2(Theory::INT_LESS_EQUAL,true,cx0,sum);
    Clause* cls = new(1) Clause(1,Unit::ASSUMPTION,new Inference(Inference::PROGRAM_ANALYSIS));
    (*cls)[0] = ineq;
    _units = _units->cons(cls);
  }
  else {
    TermList c_max(theory->getRepresentation(max));
    TermList max_x0(theory->fun2(Theory::MULTIPLY,c_max,x0));
    // c +- max*x0
    TermList sum(theory->fun2(max > 0 ? Theory::PLUS : Theory::MINUS,c,max_x0));
    Literal* ineq = theory->pred2(Theory::INT_LESS_EQUAL,true,cx0,sum);
    Clause* cls = new(1) Clause(1,Unit::ASSUMPTION,new Inference(Inference::PROGRAM_ANALYSIS));
    (*cls)[0] = ineq;
    _units = _units->cons(cls);
  }

  // and the lower bound axiom c(x0) >= c + min*x_0
  if (min == 0) { // c(x0) >= c
    Literal* ineq = theory->pred2(Theory::INT_GREATER_EQUAL,true,cx0,c);
    Clause* cls = new(1) Clause(1,Unit::ASSUMPTION,new Inference(Inference::PROGRAM_ANALYSIS));
    (*cls)[0] = ineq;
    _units = _units->cons(cls);
  }
  else if (min == 1 || min == -1) { // c(x0) >= c +- x_0
    TermList sum(theory->fun2(min == 1 ? Theory::PLUS : Theory::MINUS,c,x0));
    Literal* ineq = theory->pred2(Theory::INT_GREATER_EQUAL,true,cx0,sum);
    Clause* cls = new(1) Clause(1,Unit::ASSUMPTION,new Inference(Inference::PROGRAM_ANALYSIS));
    (*cls)[0] = ineq;
    _units = _units->cons(cls);
  }
  else {
    TermList c_min(theory->getRepresentation(min));
    TermList min_x0(theory->fun2(Theory::MULTIPLY,c_min,x0));
    // c +- min*x0
    TermList sum(theory->fun2(min > 0 ? Theory::PLUS : Theory::MINUS,c,min_x0));
    Literal* ineq = theory->pred2(Theory::INT_GREATER_EQUAL,true,cx0,sum);
    Clause* cls = new(1) Clause(1,Unit::ASSUMPTION,new Inference(Inference::PROGRAM_ANALYSIS));
    (*cls)[0] = ineq;
    _units = _units->cons(cls);
  }

  // generate density axioms
  if (max == 1) {
    // generate J > I & c(J) > V & V > c(I) -> (E K)(J > K & K > I & c(K) = V)
    TermList I;
    I.makeVar(0);
    TermList J;
    J.makeVar(1);
    TermList K;
    K.makeVar(2);
    TermList V;
    V.makeVar(3);
    TermList cI(Term::create(fun,1,&I));
    TermList cJ(Term::create(fun,1,&J));
    TermList cK(Term::create(fun,1,&K));
    Formula* JgreaterI = new AtomicFormula(theory->pred2(Theory::INT_GREATER,true,J,I));
    Formula* cJgreaterV = new AtomicFormula(theory->pred2(Theory::INT_GREATER,true,cJ,V));
    Formula* VgreatercI = new AtomicFormula(theory->pred2(Theory::INT_GREATER,true,V,cI));
    FormulaList* left = (new FormulaList(VgreatercI))->cons(cJgreaterV)->cons(JgreaterI);
    Formula* lhs = new JunctionFormula(AND,left);
    Formula* JgreaterK = new AtomicFormula(theory->pred2(Theory::INT_GREATER,true,J,K));
    Formula* KgreaterI = new AtomicFormula(theory->pred2(Theory::INT_GREATER,true,K,I));
    Formula* cKequalV = new AtomicFormula(Literal::createEquality(true,cK,V));
    FormulaList* right = (new FormulaList(JgreaterK))->cons(KgreaterI)->cons(cKequalV);
    Formula* rhs = new QuantifiedFormula(EXISTS,
					 new Formula::VarList(2),
					 new JunctionFormula(AND,right));
    _units = _units->cons(new FormulaUnit(new BinaryFormula(IMP,lhs,rhs),
					  new Inference(Inference::PROGRAM_ANALYSIS),
					  Unit::ASSUMPTION));
  }
  if (min == -1) {
    // generate J > I & c(J) < V & V < c(I) -> (E K)(J > K & K > I & c(K) = V)
    TermList I;
    I.makeVar(0);
    TermList J;
    J.makeVar(1);
    TermList K;
    K.makeVar(2);
    TermList V;
    V.makeVar(3);
    TermList cI(Term::create(fun,1,&I));
    TermList cJ(Term::create(fun,1,&J));
    TermList cK(Term::create(fun,1,&K));
    Formula* JgreaterI = new AtomicFormula(theory->pred2(Theory::INT_GREATER,true,J,I));
    Formula* cJlessV = new AtomicFormula(theory->pred2(Theory::INT_LESS,true,cJ,V));
    Formula* VlessI = new AtomicFormula(theory->pred2(Theory::INT_LESS,true,V,cI));
    FormulaList* left = (new FormulaList(VlessI))->cons(cJlessV)->cons(JgreaterI);
    Formula* lhs = new JunctionFormula(AND,left);
    Formula* JgreaterK = new AtomicFormula(theory->pred2(Theory::INT_GREATER,true,J,K));
    Formula* KgreaterI = new AtomicFormula(theory->pred2(Theory::INT_GREATER,true,K,I));
    Formula* cKequalV = new AtomicFormula(Literal::createEquality(true,cK,V));
    FormulaList* right = (new FormulaList(JgreaterK))->cons(KgreaterI)->cons(cKequalV);
    Formula* rhs = new QuantifiedFormula(EXISTS,
					 new Formula::VarList(2),
					 new JunctionFormula(AND,right));
    _units = _units->cons(new FormulaUnit(new BinaryFormula(IMP,lhs,rhs),
					  new Inference(Inference::PROGRAM_ANALYSIS),
					  Unit::ASSUMPTION));
  }
}

/**
 * Convert a program expression into a Vampire expression and relativize it to
 * the loop counter. This means that every updatable program variable gets an
 * additional argument: variable x0 and each constant variable is translated
 * into itself
 */
Term* LoopAnalyzer::relativize(Expression* expr)
{
  CALL("LoopAnalyzer::relativize");

  switch (expr->kind()) {
  case Expression::CONSTANT_INTEGER:
    {
      int val = static_cast<ConstantIntegerExpression*>(expr)->value();
      Theory* theory = Theory::instance();
      return theory->getRepresentation(val);
    }
  
  case Expression::VARIABLE:
    {
      VariableExpression* vexp = static_cast<VariableExpression*>(expr);
      // we can only work with integer variables
      ASS(vexp->etype()->kind() == Type::INT);
      // if (_updatedVariables.contains(
    }

  case Expression::FUNCTION_APPLICATION:
  case Expression::ARRAY_APPLICATION:
    return 0;

  case Expression::CONSTANT_FUNCTION:
    ASS(false);
  }
}
