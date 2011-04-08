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
#include "Lib/DHSet.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Unit.hpp"
#include "Api/FormulaBuilder.hpp"
#include "Api/Problem.hpp"


#include "Variable.hpp"
#include "Expression.hpp"
#include "Statement.hpp"
#include "Path.hpp"
#include "LoopAnalyzer.hpp"

#include "Shell/Options.hpp"
#include "Shell/Property.hpp"
#include "Shell/Preprocess.hpp"

using namespace Kernel;
using namespace Program;
using namespace Shell;

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
  cout << "Analyzing variables...\n";
  cout << "---------------------\n";
  analyzeVariables();
  cout << "\nCollecting paths...\n";
  cout << "---------------------\n";
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
  cout << "\nGenerate Let...In expressions for array updates and next states...\n";
  cout << "---------------------\n";
  generateLetExpressions();
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
  Stack<Path*> lets;
  // statements corresponding to this path, normally then-parts of IfThenElse
  Stack<Statement*> statements;
  Path* path = Path::empty();
  cout << "Paths wrt the loop condition: " << _loop->condition()->toString() << "\n";
  Statement* stat = _loop->body();
  for (;;) {
    switch (stat->kind()) {
    case Statement::ASSIGNMENT:
      { path = path->add(stat);
        stat = stat->nextStatement();
      }
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
    } //end of switch
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
 * Translate program expressions into Vampire terms (termlists)
*/

TermList LoopAnalyzer::expressionToTerm(Expression* exp)
{
  CALL("LoopAnalyzer::generateLetExpressions");
  switch (exp->kind()) {
  case Expression::CONSTANT_INTEGER:
   {
    int val = static_cast<ConstantIntegerExpression*>(exp)->value();
    Theory* theory = Theory::instance();
    TermList var(theory->getRepresentation(val)); 
    // x01(theory->fun1(Theory::SUCCESSOR,x0));
    return var;
   }
  break;
  case Expression::VARIABLE:
    {
      Variable* expVar=  static_cast<VariableExpression*>(exp)->variable();
      string expName=expVar->name() ;
      TermList var(Term::createConstant(expName));
      cout << "expression "<< exp->toString()<< " over variable "<<expName <<" translated to Vampire term "<< var<<"\n";
      return var;
    }
   break;
   case Expression::ARRAY_APPLICATION:
     {
       //create term for array variable
       Expression*  expArray=  static_cast<ArrayApplicationExpression*>(exp)->array();
       string varName=expArray->toString();
       unsigned arrayFct=env.signature->addFunction(varName,1);
       //create term represenation for array arguments
       Expression*  expArrayArguments=  static_cast<ArrayApplicationExpression*>(exp)->argument();
       TermList varArg= expressionToTerm(expArrayArguments);
       //create term for array application
       TermList varArray=TermList(Term::create1(arrayFct, varArg));
       return varArray;
     }
     break;
  //case Expression::CONSTANT_FUNCTION:
     //{}
     //break;
  case Expression::FUNCTION_APPLICATION:
    {
      //cout<<"function application in rhs of Vampire term\n";
      FunctionApplicationExpression* app = static_cast<FunctionApplicationExpression*>(exp);
      //switch on app->function did not work (error on non-integer value in switch), so used nested IF
      if ( app->function() == ConstantFunctionExpression::integerPlus() )
	{
	   Expression* e1 = app->getArgument(0);
	   Expression* e2 = app->getArgument(1);
	   TermList e1Term= expressionToTerm(e1); //make recursive call on function arguments
	   TermList e2Term=expressionToTerm(e2);
	   Theory* theory = Theory::instance();
	   TermList fctTerm(theory->fun2(Theory::PLUS,e1Term,e2Term));
	   return fctTerm;
	}
      else 
	{
	  if ( app->function() == ConstantFunctionExpression::integerMinus() )
	    {
	      Expression* e1 = app->getArgument(0);
	      Expression* e2 = app->getArgument(1);
	      TermList e1Term= expressionToTerm(e1); //make recursive call on function arguments
	      TermList e2Term=expressionToTerm(e2);	   
 	      Theory* theory = Theory::instance();
	      TermList fctTerm(theory->fun2(Theory::MINUS,e1Term,e2Term)); 
	      return fctTerm;
	    }
	  else 
	    {
	       if ( app->function() == ConstantFunctionExpression::integerMult() )
		 {
		   Expression* e1 = app->getArgument(0);
		   Expression* e2 = app->getArgument(1);
		   TermList e1Term= expressionToTerm(e1); //make recursive call on function arguments
		   TermList e2Term=expressionToTerm(e2);		
		   Theory* theory = Theory::instance();
		   TermList fctTerm(theory->fun2(Theory::MULTIPLY,e1Term,e2Term));
		   return fctTerm;
		 }
	       else
		 {
		   if ( app->function() == ConstantFunctionExpression::integerNegation() )
		     {
		        Expression* e1 = app->getArgument(0);
			TermList e1Term= expressionToTerm(e1); //make recursive call on function arguments
			Theory* theory = Theory::instance();
			TermList fctTerm(theory->fun1(Theory::UNARY_MINUS,e1Term));
			return fctTerm;
		     }
		   else //undefined/not treated theory function. Extend it to later for uninterpreted fct. 
		     {
		       //rhs is an uninterpreted function f(e1), 
		       //create term for uninterpreted function
		       Expression*  uiFct=  app->function();
		       string uiFctName=uiFct->toString();
		       unsigned uiFctNameTerm=env.signature->addFunction(uiFctName,1);
		       //create term representation for arguments e1
		       Expression* e1 = app->getArgument(0);
		       TermList e1Term= expressionToTerm(e1); //make recursive call on function arguments
		       //create term representation of f(e1)
		       TermList fctTerm=TermList(Term::create1(uiFctNameTerm,e1Term));
		       return fctTerm;
		       //string testName="toDo";
		       // TermList fctTerm(Term::createConstant(testName)); 
		       //return fctTerm;
		     }
		 }
	    }
	}
    }
    break;

}
}


/** 
 * Generate let expressions
*/


void LoopAnalyzer::generateLetExpressions()
{
  CALL("LoopAnalyzer::generateLetExpressions");
  unsigned length = _paths.length();
  //cout<<"nr. of paths: "<<length<<" \n";
  if (length == 0) {
    return;
  }
   int pathNumber = 0;
   Stack<Path*>::Iterator pit(_paths);
   while (pit.hasNext()) {
      int inc = 0;
      Path* path = pit.next();
      Path::Iterator sit(path);
      while (sit.hasNext()) {
	Statement* stat = sit.next();
        if (!sit.hasNext()) //last statement of the path, translate term into let
	  {cout<<"last statement of the path"<<"\n";}
        else
	  {
	   switch (stat->kind()) {
	    case Statement::ASSIGNMENT:
	      {
		// cout << "ASSG \n"; 
	      Expression* lhs = static_cast<Assignment*>(stat)->lhs();
	      Expression* rhs = static_cast<Assignment*>(stat)->rhs();
	      //create term representation of lhs and rhs
	      TermList lhsTerm=expressionToTerm(lhs);
	      TermList rhsTerm=expressionToTerm(rhs);
	      cout << "expression conversion for lhs "<< lhs->toString()<<" into Vampire term: "<<lhsTerm<<"\n";
	      cout << "expression conversion for rhs "<< rhs->toString()<<" into Vampire term: "<<rhsTerm<<"\n";
	      if (lhs->kind() == Expression::VARIABLE) 
	      {
		Variable* lhsVar=  static_cast<VariableExpression*>(lhs)->variable();
		string varName=lhsVar->name() ;
		//cout << varName <<" variable \n";
		TermList var(Term::createConstant(varName));
		unsigned varFun = env.signature->addFunction(varName,1);
		// term x0
		TermList x0;
		x0.makeVar(0);
		// term x0+1 for next iteration
		Theory* theory = Theory::instance();
		TermList x01(theory->fun1(Theory::SUCCESSOR,x0));
		// term c(x0)
		TermList varX0(Term::create(varFun,1,&x0));
		TermList varX01(Term::create(varFun,1,&x01));
		TermList assLetTermInner=TermList(Term::createTermLet(lhsTerm, rhsTerm, var)); 
		TermList assLetTerm=TermList(Term::createTermLet(var, varX0, assLetTermInner));  //term let  a=a(X) in a term
		cout << assLetTerm<<" .... starting let assignemnt \n";
		Formula* assLetFormula=new AtomicFormula(Literal::createEquality(true, varX01, assLetTerm));
		cout << assLetFormula->toString()<<" .... creating let formula \n";
	       }
	      if  (lhs->kind() == Expression::ARRAY_APPLICATION)
		{ 
		  Expression*  lhsArray=  static_cast<ArrayApplicationExpression*>(lhs)->array();
		  Expression*  lhsArrayArguments=  static_cast<ArrayApplicationExpression*>(lhs)->argument();
		  cout <<  lhsArray->toString() << " array update application with argument(s): "<< lhsArrayArguments->toString()<<"\n";
		}
              cout << "updated with expression: "<<rhs->toString() <<"\n";
	      }
	      break;
	    case Statement::BLOCK:
	                  break;
  	    case Statement::ITE:
	                  break;
	   }
	  }
      }
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
    //make case distinction between loops with IFs, and no IFs.
    //loops with IFs have at least 2 inner paths, thus length>=2, and hence length-2>=0. Then for-loop starting from length-2 makes sense.
    //loops with no IFs have only one path (the body), thus length=1, and hence length-2<0 makes no sense to start for-loop from. For such cases, for-loop starts from 0.
    for (int i = length>1 ? length-2:0;i >= 0;i--) {
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
 * @param gcd greatest common divisor of all increments of the counter over all paths
 */
void LoopAnalyzer::generateCounterAxiom(const string& name,int min,int max,int gcd)
{
  // value of the counter at position 0
  TermList c(Term::createConstant(name + Int::toString(0)));
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
    Formula* VlesscI = new AtomicFormula(theory->pred2(Theory::INT_LESS,true,V,cI));
    FormulaList* left = (new FormulaList(VlesscI))->cons(cJlessV)->cons(JgreaterI);
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
