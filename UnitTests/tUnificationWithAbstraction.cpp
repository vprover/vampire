/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Forwards.hpp"
#include "Lib/Environment.hpp"

#include "Shell/Options.hpp"

#include "Kernel/Unit.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/RobSubstitution.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Indexing/TermIndex.hpp"

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

// TODO make this test use assertions, instead of printing output

using namespace Kernel;
using namespace Indexing;
using SortType = TermList;

Clause* unit(Literal* lit)
{
  static Inference testInf = Kernel::NonspecificInference0(UnitInputType::ASSUMPTION, InferenceRule::INPUT); 
  Clause * cl = new(1) Clause(1,testInf);
  (* cl)[0] = lit;
  return cl;
}


TermIndexingStructure* getTermIndex()
{
  UWAMismatchHandler* handler = new UWAMismatchHandler();
  return new TermSubstitutionTree(handler); 
}

LiteralIndexingStructure* getLiteralIndex()
{
  UWAMismatchHandler* handler = new UWAMismatchHandler();
  return new LiteralSubstitutionTree(handler); 
}

void reportTermMatches(TermIndexingStructure* index, TermList term, TermList sort)
{
  TermQueryResultIterator it= index->getUnificationsUsingSorts(term,sort,true);
  cout << endl;
  cout << "Unify with " << term.toString() << endl;
  while(it.hasNext()){
    TermQueryResult qr = it.next();
    cout << qr.term.toString() << " matches with substitution: "<< endl;
    // cout << qr.substitution->tryGetRobSubstitution()->toString() << endl;
    cout << "and constraints: "<< endl;
    auto constraints = qr.substitution->getConstraints();
    while(constraints.hasNext()){
      Literal* constraint = constraints.next();
      cout << "> " << constraint->toString() << endl;
    }
  }
  cout << endl;
}

void reportMatches(LiteralIndexingStructure* index, Literal* qlit)
{
  SLQueryResultIterator it= index->getUnifications(qlit,false,true);
  cout << endl;
  cout << "Unify with " << qlit->toString() << endl;
  while(it.hasNext()){
    SLQueryResult qr = it.next();
    cout << qr.clause->toString() << " matches with substitution: "<< endl;
    // cout << qr.substitution->tryGetRobSubstitution()->toString() << endl;
    cout << "and constraints: "<< endl;
    auto constraints = qr.substitution->getConstraints();
    while(constraints.hasNext()){
      Literal* constraint = constraints.next();
      cout << "> " << constraint->toString() << endl;
    }
  }
  cout << endl;
}


TEST_FUN(term_indexing_one_side_interp)
{
  env.options->setUWA(Options::UnificationWithAbstraction::ONE_INTERP); 

  TermIndexingStructure* index = getTermIndex();

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_PRED(p, {Int})

  DECL_CONST(a, Int) 
  DECL_CONST(b, Int) 

  index->insert(num(1) + num(1), p(num(1) + num(1)), unit(p(num(1) + num(1))));
  index->insert(1 + a, p(1 + a), unit(p(a + a)));
  
  reportTermMatches(index,b + 2, Int);

  index->insert(a,p(a),unit(p(a)));

  reportTermMatches(index,b + 2, Int);
  reportTermMatches(index,x,Int);  
}

TEST_FUN(term_indexing_interp_only)
{
  env.options->setUWA(Options::UnificationWithAbstraction::INTERP_ONLY); 

  TermIndexingStructure* index = getTermIndex();

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_PRED(p, {Int})

  DECL_CONST(a, Int) 
  DECL_CONST(b, Int) 

  index->insert(num(1) + num(1), p(num(1) + num(1)), unit(p(num(1) + num(1))));
  index->insert(1 + a, p(1 + a), unit(p(a + a)));

  reportTermMatches(index,b + 2,Int);

  index->insert(a,p(a),unit(p(a)));

  reportTermMatches(index,b + 2,Int);
  reportTermMatches(index,x,Int);  
}

// This test demonstrates the current issue. The constraints produced depend on
TEST_FUN(literal_indexing)
{
  env.options->setUWA(Options::UnificationWithAbstraction::ONE_INTERP); 

  LiteralIndexingStructure* index = getLiteralIndex();

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_PRED(p, {Int})

  DECL_CONST(a, Int) 
  DECL_CONST(b, Int) 

  index->insert(p(num(1) + num(1)), unit(p(num(1) + num(1))));
  index->insert(p(1 + a), unit(p(1 + a)));  


  reportMatches(index,p(b + 2));

  index->insert(p(b + 2),unit(p(b + 2)));

  reportMatches(index,p(b +2)); 
}

static const int NORM_QUERY_BANK=2;
static const int NORM_RESULT_BANK=3;

void reportRobUnify(TermList a, TermList b, RobSubstitution& sub)
{
  cout << endl;
  cout << "Unifying " << a.toString() << " with " << b.toString() << endl;
  //MismatchHandler* hndlr = new testMismatchHandler(&constraints);
  bool result = sub.unify(a,NORM_QUERY_BANK,b,NORM_RESULT_BANK);
  cout << "Result is " << result << endl;
  if(result){
    // cout << "> Substitution is " << endl << sub.toString();
    cout << "> Constraints are:" << endl;
    auto constraints = sub.getConstraints();
    while(constraints.hasNext()){
      Literal* constraint = constraints.next();
      cout << "> " << constraint->toString() << endl;
    }
  }
  cout << endl;
}

TEST_FUN(using_robsub)
{
  env.options->setUWA(Options::UnificationWithAbstraction::ONE_INTERP);

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_FUNC(f, {Int}, Int)
  DECL_FUNC(g, {Int}, Int)  
  DECL_CONST(a, Int) 
  DECL_CONST(b, Int) 

  MismatchHandler* hndlr = new UWAMismatchHandler();
  RobSubstitution sub(hndlr);

  auto t1 = hndlr->transform(f(b + 2));
  auto t2 = hndlr->transform(f(x + 2));
  auto t3 = hndlr->transform(f(a));
  auto t4 = hndlr->transform(g(1 + a));

  reportRobUnify(t1, t2,sub);
  sub.reset();
  reportRobUnify(t2, t3,sub);
  sub.reset();
  reportRobUnify(t3, t4,sub);
}


/*TEST_FUN(complex_case)
{
  env.options->setUWA(Options::UnificationWithAbstraction::ONE_INTERP);

  // The complex case is where we have a variable that needs to be instantiated elsewhere
  // e.g. unifying f(f(g(X),X),f(Y,a)) with f(f(1,2),(3,g(Z)))
 
  unsigned f = function_symbol("f",2,IntegerConstantType::getSort()); 
  unsigned g = function_symbol("g",1,IntegerConstantType::getSort()); 
  TermList query = TermList(Term::create2(f,TermList(Term::create2(f,TermList(Term::create1(g,var(0))),var(0))), 
  					    TermList(Term::create2(f,var(1),TermList(constant("a",IntegerConstantType::getSort()))))));
  TermList node  = TermList(Term::create2(f,TermList(Term::create2(f,number("1"),number("2"))),
  					    TermList(Term::create2(f,number("3"),TermList(Term::create1(g,var(1)))))));

  reportRobUnify(query,node);

  LiteralIndexingStructure* index = new LiteralSubstitutionTree(true); 
  Literal* nlit = pred("p",node);
  index->insert(nlit,unit(nlit));
  Literal* qlit = pred("p",query);
  reportMatches(index,qlit);

}*/
