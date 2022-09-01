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

Clause* unit(Literal* lit)
{
  return clause({ lit });
}

TermIndexingStructure* getTermIndex(unique_ptr<AtomicMismatchHandler> handler)
{
  auto cmh = new MismatchHandler();
  cmh->addHandler(std::move(handler));
  return new TermSubstitutionTree(cmh); 
}

TermIndexingStructure* getTermIndex(Shell::Options::UnificationWithAbstraction uwa)
{ return getTermIndex(make_unique<UWAMismatchHandler>(uwa)); }

LiteralIndexingStructure* getLiteralIndex(Shell::Options::UnificationWithAbstraction uwa)
{
  auto cmh = new MismatchHandler();
  cmh->addHandler(make_unique<UWAMismatchHandler>(uwa));
  return new LiteralSubstitutionTree(cmh); 
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
    qr.substitution->numberOfConstraints();
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
    qr.substitution->numberOfConstraints();
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
  TermIndexingStructure* index = getTermIndex(Options::UnificationWithAbstraction::ONE_INTERP);

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_PRED(p, {Int})
  DECL_FUNC(f, {Int}, Int)
  DECL_CONST(a, Int) 
  DECL_CONST(b, Int) 

  index->insert(num(1) + num(1), p(num(1) + num(1)), unit(p(num(1) + num(1))));
  index->insert(1 + a, p(1 + a), unit(p(a + a)));
  
  reportTermMatches(index,b + 2, Int);

  index->insert(a,p(a),unit(p(a)));

  reportTermMatches(index,b + 2, Int);
  reportTermMatches(index,x,Int);  

  index->insert(f(x),p(f(x)),unit(p(f(x))));

  reportTermMatches(index, f(a), Int);
  reportTermMatches(index, a + 3 ,Int); 
}

TEST_FUN(term_indexing_poly)
{
  TermIndexingStructure* index = getTermIndex(Options::UnificationWithAbstraction::ONE_INTERP);

  DECL_DEFAULT_VARS
  DECL_DEFAULT_SORT_VARS  
  NUMBER_SUGAR(Int)
  DECL_PRED(p, {Int})
  DECL_CONST(a, Int) 
  DECL_POLY_CONST(h, 1, alpha)

  index->insert(1 + a, p(1 + a), unit(p(a + a)));
  index->insert(h(Int), p(h(Int)), unit(p(h(Int))));
  
  reportTermMatches(index,h(alpha), alpha);
}

TEST_FUN(term_indexing_interp_only)
{
  TermIndexingStructure* index = getTermIndex(Options::UnificationWithAbstraction::INTERP_ONLY);

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

TEST_FUN(literal_indexing)
{
  LiteralIndexingStructure* index = getLiteralIndex(Options::UnificationWithAbstraction::ONE_INTERP);

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

TEST_FUN(higher_order)
{
  TermIndexingStructure* index = getTermIndex(make_unique<HOMismatchHandler>());

  DECL_DEFAULT_VARS
  DECL_DEFAULT_SORT_VARS  
  NUMBER_SUGAR(Int)
  DECL_SORT(srt) 
  DECL_ARROW_SORT(xSrt, {srt, srt}) 
  DECL_ARROW_SORT(fSrt, {xSrt, srt}) 
  DECL_ARROW_SORT(gSrt, {srt, xSrt})   
  DECL_HOL_VAR(x0, 0, xSrt)
  DECL_CONST(a, xSrt)
  DECL_CONST(b, xSrt)
  DECL_CONST(c, srt)  
  DECL_CONST(f, fSrt)
  DECL_CONST(g, gSrt)
  DECL_POLY_CONST(h, 1, alpha)

  index->insert(ap(f,a), 0, 0);

  reportTermMatches(index,ap(f,b),srt);

  index->insert(ap(g,c), 0, 0);
  index->insert(g, 0, 0);

  reportTermMatches(index,x0,xSrt);

  index->insert(h(alpha), 0, 0);

  reportTermMatches(index,h(beta),beta);
  reportTermMatches(index,h(srt),srt);
}

TEST_FUN(higher_order2)
{
  TermIndexingStructure* index = getTermIndex(make_unique<HOMismatchHandler>());

  DECL_DEFAULT_VARS
  DECL_DEFAULT_SORT_VARS  
  NUMBER_SUGAR(Int)
  DECL_SORT(srt) 
  DECL_ARROW_SORT(xSrt, {srt, srt}) 
  DECL_ARROW_SORT(fSrt, {xSrt, xSrt, srt}) 
  DECL_CONST(a, xSrt)
  DECL_CONST(b, xSrt)
  DECL_CONST(f, fSrt)

  index->insert(ap(ap(f,a),b), 0, 0);

  reportTermMatches(index,ap(ap(f,b),a),srt);
}

static const int NORM_QUERY_BANK=2;
static const int NORM_RESULT_BANK=3;

void reportRobUnify(TermList a, TermList b, RobSubstitution& sub)
{
  cout << endl;
  cout << "Unifying " << a.toString() << " with " << b.toString() << endl;

  bool result = sub.unify(a,NORM_QUERY_BANK,b,NORM_RESULT_BANK);
  cout << "Result is " << result << endl;
  if(result){
    // cout << "> Substitution is " << endl << sub.toString();
    cout << "> Constraints are:" << endl;
    sub.numberOfConstraints();
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
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_FUNC(f, {Int}, Int)
  DECL_FUNC(g, {Int}, Int)  
  DECL_CONST(a, Int) 
  DECL_CONST(b, Int) 

  auto cmh = new MismatchHandler();
  cmh->addHandler(make_unique<UWAMismatchHandler>(Options::UnificationWithAbstraction::ONE_INTERP));  
  RobSubstitution sub(cmh);

  auto t1 = f(b + 2);
  auto t2 = f(x + 2);
  auto t3 = f(a);
  auto t4 = g(1 + a);

  reportRobUnify(t1, t2,sub);
  sub.reset();
  reportRobUnify(t2, t3,sub);
  sub.reset();
  reportRobUnify(t3, t4,sub);
}
