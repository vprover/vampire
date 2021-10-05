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


#include "Test/UnitTesting.hpp"

// TODO make this test use assertions, instead of printing output

using namespace Kernel;
using namespace Indexing;
using SortType = TermList;

TermList number(vstring n)
{
  return TermList(Term::create(env.signature->addIntegerConstant(n,false),0,0));
}
TermList var(unsigned i)
{
  return TermList(i,false);
}
unsigned function_symbol(vstring name,unsigned arity,SortType srt)
{
  bool added;
  unsigned f = env.signature->addFunction(name,arity,added);
  if(added){
    Signature::Symbol* symbol = env.signature->getFunction(f);
    OperatorType* ot = OperatorType::getFunctionTypeUniformRange(arity,srt,srt);
    symbol->setType(ot); 
  }
  return f; 
}
TermList constant(vstring name,SortType srt)
{
  auto c =  function_symbol(name,0,srt);
  Term* t = Term::create(c,0,0);
  return TermList(t);
}
TermList int_constant(vstring name)
{
  return constant(name,IntegerConstantType::getSort());
}
TermList binary(Interpretation fun, TermList n1, TermList n2)
{
  return TermList(Term::create2(env.signature->getInterpretingSymbol(fun),n1,n2));
}
TermList int_plus(TermList n1, TermList n2)
{
  return binary(Theory::INT_PLUS,n1,n2);
}
Literal* equals(TermList t1, TermList t2)
{
   SortType srt;
   if(!SortHelper::tryGetResultSort(t1,srt)){
     cout << "Don't call equals with two variables" << endl;
     exit(0);
   }
   return Literal::createEquality(true, t1,t2,srt); 
}
Literal* pred(vstring p, TermList t, SortType srt)
{
  bool added;
  unsigned ps = env.signature->addPredicate(p,1,added);
  if(added){
    Signature::Symbol* symbol = env.signature->getPredicate(ps);
    OperatorType* ot = OperatorType::getPredicateTypeUniformRange(1,srt);
    symbol->setType(ot);
  }
  return Literal::create1(ps,true,t);
}
Literal* pred(vstring p, TermList t)
{
  SortType srt;
  if(!SortHelper::tryGetResultSort(t,srt)){
    cout << "Don't call this pred with a variable argument" << endl;
    exit(0);
  }
  return pred(p,t,srt);
}
Clause* unit(Literal* lit)
{
  static Inference testInf = Kernel::NonspecificInference0(UnitInputType::ASSUMPTION, InferenceRule::INPUT); 
  Clause * cl = new(1) Clause(1,testInf);
  (* cl)[0] = lit;
  return cl;
}


LiteralIndexingStructure* getBasicIndex()
{
  // Let's create an index with some data in it
  // We pass true to say that we want to use constraints
  LiteralIndexingStructure * is = new LiteralSubstitutionTree(true); 


  TermList one_plus_one = int_plus(number("1"),number("1"));
  TermList one_plus_a = int_plus(number("1"),int_constant("a"));

  Literal* p1 = pred("p",one_plus_one);
  Literal* p2 = pred("p",one_plus_a);

  is->insert(p1,unit(p1));
  is->insert(p2,unit(p2));

  return is;

}

void reportMatches(LiteralIndexingStructure* index, Literal* qlit)
{
  SLQueryResultIterator it= index->getUnificationsWithConstraints(qlit,false,true);
  cout << endl;
  cout << "Unify with " << qlit->toString() << endl;
  while(it.hasNext()){
    SLQueryResult qr = it.next();
    cout << qr.clause->toString() << " matches with substitution: "<< endl;
    // cout << qr.substitution->tryGetRobSubstitution()->toString() << endl;
    cout << "and constraints: "<< endl;
    auto constraints = qr.constraints;
    for(unsigned i=0;i<constraints->size();i++){
      auto con = (*constraints)[i];
      TermList qT = qr.substitution->applyTo(con.first.first,con.first.second);
      TermList rT = qr.substitution->applyTo(con.second.first,con.second.second);

      cout << "> "<< qT.toString() << "!=" << rT.toString() << "\t\t from " << con.first.first.toString() << "!=" << con.second.first.toString() << endl;
    }
  }
  cout << endl;
}

// This test demonstrates the current issue. The constraints produced depend on
TEST_FUN(current_issue)
{
  env.options->setUWA(Options::UnificationWithAbstraction::ALL); 

  LiteralIndexingStructure* index = getBasicIndex();

  Literal* qlit = pred("p",int_plus(int_constant("b"),number("2")));

  reportMatches(index,qlit);
  // Currently this produces
  //1. p($sum(1,1)) [input] matches with constraints 
  //> $sum(b,2)!=$sum(1,1)
  //2. p($sum(1,a)) [input] matches with constraints 
  //> $sum(b,2)!=$sum(1,a)

  index->insert(qlit,unit(qlit));

  reportMatches(index,qlit);
  // Whereas this produces
  //2. p($sum(1,a)) [input] matches with constraints 
  //> b!=1
  //> 2!=a
  //1. p($sum(1,1)) [input] matches with constraints 
  //> b!=1
  //> 2!=1
  //3. p($sum(b,2)) [input] matches with constraints 
}

static const int NORM_QUERY_BANK=2;
static const int NORM_RESULT_BANK=3;

struct testMismatchHandler : MismatchHandler
{
testMismatchHandler(Stack<UnificationConstraint>* c) : _constraints(c) {}
bool handle(RobSubstitution* subst, TermList query, unsigned index1, TermList node, unsigned index2){
    ASS(index1 == NORM_QUERY_BANK && index2 == NORM_RESULT_BANK);
    static unsigned _var = 0;
    unsigned x = _var++;
    TermList nodeVar = TermList(x,true);
    subst->bindSpecialVar(x,node,index2);
    auto constraint = make_pair(make_pair(query,index1),make_pair(nodeVar,index2));
    _constraints->push(constraint);
    return true;
}
Stack<UnificationConstraint>* _constraints;
};

void reportRobUnify(TermList a, TermList b)
{
  cout << endl;
  cout << "Unifying " << a.toString() << " with " << b.toString() << endl;
  RobSubstitution sub;
  Stack<UnificationConstraint> constraints;
  //MismatchHandler* hndlr = new testMismatchHandler(&constraints);
  MismatchHandler* hndlr = new UWAMismatchHandler(constraints);
  bool result = sub.unify(a,NORM_QUERY_BANK,b,NORM_RESULT_BANK,hndlr);
  cout << "Result is " << result << endl;
  if(result){
    // cout << "> Substitution is " << endl << sub.toString();
    cout << "> Constraints are:" << endl;
    auto rs = ResultSubstitution::fromSubstitution(&sub,NORM_QUERY_BANK,NORM_RESULT_BANK);
    for(unsigned i=0;i<constraints.size();i++){
      auto con = (constraints)[i];
      TermList qT = sub.apply(con.first.first,con.first.second);
      TermList rT = sub.apply(con.second.first,con.second.second);

      cout << "> "<< qT.toString() << "!=" << rT.toString() << "\t\t from " << con.first.first.toString() << "!=" << con.second.first.toString() << endl;
    }
  }
  cout << endl;
}

TEST_FUN(using_robsub)
{
  env.options->setUWA(Options::UnificationWithAbstraction::ALL);

  TermList b_plus_two = int_plus(int_constant("b"),number("2"));
  TermList one_plus_a = int_plus(number("1"),int_constant("a"));
  TermList x_plus_two = int_plus(var(0),number("2"));

  reportRobUnify(b_plus_two,x_plus_two);
  reportRobUnify(b_plus_two,one_plus_a);

}


TEST_FUN(complex_case)
{
  env.options->setUWA(Options::UnificationWithAbstraction::ALL);

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

}
