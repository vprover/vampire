
/*
 * File tUnificationWithAbstraction.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
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
#include "Kernel/Sorts.hpp"
#include "Kernel/SortHelper.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Indexing/LiteralIndex.hpp"


#include "Test/UnitTesting.hpp"


#define UNIT_ID uwa 
UT_CREATE;

using namespace Kernel;
using namespace Indexing;

TermList number(vstring n)
{
  return TermList(Term::create(env.signature->addIntegerConstant(n,false),0,0));
}
TermList var(unsigned i)
{
  return TermList(i,false);
}
TermList constant(vstring name,unsigned srt)
{
  bool added;
  unsigned c = env.signature->addFunction(name,0,added);
  if(added){
    Signature::Symbol* symbol = env.signature->getFunction(c);
    OperatorType* ot = OperatorType::getConstantsType(srt); 
    symbol->setType(ot); 
  }
  Term* t = Term::create(c,0,0); 
  return TermList(t);
}
TermList int_constant(vstring name)
{
  return constant(name,Sorts::SRT_INTEGER);
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
   unsigned srt;
   if(!SortHelper::tryGetResultSort(t1,srt)){
     cout << "Don't call equals with two variables" << endl;
     exit(0);
   }
   return Literal::createEquality(true, t1,t2,srt); 
}
Literal* pred(vstring p, TermList t, unsigned srt)
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
  unsigned srt;
  if(!SortHelper::tryGetResultSort(t,srt)){
    cout << "Don't call this pred with a variable argument" << endl;
    exit(0);
  }
  return pred(p,t,srt);
}
Clause* unit(Literal* lit)
{
  Clause * cl = new(1) Clause(1,Unit::AXIOM,new Inference(Inference::INPUT));
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


TEST_FUN(index)
{
  env.options->setUWA(Options::UnificationWithAbstraction::ALL); 

  LiteralIndexingStructure* index = getBasicIndex();

  //Literal* qlit = pred("p",var(0),Sorts::SRT_INTEGER);
  Literal* qlit = pred("p",int_plus(int_constant("b"),number("2")));
  SLQueryResultIterator it= index->getUnificationsWithConstraints(qlit,false,true);
  cout << endl;
  while(it.hasNext()){
    SLQueryResult qr = it.next();
    cout << qr.clause->toString() << endl;
    auto constraints;
  }
  cout << endl;

}
