/*
 * File Induction 
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
/**
 * @file Induction.cpp
 * Implements class Induction.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Set.hpp"
#include "Lib/Array.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Theory.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Kernel/Signature.hpp"

#include "Shell/Skolem.hpp"

#include "IntermediateValue.hpp"
#include "Kernel/RapidHelper.hpp"

namespace Inferences
{
using namespace Kernel;
using namespace Lib; 

void IntermediateValue::attach(SaturationAlgorithm* salg)
{
  CALL("Superposition::attach");

  GeneratingInferenceEngine::attach(salg);
  _leftLimitIndex=static_cast<IntermediateValueLimitClauseIndex*> (
    _salg->getIndexManager()->request(INTERMEDIATE_VALUE) );
}

void IntermediateValue::detach()
{
  CALL("Superposition::detach");

  _leftLimitIndex=0;
  _salg->getIndexManager()->release(INTERMEDIATE_VALUE);
  GeneratingInferenceEngine::detach();
}

struct IntermediateValue::ValidRightHandSide
{
  ValidRightHandSide(TermList leftLimit) : rhs(leftLimit) {}
  
  bool operator()(SLQueryResult res)
  {
    CALL("IntermediateValue::ValidRightHandSideFn()");

    TermList tm = *res.literal->nthArgument(1);
    ASS(tm.isTerm());

    if(env.signature->getFunction(tm.term()->functor())->integerConstant()){
      return true;
    }

    return (tm == rhs);
  }

private:
  TermList rhs;
};

struct IntermediateValue::RightLimitExists
{
  RightLimitExists(TermList rightLimit,  LimitClauseContainer* limitClauses) 
  : _rightLimit(rightLimit), _limitClauses(limitClauses) {}
  
  pair<Clause*, SLQueryResult> operator()(SLQueryResult res)
  {
    TermList tm = *res.literal->nthArgument(0);
    Theory::Interpretation interp = Theory::INT_LESS;
    unsigned fun = env.signature->getInterpretingSymbol(interp);
    Literal* lit = Literal::create2(fun, true, tm, _rightLimit);
    return  make_pair(_limitClauses->getClause(lit), res);
  }

private:
  TermList _rightLimit;
  LimitClauseContainer* _limitClauses;
};


struct IntermediateValue::NotZero
{
  NotZero() {}
  
  bool operator()(pair<Clause*, SLQueryResult> p)
  {
    CALL("IntermediateValue:NotZero");

    return p.first != 0;
  }

};

struct IntermediateValue::ResultFn
{
  ResultFn(IntermediateValue& parent, TermList leftLimit, TermList lastLoopCount, 
    Clause* premise, unsigned f1, unsigned f2) : 
  _parent(parent), _leftLimit(leftLimit), _lastLoopCount(lastLoopCount), 
    _premise(premise), _f1(f1), _f2(f2) {}
  
  VirtualIterator<Clause*> operator()(pair<Clause*, SLQueryResult> p)
  {
    TermList lhs = *p.second.literal->nthArgument(0);
    TermList rhs = *p.second.literal->nthArgument(1);
    return _parent.produceConsequences(lhs, rhs, _leftLimit, 
      _lastLoopCount, _premise, p.first, p.second.clause, _f1, _f2);
  }

private:
  IntermediateValue& _parent; 
  TermList _leftLimit;
  TermList _lastLoopCount;
  Clause* _premise;
  unsigned _f1;
  unsigned _f2;
};

ClauseIterator IntermediateValue::generateClauses(Clause* premise)
{
  CALL("IntermediateValue::generateClauses");

  LimitClauseContainer* limitClauses = _salg->getLimitClauseContainer();

  if(premise->length() != 1){
    return ClauseIterator::getEmpty();
  }

  Literal* lit = (*premise)[0];

  if(RapidHelper::isRightLimitLiteral(lit)){
    limitClauses->add(premise);
    //todo change this
    return ClauseIterator::getEmpty();
  }

  unsigned f1, f2;
  if(!RapidHelper::isDensityLiteral(lit, f1, f2)){
    return ClauseIterator::getEmpty();
  }

  TermList rightLimit, leftLimit, nlTerm;

  auto natTA = env.signature->getNat();
  //TODO update to the non-nat case
  if(natTA){
    TermList zeroTerm = natTA->createZero();

    vstring timePointName = env.signature->getFunction(f2)->name();
    unsigned f3 = env.signature->getFunctionNumber("n" + timePointName, 0);
    nlTerm = TermList(Term::createConstant(f3));

    Term* startTimePoint = Term::create1(f2, zeroTerm);
    Term* endTimePoint = Term::create1(f2, nlTerm);

    leftLimit = TermList(Term::create1(f1, TermList(startTimePoint)));
    rightLimit = TermList(Term::create1(f1, TermList(endTimePoint)));
  }
 
  auto it1 = _leftLimitIndex->getAll();
  auto it2 = getFilteredIterator(it1, ValidRightHandSide(leftLimit));
  auto it3 = getMappingIterator(it2, RightLimitExists(rightLimit, limitClauses));
  auto it4 = getFilteredIterator(it3, NotZero());
  auto it5 = getMapAndFlattenIterator(it4, ResultFn(*this, leftLimit, nlTerm, premise, f1, f2));

  return pvi( it5 );

}


ClauseIterator IntermediateValue::produceConsequences(TermList lhs, TermList rhs, 
  TermList leftLimit, TermList nlTerm, Clause* prem1, Clause* prem2, Clause* prem3, unsigned f1, unsigned f2)
{
  CALL("IntermediateValue::produceConsequences");

  if(rhs.isVar()){
    return ClauseIterator::getEmpty();
  }

  auto natTA = env.signature->getNat();
  ASS(natTA);
  TermList rightLimit = 
  TermList(Term::create1(f1, TermList(Term::create1(f2, natTA->createZero()))));

  Literal* cond = 0;
  unsigned l = 1;
  if(env.signature->getFunction(rhs.term()->functor())->integerConstant()){
    cond = Literal::createEquality(false, rhs, rightLimit, AtomicSort::intSort());
    l = 2;
  } else if(rhs != rightLimit){
    return ClauseIterator::getEmpty();
  }

  static ClauseStack results;

  TermList natSort = natTA->termAlgebra()->sort();
  unsigned ltNat = natTA->getLessPredicate();

  unsigned sk = Shell::Skolem::addSkolemFunction(0, 0, 0, natSort);
  TermList skTm = TermList(Term::createConstant(sk));

  Literal* lit1 = Literal::create2(ltNat, true, skTm, nlTerm);

  UnitList* premises1 = UnitList::empty();
  UnitList::push(prem1, premises1);
  UnitList::push(prem2, premises1);
  UnitList::push(prem3, premises1);  
  Clause* conc1 = new(l) Clause(l,GeneratingInferenceMany(InferenceRule::INTERMEDIATE_VALUE, premises1));
      
  (*conc1)[0] = lit1;
  if(cond){ (*conc1)[1] = cond; }  
  results.push(conc1);

  TermList tl = TermList(Term::create1(f1, TermList(Term::create1(f2, skTm)))); 
  Literal* lit2 = Literal::createEquality(true, lhs, tl, AtomicSort::boolSort());

  UnitList* premises2 = UnitList::empty();
  UnitList::push(prem1, premises2);
  UnitList::push(prem2, premises2);
  UnitList::push(prem3, premises2);  
  Clause* conc2 = new(l) Clause(l,GeneratingInferenceMany(InferenceRule::INTERMEDIATE_VALUE, premises2));
      
  (*conc2)[0] = lit2;
  if(cond){ (*conc2)[1] = cond; }
  results.push(conc2);

  TermList one(theory->representConstant(IntegerConstantType(1)));
  TermList lhsPlusOne = 
  TermList(Term::create2(env.signature->getInterpretingSymbol(Theory::INT_PLUS),lhs,one));
  TermList skSucc = natTA->createSucc(skTm);
  tl = TermList(Term::create1(f1, TermList(Term::create1(f2, skSucc))));

  Literal* lit3 = Literal::createEquality(true, lhsPlusOne, tl, AtomicSort::boolSort());
  UnitList* premises3 = UnitList::empty();
  UnitList::push(prem1, premises3);
  UnitList::push(prem2, premises3);
  UnitList::push(prem3, premises3);  
  Clause* conc3 = new(l) Clause(l,GeneratingInferenceMany(InferenceRule::INTERMEDIATE_VALUE, premises3));

  (*conc3)[0] = lit3;
  if(cond){ (*conc3)[1] = cond; }    
  results.push(conc3);

  //cout << "CONC1 " + conc1->toString() << endl;
  //cout << "CONC2 " + conc2->toString() << endl;
  //cout << "CONC3 " + conc3->toString() << endl;
 
  return pvi(getUniquePersistentIterator(ClauseStack::Iterator(results)));

}

}
