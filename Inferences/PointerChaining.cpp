/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file ArgCong.cpp
 * Implements class ArgCong.
 */

#include <utility>

#include "Saturation/SaturationAlgorithm.hpp"

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/RapidHelper.hpp"

#include "PointerChaining.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

typedef RapidHelper RH; 

void PointerChaining::attach(SaturationAlgorithm* salg)
{
  CALL("PointerChaining::attach");

  GeneratingInferenceEngine::attach(salg);

  _rhsIndex=static_cast<PointerChainRhsIndex*> (
    _salg->getIndexManager()->request(POINTER_CHAIN_RHS_INDEX) );

  _lhsIndex=static_cast<PointerChainLhsIndex*> (
    _salg->getIndexManager()->request(POINTER_CHAIN_LHS_INDEX) );
}

void PointerChaining::detach()
{
  CALL("PointerChaining::detach");
  ASS(_salg);

  _rhsIndex=0;
  _lhsIndex=0;
  _salg->getIndexManager()->release(POINTER_CHAIN_RHS_INDEX);  
  _salg->getIndexManager()->release(POINTER_CHAIN_LHS_INDEX);
  GeneratingInferenceEngine::detach();
}


Clause* PointerChaining::createResult(Clause* queryClause, Literal* queryLit, TermList queryChainOrPointer, TermList queryEnd, TermList queryLen, TermList queryTP,
  bool right, TermQueryResult& tqr)
{
  CALL("PointerChaining::createClause");

  auto isChainOrPointer = [](TermList t){
    return RH::isChain(t) || RH::isPointer(t);
  };

  TermList resTerm = tqr.term;
  Literal* resLit = tqr.literal;
  Clause* resClause = tqr.clause;
  ResultSubstitutionSP subst = tqr.substitution;

  TermList lhs = *resLit->nthArgument(0);
  TermList rhs = *resLit->nthArgument(1);
  TermList resChainOrPointer = isChainOrPointer(lhs) ? lhs : rhs;

  auto queryStructSort = SortHelper::getResultSort(queryChainOrPointer.term());
  auto resStructSort = SortHelper::getResultSort(resChainOrPointer.term());

  if(queryStructSort != resStructSort){
    // different structs. Cannot extend chains
    return 0;
  }
  auto strct = env.signature->getStructOfSort(resStructSort);

  unsigned queryFun = queryChainOrPointer.term()->functor();
  unsigned resFun   = resChainOrPointer.term()->functor();


  auto field = RH::isPointer(resChainOrPointer) ? strct->getFieldByFunctor(resFun) :
                                                  strct->getFieldByChain(resFun);
  if(queryFun != field->chain()  && queryFun != field->functor()){
    // pointers / chains belong to different fields
    // cannot chain together      
    return 0;
  } 

  TermList resultTP = RH::getTP(resChainOrPointer);
  // have to be able to extend the unifier to unify
  // the timepoints as well
  if(!subst->tryGetRobSubstitution()->unify(queryTP, 0, resultTP, 1)){
    return 0;
  }

  TermList resultEnd;
  if(resTerm == lhs){
    resultEnd = RH::getLoc(rhs);
  } else if(resTerm == rhs){
    resultEnd = RH::getLoc(lhs);    
  } else if(resChainOrPointer == lhs){
    resultEnd = rhs;
  } else {
    resultEnd = lhs;
  }

  TermList resultLen = RH::isChain(resChainOrPointer) ? 
    *resChainOrPointer.term()->nthArgument(2) :
    RH::number::one();

  unsigned chainFunc = field->chain();

  TermList queryLenS = subst->apply(queryLen,0);
  TermList resultLenS = subst->apply(resultLen,1);

  TermList tpS = subst->apply(queryTP,0);

  TermList queryEndS = subst->apply(queryEnd,0);
  TermList resultEndS = subst->apply(resultEnd,1);
  TermList newLen = RH::number::add(queryLenS, resultLenS);

  TermList start = right ? resultEndS : queryEndS;
  TermList end   = right ? queryEndS  : resultEndS;

  TermList chain = TermList(Term::create(chainFunc, {start, tpS, newLen}));

  Literal* newLit = Literal::createEquality(true, chain, end, SortHelper::getResultSort(resChainOrPointer.term()));

  unsigned newCLen = queryClause->length() + resClause->length() - 1;

  Clause* res = new(newCLen) Clause(newCLen, GeneratingInference2(InferenceRule::POINTER_CHAINING, queryClause, resClause));
  (*res)[0] = newLit;
  unsigned next = 1;

  for(unsigned i = 0; i < queryClause->length(); i++){
    Literal* lit = (*queryClause)[i];
    if(lit != queryLit){
      Literal* litAfter = subst->apply(lit, 0);
      (*res)[next++] = litAfter;
    }
  }

  for(unsigned i = 0; i < resClause->length(); i++){
    Literal* lit = (*resClause)[i];
    if(lit != resLit){
      Literal* litAfter = subst->apply(lit, 1);
      (*res)[next++] = litAfter;
    }
  }

  return res;
}


ClauseIterator PointerChaining::generateClauses(Clause* premise)
{
  CALL("PointerChaining::generateClauses");
  
  auto isChainOrPointer = [](TermList t){
    return RH::isChain(t) || RH::isPointer(t);
  };

  static bool unit = env.options->pointerChaining() == Options::PointerChaining::UNIT;

  static ClauseStack results;

  if(premise->length() == 1 || !unit){
    for(unsigned i = 0; i < premise->length(); i++){
      Literal* lit = (*premise)[i];
      if(lit->isEquality() && lit->isPositive()){
        TermList lhs = *lit->nthArgument(0);
        TermList rhs = *lit->nthArgument(1);
        if((isChainOrPointer(lhs) && !isChainOrPointer(rhs) ) ||
           (isChainOrPointer(rhs) && !isChainOrPointer(lhs) )){

          results.reset();

          TermList chainOrPointer = isChainOrPointer(lhs) ? lhs : rhs;
          TermList l = RH::getLoc(chainOrPointer);
          TermList r = isChainOrPointer(lhs) ? rhs : lhs;
          TermList tp = RH::getTP(chainOrPointer);
          // a -> b is a chain of length 1
          TermList len = RH::isChain(chainOrPointer) ? 
            *chainOrPointer.term()->nthArgument(2) :
            RH::number::one();

          auto it1 = _lhsIndex->getUnifications(r);
          while(it1.hasNext()){
            TermQueryResult tqr = it1.next();
            Clause* result = createResult(premise, lit, chainOrPointer, l, len, tp, false, tqr);
            if(result){
              results.push(result);
            }
          }

          auto it2 = _rhsIndex->getUnifications(l);
          while(it2.hasNext()){
            TermQueryResult tqr = it2.next();
            Clause* result = createResult(premise, lit, chainOrPointer, r, len, tp, true, tqr);       
            if(result){
              results.push(result);
            }
          }

          return pvi(getUniquePersistentIterator(ClauseStack::Iterator(results)));

        }
      }
    }
  }
  return ClauseIterator::getEmpty();
}

}
