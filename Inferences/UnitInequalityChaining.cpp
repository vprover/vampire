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
#include "Kernel/RapidHelper.hpp"

#include "UnitInequalityChaining.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void UnitInequalityChaining::attach(SaturationAlgorithm* salg)
{
  CALL("UnitInequalityChaining::attach");

  GeneratingInferenceEngine::attach(salg);

  _rhsIndex=static_cast<UnitInequalityRhsIndex*> (
    _salg->getIndexManager()->request(UNIT_INEQUALITY_RHS_INDEX) );

  _lhsIndex=static_cast<UnitInequalityLhsIndex*> (
    _salg->getIndexManager()->request(UNIT_INEQUALITY_LHS_INDEX) );
}

void UnitInequalityChaining::detach()
{
  CALL("UnitInequalityChaining::detach");
  ASS(_salg);

  _rhsIndex=0;
  _lhsIndex=0;
  _salg->getIndexManager()->release(UNIT_INEQUALITY_RHS_INDEX);  
  _salg->getIndexManager()->release(UNIT_INEQUALITY_LHS_INDEX);
  GeneratingInferenceEngine::detach();
}


Clause* UnitInequalityChaining::createResult(Literal* queryLit, TermList trm,
  bool right, TermQueryResult& tqr, Clause* premise)
{
  CALL("UnitInequalityChaining::createClause");

  TermList resTerm = tqr.term;
  Literal* resLit = tqr.literal;
  Clause* resClause = tqr.clause;
  ResultSubstitutionSP subst = tqr.substitution;

  TermList resOtherTerm = *resLit->nthArgument(0) == resTerm ?
    *resLit->nthArgument(1): 
    *resLit->nthArgument(0);   

  TermList trmS = subst->apply(trm,0);
  TermList resOtherTermS = subst->apply(resOtherTerm,1);

  // if either literals is positive, result is positive
  // a <= b && b < c ===> a < c
  bool newLitPol = queryLit->polarity() || resLit->polarity();
  if(!newLitPol){
    // invert which term goes on the right
    right = !right;
  }

  Literal* newLit = right ? 
    RapidHelper::number::less(newLitPol, resOtherTermS, trmS) :
    RapidHelper::number::less(newLitPol, trmS, resOtherTermS);

  Clause* res = new(1) Clause(1, GeneratingInference2(InferenceRule::INEQUALITY_CHAINING, premise, resClause));
  (*res)[0] = newLit;   
  return res;
}


ClauseIterator UnitInequalityChaining::generateClauses(Clause* premise)
{
  CALL("UnitInequalityChaining::generateClauses");

  static ClauseStack results;

  if(premise->length() == 1){
    Literal* lit = (*premise)[0];
    auto res = RapidHelper::number::isLess(lit);
    if(res.isSome()){
      auto pair = res.unwrap();
      
      results.reset();

      TermList rhs = lit->polarity() ? pair.second : pair.first;
      TermList lhs = lit->polarity() ? pair.first : pair.second;
 
      auto it1 = _lhsIndex->getUnifications(rhs);
      while(it1.hasNext()){
        TermQueryResult tqr = it1.next();
        Clause* result = createResult(lit, lhs, false, tqr, premise);
        results.push(result);
      }

      auto it2 = _rhsIndex->getUnifications(lhs);
      while(it2.hasNext()){
        TermQueryResult tqr = it2.next();
        Clause* result = createResult(lit, rhs, true, tqr, premise);       
        results.push(result);
      }

      return pvi(getUniquePersistentIterator(ClauseStack::Iterator(results)));
    }
  }
  return ClauseIterator::getEmpty();
}

}
