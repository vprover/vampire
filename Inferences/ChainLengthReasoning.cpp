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

#include "ChainLengthReasoning.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

typedef RapidHelper RH; 

void ChainLengthReasoning::attach(SaturationAlgorithm* salg)
{
  CALL("ChainLengthReasoning::attach");

  GeneratingInferenceEngine::attach(salg);

  _index=static_cast<NullTerminatedChainIndex*> (
    _salg->getIndexManager()->request(NULL_TERMINATED_CHAIN_INDEX) );

}

void ChainLengthReasoning::detach()
{
  CALL("ChainLengthReasoning::detach");
  ASS(_salg);

  _index=0;
  _salg->getIndexManager()->release(NULL_TERMINATED_CHAIN_INDEX);  
  GeneratingInferenceEngine::detach();
}


Clause* ChainLengthReasoning::createResult(Clause* queryClause, Literal* queryLit, TermList queryChain, TermList queryLoc, TermList queryTP, TermList queryLen,
  TermQueryResult& tqr)
{
  CALL("ChainLengthReasoning::createClause");

  Literal* resLit = tqr.literal;
  Clause* resClause = tqr.clause;
  ResultSubstitutionSP subst = tqr.substitution;

  if(resClause == queryClause && resLit == queryLit){
    // if we continue in this case, we end with a clause containing a trivial literal
    // len == len
    return 0;
  }

  TermList lhs = *resLit->nthArgument(0);
  TermList rhs = *resLit->nthArgument(1);
  TermList chain = RH::isChain(lhs) ? lhs : rhs;

  if(chain.term()->functor() != queryChain.term()->functor()){
    // different chains
    // cannot make length inferences
    return 0;
  }

  TermList resultTP = RH::getTP(chain);
  // have to be able to extend the unifier to unify
  // the timepoints as well
  if(!subst->tryGetRobSubstitution()->unify(queryTP, 0, resultTP, 1)){
    return 0;
  }

  TermList resultLen = *chain.term()->nthArgument(2);

  TermList queryLenS = subst->apply(queryLen,0);
  TermList resultLenS = subst->apply(resultLen,1);

  if(queryLenS == resultLenS){
    // avoid creating clauses with trivially saitisfiable literals
    return 0;
  }

  Literal* newLit = Literal::createEquality(true, queryLenS, resultLenS, SortHelper::getResultSort(chain.term()));

  unsigned newCLen = queryClause->length() + resClause->length() - 1;

  Clause* res = new(newCLen) Clause(newCLen, GeneratingInference2(InferenceRule::CHAIN_REASONING, queryClause, resClause));
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


ClauseIterator ChainLengthReasoning::generateClauses(Clause* premise)
{
  CALL("ChainLengthReasoning::generateClauses");

  static bool unit = env.options->chainLengthReasoning() == Options::ChainLengthReasoning::UNIT;

  static ClauseStack results;

  if(premise->length() == 1 || !unit){
    for(unsigned i = 0; i < premise->length(); i++){
      Literal* lit = (*premise)[i];
      if(lit->isEquality() && lit->isPositive()){
        TermList lhs = *lit->nthArgument(0);
        TermList rhs = *lit->nthArgument(1);
        if((RH::isChain(lhs) && RH::isNull(rhs) ) ||
           (RH::isChain(rhs) && RH::isNull(lhs) )){

          results.reset();

          TermList chain = RH::isChain(lhs) ? lhs : rhs;
          TermList loc = RH::getLoc(chain);
          TermList tp = RH::getTP(chain);
          TermList len = *chain.term()->nthArgument(2);    

          auto it = _index->getUnifications(loc);
          while(it.hasNext()){
            TermQueryResult tqr = it.next();
            Clause* result = createResult(premise, lit, chain, loc, tp, len, tqr);
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
