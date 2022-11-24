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

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/RapidHelper.hpp"

#include "EqualityToInequality.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

ClauseIterator EqualityToInequality::generateClauses(Clause* premise)
{
  CALL("EqualityToInequality::generateClauses");

  static ClauseStack results;

  if(premise->length() == 1){
    Literal* lit = (*premise)[0];
    if(lit->isEquality()  && lit->polarity() && 
      SortHelper::getEqualityArgumentSort(lit).isIntSort()){

      results.reset();

      TermList lhs = *lit->nthArgument(0);
      TermList rhs = *lit->nthArgument(1);

      auto [t1, num1] = RapidHelper::decompose(lhs);
      auto [t2, num2] = RapidHelper::decompose(rhs);

      int diff = num2 - num1;
      
      // t1 or t2 not being vars is a practical addition
      // from viewing problems
      if(!diff || t1.isVar() || t2.isVar())
        return ClauseIterator::getEmpty();

      // TODO, should we add this? Vampire seems to be able to derive it pretty easily?
      Literal* notEqual = Literal::createEquality(false, t1, t2, AtomicSort::intSort());
      Clause* res1 = new(1) Clause(1, GeneratingInference1(InferenceRule::EQ_TO_INEQ, premise));
      (*res1)[0] = notEqual;    
      results.push(res1);    
    
      Literal* less;
      if(diff < 0){
        // t2 > t1
        less = RapidHelper::number::less(true, t1, t2);
      } else {
        // t2 < t1
        less = RapidHelper::number::less(true, t2, t1);      
      } 

      Clause* res2 = new(1) Clause(1, GeneratingInference1(InferenceRule::EQ_TO_INEQ, premise));
      (*res2)[0] = less;    
      results.push(res2);   

      return pvi(getUniquePersistentIterator(ClauseStack::Iterator(results)));
    }

    /*auto res = RapidHelper::number::isLess(lit);
    if(res.isSome() && lit->polarity()){
      auto lhs = res.unwrap().first;
      auto rhs = res.unwrap().second;

      Literal* notEqual = Literal::createEquality(false, lhs, rhs, AtomicSort::intSort());
      Clause* res1 = new(1) Clause(1, GeneratingInference1(InferenceRule::EQ_TO_INEQ, premise));
      (*res1)[0] = notEqual;    
      results.push(res1);    

      return pvi(getUniquePersistentIterator(ClauseStack::Iterator(results)));        
    }*/

  }
  return ClauseIterator::getEmpty();
}

}
