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
 * @file NegativeExt.cpp
 * Implements class NegativeExt.
 */

#include <utility>

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Rebalancing.hpp"
#include "Kernel/Rebalancing/Inverters.hpp"
#include "Kernel/SortHelper.hpp"

#include "EquationBalancingForLoopCounters.hpp"

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

using Balancer = Kernel::Rebalancing::Balancer<Kernel::Rebalancing::Inverters::NumberTheoryInverter>;

ClauseIterator EquationBalancingForLoopCounters::generateClauses(Clause* cl)
{
  CALL("EquationBalancingForLoopCounters::generateClauses");    
  
  bool modified = false;
  LiteralStack litStack;

  for(unsigned i = 0; i < cl->size(); i++) {
    Literal* lit = (*cl)[i];
    if (lit->isEquality() && !lit->isNegative()) {

      bool foundBalancing = false;
      for (auto b : Balancer(*lit, false)) {
        /* found a rebalancing: lhs = rhs[lhs, ...] */
        auto lhs = b.lhs();
        auto rhs = b.buildRhs();
        ASS_REP(!lhs.isVar(), lhs);
         
        // can't just use intSort, as the sort may be Nat
        litStack.push(Literal::createEquality(true, lhs, rhs, SortHelper::getResultSort(lhs.term())));
        modified = true;
        foundBalancing = true;
        break;
      }
      if(!foundBalancing){
        litStack.push(lit);
      }
    } else {
      litStack.push(lit);
    }
  }

  if(!modified){
    return ClauseIterator::getEmpty();
  }

  Inference inf = GeneratingInference1(InferenceRule::REBALANCE_FOR_FINAL_LOOP_COUNTS, cl);
  return pvi(getSingletonIterator(Clause::fromStack(litStack, inf)));
}

}
