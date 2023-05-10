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
 * @file RewritingByRule.cpp
 * Implements class RewritingByRule.
 */

#include "RewritingByRule.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

using namespace Kernel;
using namespace Inferences;

Clause* DemodulationByRule::simplify(Clause* c)
{
  CALL("DemodulationByRule::simplify");

  auto cLen = c->length();
  auto& ord = _salg->getOrdering();
  for (unsigned i = 0; i < cLen; i++) {
    auto lit = (*c)[i];
    auto it = c->getRewriteRules();
    while (it.hasNext()) {
      auto kv = it.next();
      if (lit->containsSubterm(kv.first)) {
        if (ord.compare(kv.first,kv.second)!=Ordering::GREATER) {
          continue;
        }
        if (lit->isEquality() && (lit->termArg(0) == kv.first || lit->termArg(1) == kv.first)) {
          // TODO: perform demodulation redundancy check
          auto other = lit->termArg(0) == kv.first ? lit->termArg(1) : lit->termArg(0);
          Ordering::Result tord=ord.compare(kv.second, other);
          if (tord !=Ordering::LESS && tord!=Ordering::LESS_EQ) {
            bool isMax = true;
            for (unsigned j = 0; j < cLen; j++) {
              if (lit == (*c)[j]) {
                continue;
              }
              if (ord.compare(lit, (*c)[j]) == Ordering::LESS) {
                isMax=false;
                break;
              }
            }
            if(isMax) {
              // cout << "rule " << kv.first << "->" << kv.second << ", cl: " << *c << endl;
              continue;
            }
          }
        }

        Clause* res = new(cLen) Clause(cLen,
          SimplifyingInference1(InferenceRule::DEMODULATION_BY_RULE, c));
        for(unsigned j=0;j<cLen;j++) {
          (*res)[j] = EqHelper::replace((*c)[j],kv.first,kv.second);
        }
        auto rwIt = c->getRewriteRules();
        while (rwIt.hasNext()) {
          auto kv = rwIt.next();
          res->addRewriteRule(kv.first,kv.second);
        }
        auto rwBIt = c->getBlockedTerms();
        while (rwBIt.hasNext()) {
          res->addBlockedTerm(rwBIt.next());
        }
        env.statistics->demodulationByRule++;
        return res;
      }
    }
  }
  return c;
}
