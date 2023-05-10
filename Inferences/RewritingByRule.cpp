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
  for (unsigned i = 0; i < cLen; i++) {
    auto lit = (*c)[i];
    auto it = c->getRewriteRules();
    while (it.hasNext()) {
      auto kv = it.next();
      if (lit->containsSubterm(kv.first)) {
        if (_salg->getOrdering().compare(kv.first,kv.second)!=Ordering::GREATER) {
          continue;
        }
        if (lit->isEquality() && (lit->termArg(0) == kv.first || lit->termArg(1) == kv.first)) {
          // TODO: perform demodulation redundancy check
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
