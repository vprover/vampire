/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __LFP_RULE_HPP__
#define __LFP_RULE_HPP__

#include "InferenceEngine.hpp"

namespace Inferences {

template<class Rule>
class LfpRule
  : public SimplifyingGeneratingInference1
{
  Rule _inner;
public:
  CLASS_NAME(LfpRule);
  USE_ALLOCATOR(LfpRule);
 
  LfpRule(Rule rule);
  LfpRule();
  SimplifyingGeneratingInference1::Result simplify(Clause *cl, bool doCheckOrdering) override;
  void attach(SaturationAlgorithm* alg) override { SimplifyingGeneratingInference1::attach(alg); _inner.attach(alg); }
  void detach() override { SimplifyingGeneratingInference1::detach(); _inner.detach(); }
};


template<class Rule> 
LfpRule<Rule>::LfpRule(Rule rule) : _inner(std::move(rule)) {}

template<class Rule> 
LfpRule<Rule>::LfpRule() : _inner() {}

template<class Rule> 
SimplifyingGeneratingInference1::Result LfpRule<Rule>::simplify(Clause *cl, bool doCheckOrdering) 
{
  CALL("LfpRule::simplify")

  auto splits = cl->splits();

  auto c0 = cl; // the parent of the current clause
  auto _c1 = _inner.simplify(c0, doCheckOrdering);
  auto c1 = _c1.simplified; // the current clause
  auto originalRedundant = _c1.premiseRedundant;

  while (c0 != c1) {
    auto c2 = _inner.simplify(c1, doCheckOrdering); // the new child
    if (c2.simplified != c1) {
      // We need to assign the split set since this would normally 
      // be done by SaturationAlgorithm/Splitter, which we bypass here.
      // WE do this for all clauses but for the final one we will return, 
      // because the final one will be passed back to saturation algorithm and splitter
      if (splits) {
        c1->setSplits(cl->splits());
      }
      originalRedundant = originalRedundant && c2.premiseRedundant;
    }
    c0 = c1;
    c1 = c2.simplified;
  }


  return Result {
    .simplified       = c1,
    .premiseRedundant = originalRedundant,
  };
}

} // namespace Inferences

#endif //__LFP_RULE_HPP__

