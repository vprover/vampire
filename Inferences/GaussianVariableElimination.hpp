#include "InferenceEngine.hpp"
#include "Lib/Set.hpp"
#include "PolynomialNormalization.hpp"
#include "Kernel/Clause.hpp"

namespace Inferences {

class GaussianVariableElimination 
  : public SimplifyingGeneratingInference1 
{
public:
  CLASS_NAME(GaussianVariableElimination);
  USE_ALLOCATOR(GaussianVariableElimination);

  SimplifyingGeneratingInference1::Result simplify(Clause *cl, bool doCheckOrdering) override;

private:
  SimplifyingGeneratingInference1::Result rewrite(Clause &cl, TermList find, TermList replace,
                  unsigned skipLiteral, bool doOrderingCheck) const;
};


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
};


template<class Rule> 
LfpRule<Rule>::LfpRule(Rule rule) : _inner(std::move(rule)) {}

template<class Rule> 
LfpRule<Rule>::LfpRule() : _inner() {}

template<class Rule> 
SimplifyingGeneratingInference1::Result LfpRule<Rule>::simplify(Clause *cl, bool doCheckOrdering) 
{
  CALL("LfpRule::simplify")
  // DBG("in:  ", *cl);
  auto last = cl;
  auto nxt = cl;
  auto redundant = true;
  auto last_redundant = true;

  do {
    // we need to assign the split set since this would normally 
    // be done by SaturationAlgorithm/Splitter, which we bypass here
    if (last != nxt && last->splits() != nullptr) {
      nxt->setSplits(last->splits());
    }

    last = nxt;
    redundant = redundant && last_redundant;

    auto res = _inner.simplify(last, doCheckOrdering);

    last_redundant = res.premiseRedundant;
    nxt = res.simplified;
  } while (nxt != last);

  // DBG("out: ", *nxt);
  return Result {
    .simplified       = nxt,
    .premiseRedundant = redundant,
  };
}

} // namespace Inferences
