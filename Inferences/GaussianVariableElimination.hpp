#include "InferenceEngine.hpp"
#include "Lib/Set.hpp"
#include "PolynomialNormalization.hpp"

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
  SimplifyingGeneratingInference1::Result simplify(Clause *cl, bool doCheckOrdering) override;
};


template<class Rule> 
LfpRule<Rule>::LfpRule(Rule rule) : _inner(std::move(rule)) {}

template<class Rule> 
SimplifyingGeneratingInference1::Result LfpRule<Rule>::simplify(Clause *cl, bool doCheckOrdering) 
{
  CALL("LfpRule::simplify")
  // DBG("in:  ", *cl);
  auto cur = cl;
  auto nxt = cl;
  auto redundant = true;

  do {
    cur = nxt;
    auto res = _inner.simplify(cur, doCheckOrdering);
    nxt = res.simplified;
    redundant = redundant && res.premiseRedundant;
  } while (nxt != cur);

  // DBG("out: ", *nxt);
  return Result {
    .simplified       = nxt,
    .premiseRedundant = redundant,
  };
}

} // namespace Inferences
