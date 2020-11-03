#include "InferenceEngine.hpp"
#include "Lib/Set.hpp"
#include "PolynomialNormalization.hpp"
#include "Kernel/Clause.hpp"

#if VDEBUG
#include "Saturation/Splitter.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#endif

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
#if VDEBUG
  SaturationAlgorithm* _sa;
#endif
public:
  CLASS_NAME(LfpRule);
  USE_ALLOCATOR(LfpRule);
 
  LfpRule(Rule rule
#if VDEBUG
  ,SaturationAlgorithm* sa
#endif
);
  LfpRule();
  SimplifyingGeneratingInference1::Result simplify(Clause *cl, bool doCheckOrdering) override;
};


template<class Rule> 
LfpRule<Rule>::LfpRule(Rule rule
#if VDEBUG
    , SaturationAlgorithm* sa
#endif
    ) : _inner(std::move(rule)) 
#if VDEBUG
        ,_sa(sa)
#endif
{}

template<class Rule> 
LfpRule<Rule>::LfpRule() : _inner() {}

template<class Rule> 
SimplifyingGeneratingInference1::Result LfpRule<Rule>::simplify(Clause *cl, bool doCheckOrdering) 
{
  CALL("LfpRule::simplify")
  // DBG("in:  ", *cl);
  auto c0 = cl;
  ASS(_sa->getSplitter()->allSplitLevelsActive(cl->splits()));
  auto c1 = _inner.simplify(c0, doCheckOrdering).simplified;

  while (c0 != c1) {
    // we need to assign the split set since this would normally 
    // be done by SaturationAlgorithm/Splitter, which we bypass here

    if (c0->splits()) {
      c1->setSplits(c0->splits());
      DBG("assigned splits: ", *c1)
    }

    ASS(_sa->getSplitter()->allSplitLevelsActive(c0->splits()));
    c0 = c1;
    c1 = _inner.simplify(c0, doCheckOrdering).simplified;
    ASS(_sa->getSplitter()->allSplitLevelsActive(c0->splits()));

  }

  DBG("lfp result: ", *c1, " (splits not yet assigned)");
  // DBG("out: ", *c1);
  return Result {
    .simplified       = c1,
    .premiseRedundant = false,
  };
}

} // namespace Inferences
