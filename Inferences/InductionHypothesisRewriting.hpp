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
 * @file FnDefRewriting.hpp
 * Defines class FnDefRewriting.
 */

#ifndef __InductionHypothesisRewriting__
#define __InductionHypothesisRewriting__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "GeneralInduction.hpp"

#include "InferenceEngine.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class InductionHypothesisRewriting
    : public GeneratingInferenceEngine {
public:
  CLASS_NAME(InductionHypothesisRewriting);
  USE_ALLOCATOR(InductionHypothesisRewriting);

  void attach(SaturationAlgorithm* salg) override {
    GeneratingInferenceEngine::attach(salg);
    _splitter=_salg->getSplitter();
    _induction = new GeneralInduction(InferenceRule::IH_REWRITING);
    _induction->attach(_salg);
    _lhsIndex = static_cast<IHLHSIndex *>(
      _salg->getIndexManager()->request(IH_LHS_SUBST_TREE));
    _stIndex = static_cast<DemodulationSubtermIndex *>(
      _salg->getIndexManager()->request(DEMODULATION_SUBTERM_SUBST_TREE));

  }
  void detach() override {
    _salg->getIndexManager()->release(DEMODULATION_SUBTERM_SUBST_TREE);
    _stIndex = nullptr;
    _salg->getIndexManager()->release(IH_LHS_SUBST_TREE);
    _lhsIndex = nullptr;
    _induction->detach();
    _induction = nullptr;
    _splitter = nullptr;
    GeneratingInferenceEngine::detach();
  }
  ClauseIterator generateClauses(Clause *premise) override;

private:  
  static Clause *perform(
      Clause *rwClause, Literal *rwLiteral, TermList rwSide, TermList rwTerm,
      Clause *eqClause, Literal *eqLiteral, TermList eqLHS,
      ResultSubstitutionSP subst, bool eqIsResult);

  struct ForwardResultFn;
  struct RewriteableSubtermsFn;
  struct InstancesFn;
  struct GeneralizationsFn;
  struct BackwardResultFn;

  IHLHSIndex *_lhsIndex;
  DemodulationSubtermIndex* _stIndex;
  GeneralInduction* _induction;
  Splitter* _splitter;
};

}; // namespace Inferences

#endif /* __InductionHypothesisRewriting__ */
