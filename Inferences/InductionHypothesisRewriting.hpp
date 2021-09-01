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
 * @file InductionHypothesisRewriting.hpp
 * Defines class InductionHypothesisRewriting.
 */

#ifndef __InductionHypothesisRewriting__
#define __InductionHypothesisRewriting__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

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

  InductionHypothesisRewriting(GeneratingInferenceEngine* induction)
    : _lhsIndex(0), _stIndex(0), _induction(induction), _splitter(0),
      _dupLitRemoval(new DuplicateLiteralRemovalISE()) {}

  void attach(SaturationAlgorithm* salg) override {
    GeneratingInferenceEngine::attach(salg);
    _splitter=_salg->getSplitter();
    _dupLitRemoval->attach(_salg);
    _lhsIndex = static_cast<InductionEqualityLHSIndex *>(
      _salg->getIndexManager()->request(INDUCTION_EQUALITY_LHS_SUBST_TREE));
    _stIndex = static_cast<InductionInequalitySubtermIndex *>(
      _salg->getIndexManager()->request(INDUCTION_INEQUALITY_SUBTERM_SUBST_TREE));
  }
  void detach() override {
    _salg->getIndexManager()->release(INDUCTION_INEQUALITY_SUBTERM_SUBST_TREE);
    _stIndex = nullptr;
    _salg->getIndexManager()->release(INDUCTION_EQUALITY_LHS_SUBST_TREE);
    _lhsIndex = nullptr;
    _dupLitRemoval->detach();
    _induction = nullptr;
    _splitter = nullptr;
    GeneratingInferenceEngine::detach();
  }
  ClauseIterator generateClauses(Clause *premise) override;

  ClauseIterator perform(const vset<unsigned>& sig,
      Clause *rwClause, Literal *rwLiteral, TermList rwSide, TermList rwTerm,
      Clause *eqClause, Literal *eqLiteral, TermList eqLHS,
      ResultSubstitutionSP subst, bool eqIsResult);

#if VDEBUG
  void setTestIndices(Stack<Index*> const& indices) override {
    _lhsIndex = (InductionEqualityLHSIndex*)indices[0];
    _stIndex = (InductionInequalitySubtermIndex*)indices[1];
  }
#endif

private:
  ClauseIterator generateClauses(Literal* lit, Clause* premise);

  InductionEqualityLHSIndex *_lhsIndex;
  InductionInequalitySubtermIndex* _stIndex;
  GeneratingInferenceEngine* _induction;
  Splitter* _splitter;
  unique_ptr<DuplicateLiteralRemovalISE> _dupLitRemoval;
};

}; // namespace Inferences

#endif /* __InductionHypothesisRewriting__ */
