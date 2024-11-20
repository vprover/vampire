/*
 * This file is part of the source code of the software program Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __TEST_LASCA_SIMPL_RULE__
#define __TEST_LASCA_SIMPL_RULE__

#include "Kernel/Inference.hpp"
#include "Kernel/LASCA.hpp"
#include "Kernel/Theory.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Indexing/TermSharing.hpp"
#include "Inferences/LASCA/VIRAS.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/LASCA/Normalization.hpp"

template<class Rule>
struct LascaSimplRule 
  : public SimplifyingGeneratingInference
{
  Rule _rule;
  LASCA::Normalization _norm;
  LascaSimplRule(Rule r, LASCA::Normalization n) : _rule(std::move(r)), _norm(std::move(n)) {}

  void attach(SaturationAlgorithm* salg) final override {
    _rule.attach(salg);
    _norm.attach(salg);
  }

  void detach() final override {
    _rule.detach();
    _norm.detach();
  }

  ClauseGenerationResult generateSimplify(Clause* premise) final override {
    auto res = _rule.generateSimplify(premise);
    return ClauseGenerationResult {
      .clauses = pvi(iterTraits(std::move(res.clauses))
            .filterMap([this](auto cl) { 
              auto simpl = _norm.simplify(cl);
              return someIf(simpl != nullptr, [&]() { return simpl; }); })),
      .premiseRedundant = res.premiseRedundant,
    };
  }

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const& i) final override {
    _rule.setTestIndices(i);
    _norm.setTestIndices(i);
  }
#endif
};
template<class Rule>
LascaSimplRule<Rule> lascaSimplRule(Rule r, LASCA::Normalization n) { return LascaSimplRule<Rule>(std::move(r), std::move(n)); }

template<class ISE>
struct ToSgi : SimplifyingGeneratingInference {
  ISE self;

  ToSgi(ISE ise) : self(ise) {}

  void attach(SaturationAlgorithm* salg) final override { }

  void detach() final override { }

  ClauseGenerationResult generateSimplify(Clause* premise) final override {
    auto concl = self.simplify(premise);
    return concl == nullptr 
         ? ClauseGenerationResult {
             .clauses = pvi(iterItems<Clause*>()),
             .premiseRedundant = true,
           }

         : concl == premise 
         ? ClauseGenerationResult {
             .clauses = pvi(iterItems<Clause*>()),
             .premiseRedundant = false,
           }

         : ClauseGenerationResult {
             .clauses = pvi(iterItems<Clause*>(concl)),
             .premiseRedundant = true,
           };
  }
};

template<class ISE>
ToSgi<ISE> toSgi(ISE ise) { return ToSgi<ISE>(std::move(ise)); }



#endif // def __TEST_LASCA_SIMPL_RULE__
