/*
 * This file is part of the source code of the software program Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __TEST_ALASCA_SIMPL_RULE__
#define __TEST_ALASCA_SIMPL_RULE__

#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/ALASCA.hpp"
#include "Kernel/Theory.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Indexing/TermSharing.hpp"
#include "Inferences/ALASCA/VIRAS.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/ALASCA/Normalization.hpp"
#include "Test/GenerationTester.hpp"

template<class Rule>
struct AlascaSimplRule 
  : public SimplifyingGeneratingInference
{
  Rule _rule;
  ALASCA::Normalization _norm;
  AlascaSimplRule(Rule r, ALASCA::Normalization n) : _rule(std::move(r)), _norm(std::move(n)) {}

  void attach(SaturationAlgorithm* salg) final override {
    _rule.attach(salg);
    _norm.attach(salg);
  }

  void detach() final override {
    _rule.detach();
    _norm.detach();
  }

  ClauseGenerationResult generateSimplify(Clause* premise) final override {
    auto res = _rule.generateSimplify(_norm.simplify(premise));
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
AlascaSimplRule<Rule> alascaSimplRule(Rule r, ALASCA::Normalization n) { return AlascaSimplRule<Rule>(std::move(r), std::move(n)); }

template<class ISE>
struct ToSgi : SimplifyingGeneratingInference {
  ISE self;

  ToSgi(ISE ise) : self(std::move(ise)) {}

  void attach(SaturationAlgorithm* salg) final override { }

  void detach() final override { }
ClauseGenerationResult generateSimplify(Clause* premise) final override { auto concl = self.simplify(premise);
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


template<class Rule> 
class AlascaGenerationTester : public Test::Generation::GenerationTester<AlascaSimplRule<Rule>>
{
 public:
  AlascaGenerationTester(AlascaSimplRule<Rule> r) : Test::Generation::GenerationTester<AlascaSimplRule<Rule>>(std::move(r)) { }



  virtual Clause* normalize(Kernel::Clause* c) override 
  { return Test::Generation::GenerationTester<AlascaSimplRule<Rule>>::_rule._norm.simplify(c); }

  virtual bool eq(Kernel::Clause* lhs, Kernel::Clause* rhs) override
  { 
    // auto state = testAlascaState();
    // return Test::TestUtils::permEq(*lhs, *rhs, [&](auto l, auto r) { return state->norm().equivalent(l,r); });
    return Test::TestUtils::eqModACRect(normalize(lhs), normalize(rhs));
  }
};



inline void overrideFractionalNumerals(IntTraits n) { }

template<class NumTraits>
void overrideFractionalNumerals(NumTraits n) {
  SyntaxSugarGlobals::instance().overrideFractionCreation([&](int n, int m) {
      return n == 1 && m == 1 ? NumTraits::one() 
           : NumTraits::linMul(NumTraits::constant(n, m), NumTraits::one());
  });
}

template<class NumTraits>
void mkAlascaSyntaxSugar(NumTraits n) {

  SyntaxSugarGlobals::instance().overrideMulOperator([&](auto lhs, auto rhs) {
    auto linMul = [](auto lhs, auto rhs) {
      return NumTraits::ifLinMul(lhs, [&](auto num, auto t) {
          return someIf(t == NumTraits::one(), 
              [&]() { return NumTraits::linMul(num, rhs); });
      }).flatten();
    };
    return linMul(lhs,rhs) || linMul(rhs, lhs) || NumTraits::mul(lhs, rhs); 
  });

  SyntaxSugarGlobals::instance().overrideNumeralCreation([&](int i) {
      return i == 1 ? NumTraits::one() 
           : NumTraits::linMul(NumTraits::constant(i), NumTraits::one());
  });

  SyntaxSugarGlobals::instance().overrideMinus([&](auto t) {
      return NumTraits::linMul(NumTraits::constant(-1), t);
  });

  overrideFractionalNumerals(n);
}



#endif // def __TEST_ALASCA_SIMPL_RULE__
