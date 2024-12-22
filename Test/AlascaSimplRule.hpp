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

#include "Kernel/ALASCA/State.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/ALASCA.hpp"
#include "Kernel/Theory.hpp"
#include "Test/TestUtils.hpp"
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
  Option<std::shared_ptr<AlascaState>> _state;
  Rule _rule;
  ALASCA::Normalization _norm;
  AlascaSimplRule()
    : _state(testAlascaState()) 
    , _rule(*_state)
    , _norm(*_state)
  { }

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
  AlascaGenerationTester() : AlascaGenerationTester(AlascaSimplRule<Rule>()) { }

  virtual Clause* normalize(Kernel::Clause* c) override 
  { return Test::Generation::GenerationTester<AlascaSimplRule<Rule>>::_rule._norm.simplify(c); }

  virtual bool eq(Kernel::Clause* lhs, Kernel::Clause* rhs) override
  { 
    lhs = normalize(lhs);
    rhs = normalize(rhs);
    auto vars = [](auto cl) {
      auto vs = cl->iterLits()
        .flatMap([](Literal* lit) { return vi(new VariableIterator(lit)); })
        .template collect<Stack>();
      vs.sort();
      vs.dedup();
      return vs;
    };

    auto vl = vars(lhs);
    auto vr = vars(rhs);

    Map<TermList, unsigned> rVarIdx;
    unsigned i = 0;
    for (auto v : vr) {
      rVarIdx.insert(v, i++);
    }

    if (vl.size() != vr.size()) return false;

    return Test::anyPerm(vl.size(), [&](auto& perm) { 
        Renaming rn;
        auto renamed = Clause::fromIterator(
            rhs->iterLits()
            .map([&](auto l) {
              return Literal::createFromIter(l, anyArgIter(l)
                  .map([&](auto t) {
                    return BottomUpEvaluation<TermList, TermList>()
                    .context(TermListContext {.ignoreTypeArgs = false})
                    .function([&](auto t, auto* args) {
                        if (t.isVar()) {
                          return vl[perm[rVarIdx.get(t)]];
                        } else {
                          return TermList(Term::create(t.term(), args));
                        }
                      })
                      .apply(t);
                    }));
              }),
            Inference(NonspecificInference1(InferenceRule::RECTIFY, rhs)));
        auto r = normalize(renamed);
        return Test::TestUtils::eqModAC(lhs, r); 
    });
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
