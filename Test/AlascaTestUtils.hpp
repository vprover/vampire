/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
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
#include "Test/TestUtils.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Inferences/ALASCA/Normalization.hpp"
#include "Test/GenerationTester.hpp"

template<class Rule>
struct AlascaSimplRule 
  : public SimplifyingGeneratingInference
{
  Rule _rule;
  ALASCA::Normalization _norm;
  AlascaSimplRule(SaturationAlgorithm& salg)
    : _rule(salg)
    , _norm(salg)
  { }

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
};

template<class ISE>
struct ToSgi : SimplifyingGeneratingInference {
  ISE self;

  ToSgi(SaturationAlgorithm& salg) : self(salg) {}

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


struct AlascaTestUtil {

  // static Clause* normalize(ALASCA::Normalization& norm, Kernel::Clause* c)
  // { return norm.simplify(c); }

  static bool eq(ALASCA::Normalization& norm, Kernel::Clause* lhs, Kernel::Clause* rhs)
  { 
    lhs = norm.simplify( lhs);
    rhs = norm.simplify( rhs);
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
        auto r = norm.simplify(renamed);
        return Test::TestUtils::eqModAC(lhs, r); 
    });
  }
};

class AlascaGenerationTester : public Test::Generation::GenerationTester
{
  ALASCA::Normalization _norm;

public:
  AlascaGenerationTester(SaturationAlgorithm& salg)
    : GenerationTester(salg), _norm(salg)
  {}

  Clause* normalize(Kernel::Clause* c) override
  { return _norm.simplify(c); }

  bool eq(Kernel::Clause* lhs, Kernel::Clause* rhs) override
  { return AlascaTestUtil::eq(_norm, lhs, rhs); }
};

inline void overrideFractionalNumerals(IntTraits n) { }

template<class NumTraits>
void overrideFractionalNumerals(NumTraits n) {
  using ASig = AlascaSignature<NumTraits>;
  SyntaxSugarGlobals::instance().overrideFractionCreation([&](int n, int m) {
      return ASig::numeralTl(typename ASig::ConstantType(n,m));
  });
}

template<class NumTraits>
void mkAlascaSyntaxSugar(NumTraits n) {
  using ASig = AlascaSignature<NumTraits>;
  SyntaxSugarGlobals::instance().overrideMulOperator([&](auto lhs, auto rhs) {
    auto tryLinMul = [](auto lhs, auto rhs) -> Option<TermList> {
      if (auto n =  ASig::tryNumeral(lhs)) {
        return some(ASig::linMul(*n, rhs));
      } else {
        return {};
      }
    };
    return tryLinMul(lhs,rhs) || tryLinMul(rhs, lhs) || NumTraits::mul(lhs, rhs); 
  });

  SyntaxSugarGlobals::instance().overrideNumeralCreation([&](int i) {
      return ASig::numeralTl(i);
  });

  SyntaxSugarGlobals::instance().overrideMinus([&](auto t) {
      return ASig::minus(t);
  });

  overrideFractionalNumerals(n);
}

inline Test::OptionMap alascaTestOptions(const char* uwaMode = "alasca_main") {
  return {
    { "abstracting_linear_arithmetic_superposition_calculus", "on" },
    { "term_ordering", "qkbo" },
    { "unification_with_abstraction", uwaMode },
  };
}

inline auto alascaSymmetricTest(const char* uwaMode = "alasca_main") {
  return Test::Generation::SymmetricTest()
    .options(alascaTestOptions(uwaMode));
}

#endif // def __TEST_ALASCA_SIMPL_RULE__
