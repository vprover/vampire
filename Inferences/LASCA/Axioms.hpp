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
 * @file Axioms.hpp
 * Defines class Axioms
 *
 */

#ifndef __LASCA_Axioms
#define __LASCA_Axioms

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/LASCA.hpp"
#include "Kernel/Ordering.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Indexing/LascaIndex.hpp"
#include "Superposition.hpp"
#include "FourierMotzkin.hpp"
#include "Shell/Options.hpp"
#include "Lib/Metaiterators.hpp"
#define DEBUG_FM(lvl, ...) if (lvl <= 0) DBG(__VA_ARGS__)

namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class AxiomRule 
  : public GeneratingInferenceEngine 
{
  using NumTraits = RealTraits;

  std::shared_ptr<LascaState> _shared;

  static TermList floor(TermList t) { return TermList(NumTraits::floor(t)); }
  static TermList minus(TermList t) { return TermList(NumTraits::minus(t)); }
  static TermList ceil(TermList t) { return minus(floor(minus(t))); }

  template<class... Args>
  static TermList sum(Args... args) 
  { return NumTraits::sum(iterItems(args...)); }

  static Literal* greater0(TermList t) 
  { return NumTraits::greater(/* polarity */ true, t, NumTraits::zero()); }

  static Literal* geq0(TermList t) 
  { return NumTraits::geq(/* polarity */ true, t, NumTraits::zero()); }

  static Literal* eq(TermList s, TermList t) 
  { return NumTraits::eq(/* polarity */ true, s, t); }

  static TermList numeral(int i) 
  { return NumTraits::constantTl(i); }

  template<class Premise, class... Lits>
  static auto resClause(Premise const& premise, Lits... lits) {
    return Clause::fromIterator(
        concatIters(premise.contextLiterals(), iterItems(lits...)),
        GeneratingInference1(InferenceRule::LASCA_AXIOM_RULE, premise.clause()));
  }

  auto generateClauses(Superposition::Lhs const& premise) const
  {
    return iterItems<Clause*>();
    // auto s = NumTraits::ifFloor(premise.selectedTerm(), [](auto s) { return s; }).unwrap();
    // auto t = premise.smallerSide();
    // return iterItems(
    //     resClause(premise, geq0(sum(s, minus(t))))
    //   , resClause(premise, eq(t, floor(t))) // <- TODO this derivation is a hack, it creates something greater
    //   , resClause(premise, greater0(sum(minus(s), t, numeral(1))))
    // );
  }

  auto generateClauses(FourierMotzkin::Lhs const& premise) const 
  {
    ASS(premise.numeral<NumTraits>().isPositive())
    auto s = NumTraits::ifFloor(premise.selectedTerm(), [](auto s) { return s; }).unwrap();
    auto t = premise.notSelectedTerm();
    auto pred = premise.lascaPredicate().unwrap();
    ASS(isInequality(pred))

    return iterItems(resClause(premise, createLiteral<NumTraits>(pred, sum(s, t))));


    //
    // switch (pred) {
    //   case LascaPredicate::EQ:
    //   case LascaPredicate::NEQ:
    //   case LascaPredicate::IS_INT_POS:
    //   case LascaPredicate::IS_INT_NEG:
    //     ASSERTION_VIOLATION
    //   case LascaPredicate::GREATER:
    //   case LascaPredicate::GREATER_EQ:
    //     break;
    // }
    //
    // return ifElseIter2(pred == LascaPredicate::GREATER_EQ,
    //     iterItems(
    //           resClause(premise, greater0(sum(floor(s), t, numeral(1))))
    //         , resClause(premise, greater0(sum(s, t))
    //                            , eq(s, floor(s)))
    //         ),
    //     iterItems(
    //         resClause(premise, greater0(sum(s, t)))
    //             )
    //     );
  }


  auto generateClauses(FourierMotzkin::Rhs const& premise) const 
  {
    ASS(premise.numeral<NumTraits>().isNegative())
    auto s = NumTraits::ifFloor(premise.selectedTerm(), [](auto s) { return s; }).unwrap();
    auto t = premise.notSelectedTerm();
    auto pred = premise.lascaPredicate().unwrap();
    ASS(isInequality(pred))

    return iterItems(resClause(premise, greater0(sum(minus(s), t, numeral(1)))));

    // switch (pred) {
    //   case LascaPredicate::EQ:
    //   case LascaPredicate::NEQ:
    //   case LascaPredicate::IS_INT_POS:
    //   case LascaPredicate::IS_INT_NEG:
    //     ASSERTION_VIOLATION
    //   case LascaPredicate::GREATER:
    //   case LascaPredicate::GREATER_EQ:
    //     break;
    // }
    // return concatIters(
    //     iterItems(resClause(premise, greater0(sum(minus(s), t, numeral(1))))),
    //     ifElseIter2(pred == LascaPredicate::GREATER,
    //       // TODO make sure this matches the theory. i.e. we're using greater0 instead of geq0 in the implementation. make sure this is sound and write it down in the theory part!!!!
    //           iterItems(resClause(premise, greater0(sum(minus(s), ceil(t))))),
    //           VirtualIterator<Clause*>::getEmpty()
    //       )
    //     );
  }

  template<class RuleKind>
  auto generateClauses(Clause* premise) const {
    return iterTraits(RuleKind::iter(*_shared, premise))
      .filter([](auto x) { return NumTraits::ifFloor(x.selectedTerm(), [](auto...) { return true; }); })
      .flatMap([this](auto x) { return this->generateClauses(x); });
  }

public:
  USE_ALLOCATOR(AxiomRule);

  AxiomRule(AxiomRule&&) = default;
  AxiomRule(std::shared_ptr<LascaState> shared) 
    : _shared(std::move(shared))
  {  }

  void attach(SaturationAlgorithm* salg) final override 
  { GeneratingInferenceEngine::attach(salg); }

  void detach() final override
  { ASS(_salg); GeneratingInferenceEngine::detach(); }

  ClauseIterator generateClauses(Clause* premise) final override
  {
    return pvi(concatIters(
          generateClauses<Superposition::Lhs>(premise),
          generateClauses<FourierMotzkin::Lhs>(premise),
          generateClauses<FourierMotzkin::Rhs>(premise)
    ));
  }

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const& indices) final override
  { }
#endif
    
};

} // namespace LASCA 
} // namespace Inferences 


#endif /*__LASCA_Axioms*/
