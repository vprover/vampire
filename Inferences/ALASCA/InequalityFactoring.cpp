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
 * @file InequalityFactoring.cpp
 * Defines class InequalityFactoring
 *
 */

#include "InequalityFactoring.hpp"
#include "Debug/Assertion.hpp"
#include "Inferences/ALASCA/BinInf.hpp"
#include "Kernel/ALASCA/Ordering.hpp"
#include "Kernel/ALASCA/SelectionPrimitves.hpp"
#include "Kernel/UnificationWithAbstraction.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Shell/Statistics.hpp"
#include "Debug/TimeProfiling.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {
namespace ALASCA {

void InequalityFactoring::attach(SaturationAlgorithm* salg) { }

void InequalityFactoring::detach() { }


#define CHECK_CONDITION(name, condition)                                                            \
  if (!(condition)) {                                                                               \
    DEBUG("side condition not satisfied: " name)                                                    \
  }                                                                                                 \

//  C \/ +j s1 + t1 >1 0 \/ +k s2 + t2 >2 0
// ====================================================
// (C \/ k t1 − j t2 >3 0 \/ +k s2 + t2 >2 0) σ \/ Cnst
//
// TODO update to selection function version
//
// where
// • ⟨σ,Cnst⟩ = uwa(s1,s2)
// • >i ∈ {>,≥}
// • s1σ /⪯ terms(t1)σ
// • s2σ /⪯ terms(t2)σ
// •    (j s1 + t1 >1 0)σ /≺ (k s2 + t2 >2 0 \/ C)σ
//   or (k s2 + t2 >2 0)σ /≺ (j s1 + t1 >1 0 \/ C)σ
// • (>3) = if (>1, >2) = (>=, >) then (>=) 
//                                else (>)

template<class NumTraits>
InequalityFactoring::Iter InequalityFactoring::applyRule(
    SelectedAtomicTermItp<NumTraits> const& l1,  // +j s1 + t1 >1 0
    SelectedAtomicTermItp<NumTraits> const& l2,  // +k s2 + t2 >2 0
    AbstractingUnifier& uwa
    )
{
  TIME_TRACE("alasca inequality factoring application")
  DEBUG("l1: ", l1)
  DEBUG("l2: ", l2)

  auto nothing = [&]() { return arrayIter(SArray()); };


  auto sigma = [&](auto x){ return uwa.subs().apply(x, /* varbank */ 0); };
  auto j = l1.numeral();
  auto k = l2.numeral();
  ASS_EQ(l1.clause(), l2.clause())
  auto premise = l1.clause();

  /////////////////////////////////////////////////////////////////////////////////////
  // applicability checks
  //////////////////////////////////////////////////////

  {
    namespace C = ApplicabilityCheck;
    auto ll1 = std::make_pair(&l1, unsigned(/* varBank */ 0));
    auto ll2 = std::make_pair(&l2, unsigned(/* varBank */ 0));

    auto applicableTerms = C::all(
              C::TermMaximalityConstraint { .max = SelectionCriterion::NOT_LESS, .local = false, },
              C::TermMaximalityConstraint { .max = SelectionCriterion::NOT_LEQ, .local = true, }
            ).checkAfterUnif(ll1, _shared->ordering, uwa, [](auto msg) { DEBUG("l1 :", msg) }) 
      && C::all(
              C::TermMaximalityConstraint { .max = SelectionCriterion::NOT_LESS, .local = false, },
              C::TermMaximalityConstraint { .max = SelectionCriterion::NOT_LEQ, .local = true, }
            ).checkAfterUnif(ll2, _shared->ordering, uwa, [](auto msg) { DEBUG("l2 :", msg) });

    auto applicableLiteral = 
        C::LiteralMaximalityConstraint { .max = SelectionCriterion::NOT_LESS, }
          .checkAfterUnif(ll1, _shared->ordering, uwa, [](auto msg) { DEBUG("l1 :", msg) })
     || C::LiteralMaximalityConstraint { .max = SelectionCriterion::NOT_LESS, }
          .checkAfterUnif(ll2, _shared->ordering, uwa, [](auto msg) { DEBUG("l2 :", msg) });

    auto applicable = applicableTerms && applicableLiteral;

    if (!applicable) {
      return nothing();
    }
  }

  ASS(j.sign() == k.sign())
  ASS(j.sign() == Sign::Pos)

  // • (>3) = if (>1, >2) = (>=, >) then (>=) 
  //                                else (>)
  auto less3 = [](auto& l1, auto& l2) {
    return l1.symbol() == AlascaPredicate::GREATER_EQ 
        && l2.symbol() == AlascaPredicate::GREATER ? AlascaPredicate::GREATER_EQ
                                                   : AlascaPredicate::GREATER; };

  auto i1 = l1.litIdx();
  auto i2 = l2.litIdx();
  auto ctxtLitsσ =  [&]() { return l1.allLiterals()
           .dropNth(std::max(i1,i2))
           .dropNth(std::min(i1,i2))
           .map([&](auto l) { return sigma(l); }); };

  auto cnst  = uwa.computeConstraintLiterals();

  auto k_t1_minus_j_t2σ = /* (k t1 − j t2)σ */
         NumTraits::sum(concatIters(
            l1.contextTerms().map([&](auto t) { return  sigma(( k * t).toTerm()); }),
            l2.contextTerms().map([&](auto t) { return  sigma((-j * t).toTerm()); })));

  auto inf = [&]() { return Inference(GeneratingInference1(Kernel::InferenceRule::ALASCA_LITERAL_FACTORING, premise)); };

  auto L1σ = sigma(l1.literal()); // <- (j s1 + t1 >1 0)σ
  auto L2σ = sigma(l2.literal()); // <- (j s2 + t2 >2 0)σ

  auto c1 = [&]() { 
    return Clause::fromIterator(concatIters(
       iterItems(
         /* (k t1 − j t2 >3 0)σ */ createLiteral<NumTraits>(less3(l1, l2), k_t1_minus_j_t2σ),
         /*   (±ks2 + t2 <> 0)σ */ L2σ 
       ),
       ctxtLitsσ(),
       arrayIter(cnst).cloned()
    ), inf());
  };

  auto c2 = [&]() { 
    return Clause::fromIterator(concatIters(
       iterItems(
         /* -(k t1 − j t2 >3' 0)σ */ createLiteral<NumTraits>(less3(l2, l1), NumTraits::minus(k_t1_minus_j_t2σ)),
         /*   (±js1 + t1 <> 0)σ */ L1σ 
       ),
       ctxtLitsσ(),
       arrayIter(cnst).cloned()
    ), inf());
  };

  auto out = InequalityNormalizer::normalize(L1σ) == InequalityNormalizer::normalize(L2σ)
    /* optimization to not create duplicate clauses, as in this case c1() and c2() are equivalent */
    ? SArray::fromItems(Clause::fromIterator(concatIters(
       iterItems( /*   (±js1 + t1 <> 0)σ */ L1σ ),
       ctxtLitsσ(),
       arrayIter(cnst).cloned()
    ), inf()))
    : SArray::fromItems(c1(), c2());

  DEBUG("conclusion: ", out)
  return arrayIter(std::move(out));
}

InequalityFactoring::Iter InequalityFactoring::applyRule(SelectedAtomicTermItpAny const& l1, SelectedAtomicTermItpAny const& l2, AbstractingUnifier& uwa)
{
  return l1.apply([&](auto& l1) {
    ASS_EQ(l1.clause(), l2.clause())
    return applyRule(l1, l2.template unwrap<std::remove_const_t<std::remove_reference_t<decltype(l1)>>>(), uwa);
  });
}

struct Lhs : public SelectedAtomicTermItpAny {

  Lhs(SelectedAtomicTermItpAny self) : SelectedAtomicTermItpAny(std::move(self)) {}

  static auto iter(AlascaState& shared, __SelectedLiteral const& lit) {
    return SelectedAtomicTermItpAny::iter(shared.ordering, lit, SelectionCriterion::NOT_LESS)
          .filter([](auto& s) { return s.apply([](auto& s) { return 
                    s.isInequality() 
                &&  s.numeral().sign() == Sign::Pos 
                && !s.selectedAtomicTerm().isVar();
                }); })
      .map([](auto x) { return Lhs(x); });
  }

};

struct IterAppls {
  auto iter(AlascaState& shared, __SelectedLiteral lit, Stack<RStack<Lhs>>& all) {
    return Lhs::iter(shared, lit)
      .flatMap([&all](auto l1) { 
          // all[l1.litIdx()]->reset();
          return arrayIter(all)
            .flatMap([](auto& x) { return arrayIter(x); })
            .filter([=](auto& l2) { return l1.litIdx() != l2.litIdx(); })
            .filter([=](auto& l2) { return l1.numTraits() == l2.numTraits(); })
            .map([=](auto l2) { return std::make_pair(l1, l2); });
      });
  }
  auto allL2(AlascaState& shared, Clause* cl) {
    return range(0, cl->size())
          .map([&shared,cl](auto i) { return Lhs::iter(shared, __SelectedLiteral(cl, i, /*bgSelected*/ false /* don't care */)).collectRStack(); })
          .collectRStack();
  }
  auto iter(AlascaState& shared, __SelectedLiteral lit) {
    auto l2s = allL2(shared, lit.clause());
    auto& l2sPtr = *l2s;
    return iter(shared, lit, l2sPtr)
      .store(std::move(l2s));
  }
};

VirtualIterator<std::tuple<>> InequalityFactoring::lookaheadResultEstimation(__SelectedLiteral const& selection)
{ return pvi(dropElementType(IterAppls{}.iter(*_shared, selection))); }

ClauseIterator InequalityFactoring::generateClauses(Clause* premise) 
{
  TIME_TRACE("alasca inequality factoring generate")
  DEBUG("in: ", *premise)

  auto selectedLits_ = _shared->selected(premise).map([](auto lit) { return lit.litIdx(); }).collectRStack();
  auto& selectedLits = *selectedLits_;

  return pvi(_shared->selected(premise)
        .flatMap([this, &selectedLits](auto lit) mutable { 
          return IterAppls{}.iter(*_shared, lit)
              .flatMap([this,&selectedLits](auto l1_l2) {
                  auto& l1 = l1_l2.first;
                  auto& l2 = l1_l2.second;

                  auto bothSelected = selectedLits.find(l2.litIdx());

                  return ifElseIter(
                      /* symmetry breaking */
                      bothSelected && l1.litIdx() > l2.litIdx(), 
                      [&]() { return iterItems<Clause*>(); },

                      [&]() { return iterTraits(_shared->unify(l1.selectedAtomicTerm(), l2.selectedAtomicTerm()).intoIter())
                            .flatMap([this, l1, l2](auto uwa) { return this->applyRule(l1, l2, uwa); }); });
              });
          })
          .store(std::move(selectedLits_))
          // .store(std::move(l2s))
    );
}

} // namespace ALASCA 
} // namespace Inferences 
