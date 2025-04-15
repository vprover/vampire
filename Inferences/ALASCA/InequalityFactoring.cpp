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
    return nothing();                                                                               \
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

  auto nothing = [&]() { return arrayIter(SmallArray()); };

  auto s1 = l1.selectedAtomicTerm();
  auto s2 = l2.selectedAtomicTerm();

  auto sigma = [&](auto x){ return uwa.subs().apply(x, /* varbank */ 0); };
  auto j = l1.numeral();
  auto k = l2.numeral();
  ASS_EQ(l1.clause(), l2.clause())
  auto premise = l1.clause();

  /////////////////////////////////////////////////////////////////////////////////////
  // applicability checks
  //////////////////////////////////////////////////////

  CHECK_CONDITION("sign(j) == sign(k)", j.sign() == k.sign())
  ASS(j.sign() != Sign::Zero)
  ASS(j.isPositive())

  auto s1σ = sigma(s1);
  // Stack<TermList> t1σ;
  CHECK_CONDITION("s1σ /⪯ terms(t1)σ",
      l1.contextTerms() 
        .all([&](auto ki_ti) {
          auto tiσ = sigma(ki_ti.atom());
          // t1σ.push(NumTraits::mulSimpl(ki_ti.numeral(), tiσ));
          return _shared->notLeq(TermList(s1σ), tiσ);
        }));

  auto s2σ = sigma(s2);
  // Stack<TermList> t2σ;
  CHECK_CONDITION("s2σ /⪯ terms(t2)σ",
      l2.contextTerms() 
        .all([&](auto ki_ti) {
          auto tiσ = sigma(ki_ti.atom());
          // t2σ.push(NumTraits::mulSimpl(ki_ti.numeral(), tiσ));
          return _shared->notLeq(TermList(s2σ), tiσ);
        }));

  // // •    (j s1 + t1 >1 0)σ /≺ (k s2 + t2 >2 0 \/ C)σ <- cond1
  // //   or (k s2 + t2 >2 0)σ /≺ (j s1 + t1 >1 0 \/ C)σ <- cond2


  CHECK_CONDITION(
      "(j s1 + t1 >1 0)σ /≺ (k s2 + t2 >2 0 \\/ C)σ or (k s2 + t2 >2 0)σ /≺ (j s1 + t1 >1 0 \\/ C)σ",
      // TODO 2 use the DSL
          AlascaOrderingUtils::litMaxAfterUnif(_shared->ordering, l2, SelectionCriterion::NOT_LESS, uwa, /*varBank=*/ 0, [](auto msg) {  })
       || AlascaOrderingUtils::litMaxAfterUnif(_shared->ordering, l1, SelectionCriterion::NOT_LESS, uwa, /*varBank=*/ 0, [](auto msg) {  })
      );



  // • (>3) = if (>1, >2) = (>=, >) then (>=) 
  //                                else (>)
  auto less3 = [](auto& l1, auto& l2) {
    return l1.symbol() == AlascaPredicate::GREATER_EQ 
        && l2.symbol() == AlascaPredicate::GREATER ? AlascaPredicate::GREATER_EQ
                                                   : AlascaPredicate::GREATER; };

  auto i1 = l1.litIdx();
  auto i2 = l2.litIdx();
  ASS(i1 < i2)
  auto ctxtLits =  [&]() { return l1.allLiterals()
           .dropNth(i2)
           .dropNth(i1); };

  auto cnst  = uwa.computeConstraintLiterals();

  auto k_t1_minus_j_t2σ = /* (k t1 − j t2)σ */
         NumTraits::sum(concatIters(
            l1.contextTerms().map([&](auto t) { return  sigma(( k * t).toTerm()); }),
            l2.contextTerms().map([&](auto t) { return  sigma((-j * t).toTerm()); })));

  Inference inf(GeneratingInference1(Kernel::InferenceRule::ALASCA_LITERAL_FACTORING, premise));

  auto L1σ = sigma(l1.literal()); // <- (j s1 + t1 >1 0)σ
  auto L2σ = sigma(l2.literal()); // <- (j s2 + t2 >2 0)σ

  auto c1 = [&]() { 
    return Clause::fromIterator(concatIters(
       iterItems(
         /* (k t1 − j t2 >3 0)σ */ createLiteral<NumTraits>(less3(l1, l2), k_t1_minus_j_t2σ),
         /*   (±ks2 + t2 <> 0)σ */ L2σ 
       ),
       ctxtLits(),
       arrayIter(cnst).cloned()
    ), inf);
  };

  auto c2 = [&]() { 
    return Clause::fromIterator(concatIters(
       iterItems(
         /* -(k t1 − j t2 >3' 0)σ */ createLiteral<NumTraits>(less3(l2, l1), NumTraits::minus(k_t1_minus_j_t2σ)),
         /*   (±js1 + t1 <> 0)σ */ L1σ 
       ),
       ctxtLits(),
       arrayIter(cnst).cloned()
    ), inf);
  };

  auto out = InequalityNormalizer::normalize(L1σ) == InequalityNormalizer::normalize(L2σ)
    /* optimization to not create duplicate clauses, as in this case c1() and c2() are equivalent */
    ? SmallArray::fromItems(Clause::fromIterator(concatIters(
       iterItems( /*   (±js1 + t1 <> 0)σ */ L1σ ),
       ctxtLits(),
       arrayIter(cnst).cloned()
    ), inf))
    : SmallArray::fromItems(c1(), c2());

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



  static auto literalMaximality() { return SelectionCriterion::NOT_LESS; }
  // TODO 2 double check NOT_LEQ
  static auto    atomicTermMaxmialityLocal() { return SelectionCriterion::NOT_LEQ; }

  static auto iter(AlascaState& shared, __SelectedLiteral const& lit) {
    return SelectedAtomicTermItpAny::iter(shared.ordering, lit, atomicTermMaxmialityLocal())
          .filter([](auto& s) { return s.apply([](auto& s) { return 
              s.isInequality()
              && s.numeral().sign() == Sign::Pos; 
              }); })
      .map([](auto x) { return Lhs(x); });
  }
  // TODO 2 sort out post unificaiton check and symmetry breaking
};

ClauseIterator InequalityFactoring::generateClauses(Clause* premise) 
{
  TIME_TRACE("alasca inequality factoring generate")
  DEBUG("in: ", *premise)


  // TODO think about this, we don't want any literals but one of the two hast to be weakly maximal
    auto selected = 
        _shared->selected(premise)
          .flatMap([&](auto lit) { return Lhs::iter(*_shared, lit); })
          .collectRStack();

    auto nonSelected = 
      range(0, premise->size())
          .flatMap([&](auto i) { return Lhs::iter(*_shared, __SelectedLiteral(premise, i, /*bgSelected*/ false /* don't care */)); })
          .collectRStack();




  return pvi(arrayIter(std::move(selected))
      .flatMap([this,nonSelected = std::move(nonSelected)](auto l1) {
        return arrayIter(*nonSelected)
          .filter([=](auto& l2) { return l1.litIdx()    != l2.litIdx(); })
          .filter([=](auto& l2) { return l1.numTraits() == l2.numTraits(); })
          .flatMap([=](auto& l2) {
              return iterTraits(_shared->unify(l1.selectedAtomicTerm(), l2.selectedAtomicTerm())
                  .intoIter())
                  .flatMap([this, &l1, &l2](auto uwa) {
                      return this->applyRule(l1, l2, uwa);
                  });
          });
      }));
}

  

#if VDEBUG
void InequalityFactoring::setTestIndices(Stack<Indexing::Index*> const&) { }
#endif

} // namespace ALASCA 
} // namespace Inferences 
