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
 * @file EqFactoring.cpp
 * Defines class EqFactoring
 *
 */

#include "EqFactoring.hpp"
#include "Debug/TimeProfiling.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {
namespace ALASCA {

void EqFactoring::attach(SaturationAlgorithm* salg) 
{ }

void EqFactoring::detach() 
{ }

//  Integer version
//
//  C \/ j s1 ≈ t1 \/ k s2 ≈ t2
// ===================================================
// (C \/ j s1 ≈ t1 \/ k t1  ̸≈ j t2) σ \/ Cnst
//
// where
// • uwa(s1,s2)=⟨σ,Cnst⟩
// • s1σ /⪯ t1σ
// • s2σ /⪯ t2σ
// • (s2 ≈ t2)σ /< (s1 ≈ t1 \/ C)σ


//  C \/ s1 ≈ t1 \/ s2 ≈ t2
// ===================================================
// (C \/ s1 ≈ t1 \/ t1  ̸≈ t2) σ \/ Cnst
//
// where
// • uwa(s1,s2)=⟨σ,Cnst⟩
// • s1σ /⪯ t1σ
// • s2σ /⪯ t2σ
// • (s2 ≈ t2)σ /< (s1 ≈ t1 \/ C)σ

Option<Clause*> EqFactoring::applyRule(SelectedEquality const& l1, SelectedEquality const& l2)
{
  TIME_TRACE("alasca equality factoring application")
  DEBUG("============")
  DEBUG("l1: ", l1)
  DEBUG("l2: ", l2)


  auto unifySorts = [](auto s1, auto s2) -> Option<TermList> {
    static RobSubstitution subst;
    if (!subst.unify(s1, 0, s2, 0)) {
      return Option<TermList>();
    } else {
      ASS_EQ(subst.apply(s1,0), subst.apply(s2,0))
      return Option<TermList>(subst.apply(s1, 0));
    }
  };

  auto nothing = [&]() { return Option<Clause*>(); };

  auto s1 = l1.biggerSide();
  auto s2 = l2.biggerSide();
  auto t1 = l1.smallerSide();
  auto t2 = l2.smallerSide();

  ASS (l1.positive() && l2.positive())
  // ASS(!s1.isVar())
  // ASS(!s2.isVar())
  ASS(!l1.isFracNum() || !l1.biggerSide().isVar())
  ASS(!l2.isFracNum() || !l2.biggerSide().isVar())

#define check_side_condition(cond, cond_code)                                                       \
    if (!(cond_code)) {                                                                             \
      DEBUG("side condition not fulfilled: ", cond)                                                 \
      return nothing();                                                                             \
    }                                                                                               \

  auto srt_ = unifySorts(
      SortHelper::getEqualityArgumentSort(l1.literal()),
      SortHelper::getEqualityArgumentSort(l2.literal())
      );
  check_side_condition(
      "s1 and s2 are of unifyable sorts",
      srt_.isSome())
  auto& srt = srt_.unwrap();

  auto uwa = _shared->unify(s1, s2);
  check_side_condition(
      "uwa(s1,s2) = ⟨σ,Cnst⟩",
      uwa.isSome())
  
  auto sigma = [&](auto t) { return uwa->subs().apply(t, /* varbank */ 0); };
  auto cnst = uwa->computeConstraintLiterals();

  Stack<Literal*> concl(l1.clause()->size() // <- (C \/ s1 ≈ t1 \/ t1  ̸≈ t2)σ
                      + cnst->size()); // <- Cnstσ

  auto L2σ = sigma(l2.literal());
  check_side_condition(
        "(s2 ≈ t2)σ /< (s1 ≈ t1 \\/ C)σ",
        l2.contextLiterals()
          .all([&](auto L) {
             auto Lσ = sigma(L);
             concl.push(Lσ);
             return _shared->notLess(L2σ, Lσ);
           }))

  auto s1σ = sigma(s1);
  auto s2σ = sigma(s2);
  auto t1σ = sigma(t1);
  auto t2σ = sigma(t2);

  check_side_condition( "s1σ /⪯ t1σ", _shared->notLeq(s1σ.untyped(), t1σ))
  check_side_condition( "s2σ /⪯ t2σ", _shared->notLeq(s2σ.untyped(), t1σ))


  auto res = Literal::createEquality(false, t1σ, t2σ, srt);
  concl.push(res);

  // adding Cnst
  concl.loadFromIterator(cnst->iterFifo());

  Inference inf(GeneratingInference1(Kernel::InferenceRule::ALASCA_EQ_FACTORING, l1.clause()));
  auto out = Clause::fromStack(concl, inf);
  DEBUG("out: ", *out);
  return Option<Clause*>(out);
}

// TODO EQ factoring for integers

ClauseIterator EqFactoring::generateClauses(Clause* premise) 
{

  TIME_TRACE("alasca equality factoring generate")
  DEBUG("in: ", *premise)

  auto selected = Lib::make_shared(
      _shared->selectedEqualities(premise, 
                       /* literal */ SelectionCriterion::NOT_LESS, 
                       /* summand */ SelectionCriterion::NOT_LEQ,
                       /* include number vars */ false)
        .filter([](auto& s) { return s.positive(); })
        // .filter([](auto& s) { return !s.isFracNum() || !s.biggerSide().isVar(); })
        .template collect<Stack>());

  auto rest = Lib::make_shared(
      _shared->selectedEqualities(premise, 
                       /* literal */ SelectionCriterion::ANY, 
                       /* summand */ SelectionCriterion::NOT_LEQ,
                       /* include number vars */ false)
        .filter([](auto& s) { return s.positive(); })
        // .filter([](auto& s) { return !s.isFracNum() || !s.biggerSide().isVar(); })
        .template collect<Stack>());

  return pvi(range(0, selected->size())
      .flatMap([=](auto i) {
        return range(0, rest->size())
          .filter([=](auto j) { return (*selected)[i].litIdx() != (*rest)[j].litIdx(); })
          // .filter([=](auto j) { return (*selected)[i].numTraits() == (*rest)[j].numTraits(); })
          .flatMap([=](auto j) {
              auto& max = (*selected)[i];
              auto& other = (*rest)[j];
              return ifElseIter(

                  // both literals are the same. 
                  // we use a symmetry breaking index comparison
                  // TODO we could replace this == by _shared.equivalent
                  max.literal() == other.literal() && other.litIdx() < max.litIdx(), 
                  [&]() { return arrayIter(Stack<Clause*>{}); },

                  // only one is selected (= maximal)
                  [&]() { return concatIters(applyRule(other, max).intoIter()); });
          });
      }));
}


  

#if VDEBUG
void EqFactoring::setTestIndices(Stack<Indexing::Index*> const&) 
{

}
#endif

} // namespace ALASCA 
} // namespace Inferences 
