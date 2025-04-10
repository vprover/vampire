/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef __ALASCA_ORDERING__
#define __ALASCA_ORDERING__

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"

#include "Kernel/ALASCA/Normalization.hpp"
#include "Kernel/ALASCA/SelectionPrimitves.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/TermIterators.hpp"
#include "Lib/DArray.hpp"

#include "Kernel/Ordering.hpp"
#include "Lib/DArray.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/UnificationWithAbstraction.hpp"
#include "Kernel/KBO.hpp"
#include "Kernel/OrderingUtils.hpp"
#include "Lib/Option.hpp"

#define DEBUG_ALASCA_ORD(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }

namespace Kernel {

using namespace Lib;
// TODO namespacing of all alasca stuff

struct AlascaOrderingUtils {

  template<class Iter>
  static auto lexIter(Iter iter) {
    while (iter.hasNext()) {
      auto res = iter.next();
      switch(res) {
        case Ordering::Result::GREATER:
        case Ordering::Result::LESS:
        case Ordering::Result::INCOMPARABLE:
          return res;
        case Ordering::Result::EQUAL:
          break;
      }
    }
    return Ordering::Result::EQUAL;
  }

  template<class... As>
  static auto lex(As... as)
  { return lex(iterItems(as...)); }

  template<class... As>
  static auto lexLazy(As... as)
  { return lexIter(concatIters(iterItems(as).eval()...)); }

  template<class N>
  static Ordering::Result cmpN(N c1, N c2)
  { return c1 < c2 ? Ordering::Result::LESS
         : c2 < c1 ? Ordering::Result::GREATER
                   : Ordering::Result::EQUAL; }

  template<class Q>
  static Ordering::Result cmpQ(Q c1, Q c2)
  { return lexLazy( [&](){ return cmpN(c1 < 0              , c2 < 0              ); }
                  , [&](){ return cmpN(c1.denominator()    , c2.denominator()    ); }
                  , [&](){ return cmpN(c1.numerator().abs(), c2.numerator().abs()); } ); }

  static Ordering::Result cmpQ(IntegerConstantType c1, IntegerConstantType c2)
  { return lexLazy( [&](){ return cmpN(c1 < 0  , c2 < 0  ); }
                  , [&](){ return cmpN(c1.abs(), c2.abs()); } ); }

  static Ordering::Result cmpQ(std::tuple<> c1, std::tuple<> c2)
  { return Ordering::Result::EQUAL; }

  static Ordering::Result compareAtom(Ordering* ord, Literal* const& a1, Literal* const& a2) 
  { return ord->compare(a1, a2); }

  static Ordering::Result compareAtom(Ordering* ord, TypedTermList const& a1, TypedTermList const& a2) 
  { return ord->compare(a1, a2); }

  static Ordering::Result compareAtom(Ordering* ord, AlascaAtom const& a1, AlascaAtom const& a2) {
    return lexLazy(
      [&]() { return cmpN(a1.is<Literal*>(), a2.is<Literal*>()); },
      [&]() { 
        return a1.apply([&](auto a1) { return compareAtom(ord, a1, a2.template unwrap<decltype(a1)>()); });
      }
    );
  }

  static Ordering::Result compareAtom(Ordering* ord, SelectedAtom const& a1, SelectedAtom const& a2) {
    return lexLazy(
        [&]() { return compareAtom(ord, a1.selectedAtom(), a2.selectedAtom()); },
        [&]() { return a1 == a2 ? Ordering::Result::EQUAL : Ordering::Result::INCOMPARABLE; }
        );
  }

  template<class Selected>
  static bool atomMaxAfterUnif(Ordering* ord, Selected const& atom, SelectionCriterion sel, AbstractingUnifier& unif, unsigned varBank) {

    // TODO 1.2 we must actually apply the unifier before calling `iter` I think (think of top level vars)
    //         or is it find because they will always be shielded thus none of the atoms created by them can get maximal anyways ...?

    if (sel == SelectionCriterion::ANY) { return true; }

    ASS_REP(sel == SelectionCriterion::NOT_LESS || sel == SelectionCriterion::NOT_LEQ, sel);
    auto sigma = [&](auto t) {
      return t.applyCo([&](auto termOrLit) { return unif.subs().apply(termOrLit, varBank); });
    }; 
    auto sσ = sigma(atom.selectedAtom());

    return SelectedAtom::iter(atom.clause())
                  .filter([&](auto& t) { return t != SelectedAtom(atom); })
                  .all([&](auto t) { 
                      auto tσ = sigma(t.selectedAtom());
                      auto cmp = compareAtom(ord, sσ, tσ);
                      // DBG(sσ, " ", cmp, " ", tσ)
                      return sel == SelectionCriterion::NOT_LEQ  ? OrderingUtils::notLeq(cmp)
                           : sel == SelectionCriterion::NOT_LESS ? OrderingUtils::notLess(cmp)
                           : assertionViolation<bool>();
                      });
  }

  template<class Selected>
  static bool litMaxAfterUnif(Ordering* ord, Selected const& atom, SelectionCriterion sel, AbstractingUnifier& unif, unsigned varBank) {

    if (sel == SelectionCriterion::ANY) { return true; }
    ASS_REP(sel == SelectionCriterion::NOT_LESS || sel == SelectionCriterion::NOT_LEQ, sel);

    auto sigma = [&](auto x) { return unif.subs().apply(x, varBank); }; 
    auto L1σ = sigma(atom.literal());

    return atom.clause()->iterLits()
          .dropNth(atom.litIdx())
          .all([&](auto L2) { 
              auto L2σ = sigma(L2);
              auto cmp = ord->compare(L1σ, L2σ);
              return sel == SelectionCriterion::NOT_LEQ  ? OrderingUtils::notLeq(cmp)
                   : sel == SelectionCriterion::NOT_LESS ? OrderingUtils::notLess(cmp)
                   : assertionViolation<bool>();
              });
  }


};


template<class F>
bool isFloor(F f) {
  return forAnyNumTraits([&](auto n) { return n.isFloor(f); });
}

template<class Ord>
struct SkelOrd 
  : public Ordering
{
  Ord _ord;
  mutable Map<Term*, Option<TermList>> _skeletons;

  SkelOrd(Ord ord) : _ord(std::move(ord)) {}
  SkelOrd(Problem& prb, const Options& opt) : SkelOrd(Ord(prb, opt)) {}

  void show(std::ostream& out) const final override { return _ord.show(out); }
  virtual bool isAlascaLiteralOrdering() const final override { return true; }

  template<class NumTraits>
  Ordering::Result cmpSameSkeleton(AlascaMonom<NumTraits> const& t0, AlascaMonom<NumTraits> const& t1) const
  {
    auto normAtom = [](auto t) { return AnyAlascaTerm::normalize(TypedTermList(t.atom(), NumTraits::sort())); };
    return AlascaOrderingUtils::lexLazy(
        [&](){ return cmpSameSkeleton(normAtom(t1), normAtom(t1)); },
        [&](){ return AlascaOrderingUtils::cmpQ(t0.numeral(), t1.numeral()); }
    );
  }


  template<class NumTraits>
  Ordering::Result cmpSameSkeleton(AlascaTermItp<NumTraits> const& t0, AlascaTermItp<NumTraits> const& t1) const
  {
    ASS_REP(t1 != t0, "case should be handled earlier")

    if (t0.nSummands() == 1 && t1.nSummands() == 1) {
      return cmpSameSkeleton(t0.summandAt(0), t1.summandAt(0));
    } else {
      auto set = [](auto p) { return p.iterSummands().template collect<MultiSet>(); };
      return OrderingUtils::mulExt(set(t0), set(t1), [&](auto& l, auto& r) { return compare(l, r); });
    }
  }

  template<class NumTraits>
  Ordering::Result cmpSameSkeleton(AlascaTermItp<NumTraits> const& t0, AnyAlascaTerm const& t1) const
  { return cmpSameSkeleton(t0, t1.asSum<NumTraits>().unwrap()); }

  Ordering::Result cmpSameSkeleton(TypedTermList t0, TypedTermList t1) const
  { return cmpSameSkeleton(InequalityNormalizer::normalize(t0), InequalityNormalizer::normalize(t1)); }

  Ordering::Result cmpSameSkeleton(AlascaTermItpAny const& t0, AnyAlascaTerm const& t1) const
  { return t0.apply([&](auto& t0) { return cmpSameSkeleton(t0, t1); }); }

  static Option<AlascaTermItpAny> asNonTrivialSum(AnyAlascaTerm const& t) {
    return t.asSum()
      .andThen([](auto x) -> Option<AlascaTermItpAny> {
        if(x.apply([](auto& x) {
          return x.nSummands() == 1 && x.monomAt(0).numeral() == 1;
        })) {
          return {};
        } else {
          return some(x);
        }
    });
  }

  Ordering::Result cmpSameSkeleton(AnyAlascaTerm const& t0, AnyAlascaTerm const& t1) const {
    if (t0 == t1) return Ordering::Result::EQUAL;
    // TODO make this nicer

    if (auto p0 = asNonTrivialSum(t0)) {
      return cmpSameSkeleton(*p0, t1);
    } else if (auto p1 = asNonTrivialSum(t1)) {
      return Ordering::reverse(cmpSameSkeleton(*p1, t0));

    } else if (t0.toTerm().isVar() || t1.toTerm().isVar()) {
      return Ordering::Result::INCOMPARABLE;

    } else {
      ASS(t0.toTerm().isTerm() && t1.toTerm().isTerm())
      auto f0 = t0.toTerm().term();
      auto f1 = t1.toTerm().term();
      auto sort = SortHelper::getResultSort(f0);
      ASS_EQ(sort, SortHelper::getResultSort(f1))
      auto floor0 = isFloor(f0->functor());
      auto floor1 = isFloor(f1->functor());
      if (floor0 && floor1) {
        return cmpSameSkeleton(TypedTermList(f0->termArg(0), sort), TypedTermList(f1->termArg(0), sort));
      } else if (!floor0 && floor1) {
        return Ordering::Result::LESS;
      } else if (floor0 && !floor1) {
        return Ordering::Result::GREATER;
      } else {
        ASS(!floor0 && !floor1)
        return AlascaOrderingUtils::lexIter(anyArgIterTyped(f0).zip(anyArgIterTyped(f1))
            .map([&](auto pair) { return cmpSameSkeleton(pair.first, pair.second); }));
      }
    }
  }


  static MultiSet<TermList> set(unsigned f, TermList t) {
    MultiSet<TermList> out;
    RStack<TermList> todo;
    RStack<TermList> set;
    todo->push(t);
    while (todo->isNonEmpty()) {
      auto t = todo->pop();
      if (t.isTerm() && t.term()->functor() == f) {
        set->push(t.term()->termArg(0));
        set->push(t.term()->termArg(1));
      } else {
        set->push(t);
      }
    }
    return MultiSet<TermList>::fromIterator(arrayIter(std::move(set)));
  }

  Ordering::Result cmpSameSkeleton(TermList t0, TermList t1) const {
    if (t0 == t1) return Ordering::Result::EQUAL;
    // TODO make this nicer

    Option<Ordering::Result> resultItp = forAnyNumTraits([&](auto n) -> Option<Ordering::Result> {
        auto isZero = [](auto option) { return option.isSome() && option.unwrap() == 0; };
        if (asig(n).isAdd(t0) || asig(n).isAdd(t1)) {
          auto add = n.addF();
          return some(OrderingUtils::mulExt(set(add, t0), set(add, t1), 
                [&](auto& l, auto& r) { return compare(l, r); }));

        } else if (isZero(asig(n).tryNumeral(t0))) {
          ASS(!isZero(asig(n).tryNumeral(t0)))
          /* cmpSameSkeleton(0, r) = LESS */
          return some(Ordering::Result::LESS);

        } else if (isZero(asig(n).tryNumeral(t1))) {
          /* cmpSameSkeleton(  l, 0) = GREATER */
          return some(Ordering::Result::GREATER);

        } else if (isZero(asig(n).tryLinMul(t0)) &&  isZero(asig(n).tryLinMul(t1))) {
          /* cmpSameSkeleton(0 l, 0 r) = cmpSameSkeleton(l,r) */
          return some(cmpSameSkeleton(t0.term()->termArg(0), t1.term()->termArg(0)));

        } else if (isZero(asig(n).tryLinMul(t0))) {
          /* cmpSameSkeleton(0 l,   r) = LESS */
          return some(Ordering::Result::LESS);

        } else if (isZero(asig(n).tryLinMul(t1))) {
          /* cmpSameSkeleton(  l, 0 r) = GREATER */
          return some(Ordering::Result::GREATER);


        } else if (asig(n).tryNumeral(t0).isSome() &&  asig(n).tryNumeral(t1).isSome()) {
          auto j = *asig(n).tryNumeral(t0);
          auto k = *asig(n).tryNumeral(t1);
          /* cmpSameSkeleton(j, k) = cmpQ(j, k) */
          return some(AlascaOrderingUtils::cmpQ(j, k));

        } else if (asig(n).tryNumeral(t0).isSome()) {
          /* cmpSameSkeleton(j, r) = LESS */
          return some(Ordering::Result::LESS);

        } else if (asig(n).tryNumeral(t1).isSome()) {
          /* cmpSameSkeleton(  l, k) = GREATER */
          return some(Ordering::Result::GREATER);

        } else if (asig(n).tryLinMul(t0).isSome() &&  asig(n).tryLinMul(t1).isSome()) {
          auto j = *asig(n).tryLinMul(t0);
          auto k = *asig(n).tryLinMul(t1);
          /* cmpSameSkeleton(j l, k r) = cmpSameSkeleton(l,r) ⊕ cmpQ(j, k) */
          return some(AlascaOrderingUtils::lexLazy(
              [&](){ return cmpSameSkeleton(t0.term()->termArg(0), t1.term()->termArg(0)); },
              [&](){ return AlascaOrderingUtils::cmpQ(j, k); }));

        } else if (asig(n).tryLinMul(t0).isSome()) {
          /* cmpSameSkeleton(j l,   r) = GREATER */
          return some(Ordering::Result::GREATER);

        } else if (asig(n).tryLinMul(t1).isSome()) {
          /* cmpSameSkeleton(  l, k r) = LESS */
          return some(Ordering::Result::LESS);

        } else if (asig(n).isFloor(t0) && asig(n).isFloor(t1)) {
          /* cmpSameSkeleton(⌊l⌋, ⌊r⌋) = cmpSameSkeleton(l,r) */
          return some(cmpSameSkeleton(t0.term()->termArg(0), t1.term()->termArg(0)));

        } else if ( asig(n).isFloor(t0) && !asig(n).isFloor(t1)) {
          /* cmpSameSkeleton(⌊l⌋,  r ) = GREATER */
          return some(Ordering::Result::GREATER);

        } else if (!asig(n).isFloor(t0) &&  asig(n).isFloor(t1)) {
          /* cmpSameSkeleton( l , ⌊r⌋) = LESS */
          return some(Ordering::Result::LESS);

        } else {
          return {};
        }
    });


    if (resultItp) { 
      return *resultItp; 
    } else {
      ASS(t0.isTerm() && t1.isTerm() && t0.term()->functor() == t1.term()->functor())
      return AlascaOrderingUtils::lexIter(anyArgIter(t0.term()).zip(anyArgIter(t1.term()))
          .map([&](auto pair) { return cmpSameSkeleton(pair.first, pair.second); }));
    }
  }

  // Option<TermList> computeSkeletonItp(AlascaTermItpAny const& t) const
  // { return t.apply([&](auto& t) { return computeSkeletonItp(t); }); }
  //
  // template<class Iter>
  // Option<RStack<TermList>> trySkeleton(Iter iter) const {
  //   auto out = RStack<TermList>();
  //   for (auto x : iter) {
  //     if (auto s = skeleton(x)) {
  //       out->push(*s);
  //     } else {
  //       return {};
  //     }
  //   }
  //   return some(std::move(out));
  // }

#define DEBUG_RESULT(lvl, msg, ...)                                                       \
     auto impl = [&]() { __VA_ARGS__ };                                                   \
     DEBUG_ALASCA_ORD(lvl, msg, "???");                                                   \
     auto res = impl();                                                                   \
     DEBUG_ALASCA_ORD(lvl, msg, res);                                                     \
     return res;                                                                          \

#define DEBUG_FN_RESULT(lvl, msg, ...)                                                    \
  { DEBUG_RESULT(lvl, msg, __VA_ARGS__) }

  // template<class NumTraits>
  // Option<TermList> computeSkeletonItp(AlascaTermItp<NumTraits> const& t) const
  // DEBUG_FN_RESULT(2, Output::cat("computeSkeletonItp(", t, ") = "),
  // {
  //   if (t.nSummands() == 0) {
  //     return some(NumTraits::one());
  //   }
  //   if (auto summands = trySkeleton(t.iterSummands())) {
  //     auto maxIter = OrderingUtils::maxElems(summands->size(),
  //         [&](auto t0, auto t1) { return _ord.compare((*summands)[t0], (*summands)[t1]);  },
  //         [&](auto i) { return (*summands)[i]; },
  //         SelectionCriterion::NOT_LESS,
  //         /* dedup */ true);
  //     if (!maxIter.hasNext()) {
  //       return Option<TermList>{};
  //     } else {
  //       auto max = maxIter.next();
  //       if (maxIter.hasNext()) {
  //         // no unique max
  //         // TODO theory (?)
  //         return Option<TermList>{};
  //       } else {
  //         return some((*summands)[max]);
  //       }
  //     }
  //   } else {
  //     return Option<TermList>{};
  //   }
  // }
  // )

  // Option<TermList> computeSkeletonUF(Term* t) const {
  //   return trySkeleton(termArgIterTyped(t))
  //     .map([&](auto args) {
  //         if (isFloor(t->functor())) {
  //           return args[0];
  //         } else {
  //           return TermList(Term::createFromIter(
  //                 t->functor(),
  //                 concatIters(
  //                   typeArgIter(t),
  //                   arrayIter(*args).cloned()
  //                   )));
  //         }
  //     });
  // }

  Option<TermList> computeSkeleton(Term* t) const
  {
    Option<Option<TermList>> interpretedResult = forAnyNumTraits([&](auto n) {
        return optionIfThenElse(
              [&]() { return asig(n).ifFloor(t, [&](auto t) { return skeleton(t); }); }
            , [&]() { return asig(n).ifLinMul(t, [&](auto k, auto t) { return skeleton(t); }); }
            , [&]() { return asig(n).tryNumeral(t).map([&](auto k) { return some(asig(n).one()); }); }
            , [&]() { return n.ifAdd(t, [this](auto t0, auto t1) -> Option<TermList> { 
                auto s0 = skeleton(t0);
                auto s1 = skeleton(t1);
                if (s0.isSome() && s1.isSome()) {
                  switch (_ord.compare(*s0, *s1)) {
                    case Ordering::Result::EQUAL: return some(*s0);
                    case Ordering::Result::GREATER: return some(*s0);
                    case Ordering::Result::LESS: return some(*s1);
                    case Ordering::Result::INCOMPARABLE: return {};
                  }
                } else {
                  return {};
                }
              }); 
            });
    });
    if (interpretedResult) {
      return *interpretedResult;
    } else {
      RStack<TermList> args;
      args->loadFromIterator(typeArgIter(t));
      for (auto x : termArgIter(t)) {
        if (auto sx = skeleton(x)) {
          args->push(*sx);
        } else {
          return {};
        }
      }
      return some(TermList(Term::create(t, args->begin())));
    }
  }

  // TODO atoms of equalities normalizing!!!

  Option<TermList> skeleton(TermList t) const
  {
    if (t.isVar()) {
      return some(t);
    } else if (auto r = _skeletons.tryGet(t.term())) {
      return *r;
    } else {
      auto res = computeSkeleton(t.term());
      _skeletons.insert(t.term(), res);
      return res;
    }
  }

  template<class NumTraits>
  Option<TermList> skeleton(AlascaMonom<NumTraits> const& t) const
  { return skeleton(TypedTermList(t.atom(), NumTraits::sort())); }

  Option<TermList> skeleton(TypedTermList t) const
  { return skeleton(InequalityNormalizer::normalize(t)); }

  // Ordering::Result compare(AnyAlascaTerm const& t0, AnyAlascaTerm const& t1) const
  // { return genericCompare(t0, t1); }
  //
  // template<class NumTraits>
  // Ordering::Result compare(AlascaMonom<NumTraits> const& t0, AlascaMonom<NumTraits> const& t1) const
  // { return genericCompare(t0, t1); }

  // template<class Term>
  // Ordering::Result genericCompare(Term const& t0, Term const& t1) const
  // {
  //   if (t0 == t1) return Ordering::Result::EQUAL;
  //   auto s0 = skeleton(t0);
  //   auto s1 = skeleton(t1);
  //   DEBUG_ALASCA_ORD(1, "skel(", t0, ") = ", s0)
  //   DEBUG_ALASCA_ORD(1, "skel(", t1, ") = ", s1)
  //   if (s0.isSome() && s1.isSome()) {
  //     return AlascaOrderingUtils::lexLazy(
  //         [&](){ return _ord.compare(*s0, *s1); },
  //         [&](){ return cmpSameSkeleton(t0, t1); });
  //   } else {
  //     //TODO
  //     return Ordering::Result::INCOMPARABLE;
  //   }
  // }

  int predPrec(unsigned pred) const { return _ord.predicatePrecedence(pred); }
  Ordering::Result cmpPredPrec(unsigned p0, unsigned p1) const { return AlascaOrderingUtils::cmpN(predPrec(p0), predPrec(p1)); }

  Ordering::Result compare(TermList t1, TermList t2) const final override
  DEBUG_FN_RESULT(2, Output::cat("comapre", std::tie(t1, t2), " = "),
  {
    DEBUG_CODE(if (t1.isTerm() && t2.isTerm()) { ASS_EQ(t1.term()->isSort(), t2.term()->isSort()) })

    if ((t1.isTerm() && t1.term()->isSort())
      ||(t2.isTerm() && t2.term()->isSort())) {
      return _ord.compare(t1, t2);

    } else if (t1.isVar() && t2.isVar()) {
      return t1 == t2 ? Ordering::Result::EQUAL : Ordering::Result::INCOMPARABLE;

    } else if (t1.isVar() && !t2.isVar()) {
      return t2.containsSubterm(t1) ? Ordering::Result::LESS : Ordering::Result::INCOMPARABLE;

    } else if (t2.isVar() && !t1.isVar()) {
      return t1.containsSubterm(t2) ? Ordering::Result::GREATER : Ordering::Result::INCOMPARABLE;

    } else {
      ASS(t1.isTerm() && t2.isTerm())

      if (t1 == t2) return Ordering::Result::EQUAL;
      auto s1 = skeleton(t1);
      auto s2 = skeleton(t2);
      DEBUG_ALASCA_ORD(1, "skel(", t1, ") = ", s1)
      DEBUG_ALASCA_ORD(1, "skel(", t2, ") = ", s2)
      if (s1.isSome() && s2.isSome()) {
        return AlascaOrderingUtils::lexLazy(
            [&](){ return _ord.compare(*s1, *s2); },
            [&](){ return cmpSameSkeleton(t1, t2); });
      } else {
        //TODO
        return Ordering::Result::INCOMPARABLE;
      }
    }
  }
  )

  using AnyNumeral = Coproduct<IntegerConstantType, RationalConstantType, RealConstantType>;
  using Atom = std::tuple<TermList, unsigned , Option<AnyNumeral>>;

  static unsigned lvl(AlascaPredicate p) {
    switch(p) {
      case AlascaPredicate::EQ: return 0;
      case AlascaPredicate::GREATER:
      case AlascaPredicate::GREATER_EQ:
                               return 1;
      case AlascaPredicate::NEQ:
                               return 2;
    } ASSERTION_VIOLATION
  }

  template<class NumTraits>
  static void atoms(NumTraits n, TermList t, AlascaPredicate p, Stack<Atom>& out) {
    if (asig(n).isAdd(t)) {
      atoms(n, t.term()->termArg(0), p, out);
      atoms(n, t.term()->termArg(1), p, out);

    } else if (auto k = asig(n).tryNumeral(t)) {
      out.push(std::make_tuple(n.one(), lvl(p), some(AnyNumeral(*k))));

    } else if (auto k = asig(n).tryLinMul(t)) {
      out.push(std::make_tuple(t.term()->termArg(0), lvl(p), some(AnyNumeral(*k))));

    } else {
      out.push(std::make_tuple(t, lvl(p), Option<AnyNumeral>()));
    }
  }


  template<class NumTraits>
  static MultiSet<Atom> atoms(NumTraits n, TermList t, AlascaPredicate p) {
    RStack<Atom> out;
    atoms(n, t, p, *out);
    return MultiSet<Atom>::fromIterator(arrayIter(std::move(out)));
  }

  Option<MultiSet<Atom>> atoms(Literal* l) const {
    auto itpRes = forAnyNumTraits([&](auto n) -> Option<MultiSet<Atom>> {

#define TRY_INEQ(sym, check) \
        if (check(l)) { \
          ASS_EQ(l->termArg(1), n.zero()) \
          return some(atoms(n, l->termArg(0), sym)); \
        } \

#define TRY_EQ(sym, check) \
        if (check(l)) { \
          auto t = l->termArg(1) == n.zero() ? l->termArg(0) : l->termArg(1); \
          return some(atoms(n, t, sym)); \
        } \

        TRY_EQ(AlascaPredicate::EQ        , [&](auto l) { return n.isPosEq  (l); });
        TRY_EQ(AlascaPredicate::NEQ       , [&](auto l) { return n.isNegEq  (l); });
        TRY_INEQ(AlascaPredicate::GREATER   , [&](auto l) { return n.isGreater(l); });
        TRY_INEQ(AlascaPredicate::GREATER_EQ, [&](auto l) { return n.isGeq    (l); });
        return {};

#undef TRY_INEQ
#undef TRY_EQ
    });
    if (itpRes) return itpRes;
    else if (l->isEquality()) {
      auto sym = l->isPositive() ? AlascaPredicate::EQ : AlascaPredicate::NEQ;
      return some(iterItems(0, 1)
        .map([&](auto i) { return std::make_tuple(l->termArg(i), lvl(sym), Option<AnyNumeral>()); })
        .template collect<MultiSet>());
    } else {
      return {};
    }
  }

  Ordering::Result cmpPrec(Literal* l0, Literal* l1) const
  {
    if (l0->isEquality() && l1->isEquality()) {
      return _ord.compare(l0->eqArgSort(), l1->eqArgSort());
    } else {
      return cmpPredPrec(l0->functor(), l1->functor());
    }
  }

  Ordering::Result cmpPrecUninterpreted(Literal* l0, Literal* l1) const {
    ASS(!l0->isEquality() && !l1->isEquality())
    return cmpPredPrec(l0->functor(), l1->functor());
  }

  static Ordering::Result cmpPolarity(bool p0, bool p1) {
    return  p0 ==  p1 ? Ordering::Result::EQUAL
         : !p0 &&  p1 ? Ordering::Result::GREATER
         :  p0 && !p1 ? Ordering::Result::LESS
         : assertionViolation<Ordering::Result>();
  }


  static Ordering::Result cmpPolarity(Literal* l0, Literal* l1)
  { return cmpPolarity(l0->isPositive(), l1->isPositive()); }

  Result compareUninterpreted(Literal* l1, Literal* l2) const {
    if (l1->functor() == l2->functor()) {
      // TODO think about the polymorphic case
      return AlascaOrderingUtils::lexIter(concatIters(
            anyArgIter(l1).zip(anyArgIter(l2))
              .map([&](auto pair) { return compare(pair.first, pair.second); }),
            iterItems([&](){ return cmpPolarity(l1, l2); }).eval()
      ));
    } else {
      return cmpPrecUninterpreted(l1, l2);
    }
  }

  Ordering::Result cmpAtom(Atom a1, Atom a2) const {
    return AlascaOrderingUtils::lexLazy(
            [&](){ return compare(std::get<0>(a1), std::get<0>(a2)); },
            [&](){ return AlascaOrderingUtils::cmpN(std::get<1>(a1), std::get<1>(a2)); },
            [&](){
              auto& n1 = std::get<2>(a1);
              auto& n2 = std::get<2>(a2);
              if (!n1.isSome() &&  n2.isSome()) {
                return Ordering::Result::LESS;

              } else if ( n1.isSome() && !n2.isSome()) {
                return Ordering::Result::GREATER;

              } else if (n1.isSome() && n2.isSome()) {
                return n1->applyWithIdx([&](auto& n1, auto N) { 
                    return AlascaOrderingUtils::cmpQ(n1, n2->unwrap<N.value>()); });
              } else {
                ASS(!n1.isSome() && !n2.isSome())
                return Ordering::Result::EQUAL;
              }
            }
          );
  }


  Result compare(Literal* l1, Literal* l2) const final override {
    auto atoms1 = atoms(l1);
    auto atoms2 = atoms(l2);
    if (!atoms1.isSome() && atoms2.isSome()) {
      return Ordering::GREATER;

    } else if (atoms1.isSome() && !atoms2.isSome()) {
      return Ordering::LESS;

    } else if (atoms1.isSome() && atoms2.isSome()) {

      return AlascaOrderingUtils::lexLazy(
            [&](){ return OrderingUtils::mulExt(*atoms1, *atoms2, [&](auto l, auto r) { return cmpAtom(l, r); }); },
            [&](){ return cmpPrec(l1, l2); }
            );

    } else {
      ASS(atoms1.isNone() && atoms2.isNone())
      return compareUninterpreted(l1,l2);
    }
  }


};


template<class TermOrdering>
class LiteralOrdering
  : public Ordering
{
  TermOrdering _termOrdering;

  Ordering::Result cmpPrecUninterpreted(Literal* l0, Literal* l1) const {
    ASS(!l0->isEquality() && !l1->isEquality())
    return _termOrdering.cmpPredPrec(l0->functor(), l1->functor());
  }

  Ordering::Result cmpPrec(Literal* l0, Literal* l1) const
  {
    if (l0->isEquality() && l1->isEquality()) {
      return _termOrdering.compare(l0->eqArgSort(), l1->eqArgSort());
    } else {
      return _termOrdering.cmpPredPrec(l0->functor(), l1->functor());
    }
  }

  static Ordering::Result cmpPolarity(Literal* l0, Literal* l1)
  { return cmpPolarity(l0->isPositive(), l1->isPositive()); }

  static Ordering::Result cmpPolarity(bool p0, bool p1) {
    return  p0 ==  p1 ? Ordering::Result::EQUAL
         : !p0 &&  p1 ? Ordering::Result::GREATER
         :  p0 && !p1 ? Ordering::Result::LESS
         : assertionViolation<Ordering::Result>();
  }

  using AnyNumeral = Coproduct<IntegerConstantType, RationalConstantType, RealConstantType, std::tuple<>>;
  //                                                                      No Numeral <------^^^^^^^^^^^^

  using Atom = std::tuple<AnyAlascaTerm, unsigned , AnyNumeral>;

  unsigned lvl(AlascaPredicate p) const {
    switch(p) {
      case AlascaPredicate::EQ: return 0;
      case AlascaPredicate::GREATER:
      case AlascaPredicate::GREATER_EQ:
                               return 1;
      case AlascaPredicate::NEQ:
                               return 2;
    } ASSERTION_VIOLATION
  }

  MultiSet<Atom> atoms(AlascaLiteralItpAny const& l) const
  { return l.apply([&](auto l) { return atoms(l); }); }

  template<class NumTraits>
  MultiSet<Atom> atoms(AlascaLiteralItp<NumTraits> const& l1) const {
    return l1.term().iterSummands()
      .map([&](auto monom) { return std::make_tuple(
            AnyAlascaTerm::normalize(TypedTermList(monom.atom(), NumTraits::sort())),
            lvl(l1.symbol()),
            AnyNumeral(monom.numeral())); })
      .template collect<MultiSet>();
  }

  Option<MultiSet<Atom>> atoms(Literal* l) const {
    if (auto alasca = InequalityNormalizer::tryNormalizeInterpreted(l)) {
      return some(atoms(*alasca));
    } else if (l->isEquality()) {
      auto sym = l->isPositive() ? AlascaPredicate::EQ : AlascaPredicate::NEQ;
      return some(termArgIterTyped(l)
        .map([&](auto t) { return std::make_tuple(InequalityNormalizer::normalize(t), lvl(sym), AnyNumeral(std::make_tuple())); })
        .template collect<MultiSet>());
    } else {
      return {};
    }
  }

  Ordering::Result cmpAtom(Atom a1, Atom a2) const {
    return AlascaOrderingUtils::lexLazy(
            [&](){ return _termOrdering.compare(std::get<0>(a1).toTerm(), std::get<0>(a2).toTerm()); },
            [&](){ return AlascaOrderingUtils::cmpN(std::get<1>(a1), std::get<1>(a2)); },
            [&](){
                  auto& n1 = std::get<2>(a1);
                  auto& n2 = std::get<2>(a2);
                  ASS_EQ(n1.tag(), n2.tag())
                  return n1.applyWithIdx([&](auto& n1, auto N) { return AlascaOrderingUtils::cmpQ(n1, n2.unwrap<N.value>()); });
            }
          );
  }

public:
  USE_ALLOCATOR(LiteralOrdering);

  LiteralOrdering(LiteralOrdering&& kbo) = default;
  LiteralOrdering& operator=(LiteralOrdering&& kbo) = default;
  LiteralOrdering(TermOrdering inner)
    : _termOrdering(std::move(inner)) { }
  LiteralOrdering(Problem& prb, const Options& opt)
    : LiteralOrdering(TermOrdering(prb, opt)) { }

  virtual ~LiteralOrdering() {}

  virtual bool isAlascaLiteralOrdering() const final override { return true; }

  Result compare(Literal* l1, Literal* l2) const final override {
    auto atoms1 = atoms(l1);
    auto atoms2 = atoms(l2);
    if (!atoms1.isSome() && atoms2.isSome()) {
      return Ordering::GREATER;

    } else if (atoms1.isSome() && !atoms2.isSome()) {
      return Ordering::LESS;

    } else if (atoms1.isSome() && atoms2.isSome()) {

      return AlascaOrderingUtils::lexLazy(
            [&](){ return OrderingUtils::mulExt(*atoms1, *atoms2, [&](auto l, auto r) { return cmpAtom(l, r); }); },
            [&](){ return cmpPrec(l1, l2); }
            );

    } else {
      ASS(atoms1.isNone() && atoms2.isNone())
      return compareUninterpreted(l1,l2);
    }
  }

  Result compare(TermList t1, TermList t2) const final override
  { return _termOrdering.compare(t1, t2); }

  void show(std::ostream& out) const final override
  { _termOrdering.show(out); }

private:

  Result compareUninterpreted(Literal* l1, Literal* l2) const {
    if (l1->functor() == l2->functor()) {
      // TODO think about the polymorphic case
      return AlascaOrderingUtils::lexIter(concatIters(
            anyArgIter(l1).zip(anyArgIter(l2))
              .map([&](auto pair) { return _termOrdering.compare(pair.first, pair.second); }),
            iterItems([&](){ return cmpPolarity(l1, l2); }).eval()
      ));
    } else {
      return cmpPrecUninterpreted(l1, l2);
    }
  }
};

using LAKBO = SkelOrd<KBO>;

template<class Inner>
SkelOrd(Inner) -> SkelOrd<Inner>;

template<class Inner>
LiteralOrdering(Inner) -> LiteralOrdering<Inner>;


#undef DEBUG_FN_RESULT
#undef DEBUG_RESULT

} // namespace Kernel

#endif // __ALASCA_ORDERING__
