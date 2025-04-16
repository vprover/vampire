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

  static Ordering::Result cmpSgn(Sign c1, Sign c2)
  { 
    auto toN = [](Sign s) {
      switch (s) {
        case Sign::Zero: return 0;
        case Sign::Pos: return 1;
        case Sign::Neg: return 2;
      }
    };
    return cmpN(toN(c1), toN(c2)); 
  }

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

  template<class Selected, class Logger, class Iter>
  static bool atomMaxAfterUnif(Ordering* ord, Selected const& atom, SelectionCriterion sel, AbstractingUnifier& unif, unsigned varBank, Logger logger, Iter iter) {

    // TODO 1.2 we must actually apply the unifier before calling `iter` I think (think of top level vars)
    //         or is it find because they will always be shielded thus none of the atoms created by them can get maximal anyways ...?

    if (sel == SelectionCriterion::ANY) { return true; }

    ASS_REP(sel == SelectionCriterion::NOT_LESS || sel == SelectionCriterion::NOT_LEQ, sel);
    auto sigma = [&](auto t) {
      return t.applyCo([&](auto termOrLit) { return unif.subs().apply(termOrLit, varBank); });
    }; 
    auto sσ = sigma(atom.selectedAtom());

    return iterTraits(std::move(iter))
                  .filter([&](auto& t) { return t != SelectedAtom(atom); })
                  // .filter([&](auto& t) { return !isSame(t, atom); })
                  .all([&](auto t) { 
                      auto tσ = sigma(t.selectedAtom());
                      auto cmp = compareAtom(ord, sσ, tσ);
                      auto r = sel == SelectionCriterion::NOT_LEQ  ? OrderingUtils::notLeq(cmp)
                             : sel == SelectionCriterion::NOT_LESS ? OrderingUtils::notLess(cmp)
                             : assertionViolation<bool>();
                      if (!r) {
                        logger(Output::cat(sσ, " ", cmp, " ", tσ));
                      }
                      return r;
                  });
  }


  template<class Selected, class Logger>
  static bool atomLocalMaxAfterUnif(Ordering* ord, Selected const& atom, SelectionCriterion sel, AbstractingUnifier& unif, unsigned varBank, Logger logger) {
    return atomMaxAfterUnif(ord, atom, sel, unif, varBank, std::move(logger), 
        SelectedAtom::iter(ord, __SelectedLiteral(atom.clause(), atom.litIdx(), atom.isBGSelected()), sel));
  }

  template<class Selected, class Logger>
  static bool atomGlobalMaxAfterUnif(Ordering* ord, Selected const& atom, SelectionCriterion sel, AbstractingUnifier& unif, unsigned varBank, Logger logger) {
    return atomMaxAfterUnif(ord, atom, sel, unif, varBank, std::move(logger), 
      SelectedAtom::iter(atom.clause(), /*bgSelected=*/true));
  }

  template<class Selected, class Logger>
  static bool litMaxAfterUnif(Ordering* ord, Selected const& atom, SelectionCriterion sel, AbstractingUnifier& unif, unsigned varBank, Logger logger) {

    if (sel == SelectionCriterion::ANY) { return true; }
    ASS_REP(sel == SelectionCriterion::NOT_LESS || sel == SelectionCriterion::NOT_LEQ, sel);

    auto sigma = [&](auto x) { return unif.subs().apply(x, varBank); }; 
    auto L1σ = sigma(atom.literal());

    return atom.clause()->iterLits()
          .dropNth(atom.litIdx())
          .all([&](auto L2) { 
              auto L2σ = sigma(L2);
              auto cmp = ord->compare(L1σ, L2σ);
              auto r = sel == SelectionCriterion::NOT_LEQ  ? OrderingUtils::notLeq(cmp)
                     : sel == SelectionCriterion::NOT_LESS ? OrderingUtils::notLess(cmp)
             : assertionViolation<bool>();
              if (!r) {
                logger(Output::cat(*L1σ, " ", cmp, " ", *L2σ));
              }
              return r;
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
  static MultiSet<TermList> gen_set(NumTraits n, TermList t, bool set1) {
    auto f = n.addF();
    MultiSet<TermList> out;
    RStack<TermList> todo;
    RStack<TermList> set;
    todo->push(t);
    while (todo->isNonEmpty()) {
      auto t = todo->pop();
      if (t.isTerm() && t.term()->functor() == f) {
        todo->push(t.term()->termArg(0));
        todo->push(t.term()->termArg(1));
      } else if (set1 && asig(n).isNumeral(t)) {
        set->push(NumTraits::one());
      } else if (set1 && asig(n).isLinMul(t)) {
        todo->push(t.term()->termArg(0));
      } else {
        set->push(t);
      }
    }
    return MultiSet<TermList>::fromIterator(arrayIter(std::move(set)));
  }

  template<class NumTraits>
  static MultiSet<TermList> set1(NumTraits n, TermList t) 
  { return gen_set(n, t, /* set1 */ true); }

  template<class NumTraits>
  static MultiSet<TermList> set2(NumTraits n, TermList t) 
  { return gen_set(n, t, /* set1 */ false); }


  Ordering::Result cmpSameSkeleton(TermList t0, TermList t1) const {
    if (t0 == t1) return Ordering::Result::EQUAL;
    // TODO make this nicer

    Option<Ordering::Result> resultItp = forAnyNumTraits([&](auto n) -> Option<Ordering::Result> {
        auto isZero = [](auto option) { return option.isSome() && option.unwrap() == 0; };
        if (asig(n).isAdd(t0) || asig(n).isAdd(t1)) {
          auto mulExt = [&](auto l, auto r) { return OrderingUtils::mulExt(l, r, 
                [&](auto& l, auto& r) { return this->compare(l, r); }); };
          return some(AlascaOrderingUtils::lexLazy(
              [&]() { return mulExt(set1(n, t0), set1(n, t1)); },
              [&]() { return mulExt(set2(n, t0), set2(n, t1)); }));

        } else if (isZero(asig(n).tryNumeral(t0))) {
          ASS(!isZero(asig(n).tryNumeral(t1)))
          /* cmpSameSkeleton(0, r) = LESS */
          return some(Ordering::Result::LESS);

        } else if (isZero(asig(n).tryNumeral(t1))) {
          ASS(!isZero(asig(n).tryNumeral(t0)))
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

#define DEBUG_RESULT(lvl, msg, ...)                                                       \
     auto impl = [&]() { __VA_ARGS__ };                                                   \
     DEBUG_ALASCA_ORD(lvl, msg, "???");                                                   \
     auto res = impl();                                                                   \
     DEBUG_ALASCA_ORD(lvl, msg, res);                                                     \
     return res;                                                                          \

#define DEBUG_FN_RESULT(lvl, msg, ...)                                                    \
  { DEBUG_RESULT(lvl, msg, __VA_ARGS__) }

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
                  ASSERTION_VIOLATION
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
  using Atom = std::tuple<TermList, unsigned>;

  static unsigned lvl(Sign sgn, AlascaPredicate p) {
    if (sgn == Sign::Zero) return 0;
    switch(p) {
      case AlascaPredicate::EQ: return 1;
      case AlascaPredicate::GREATER:
      case AlascaPredicate::GREATER_EQ:
                               return sgn == Sign::Pos ? 2 
                                    : sgn == Sign::Neg ? 3
                                    : assertionViolation<unsigned>();
      case AlascaPredicate::NEQ:
                               return 4;
    } ASSERTION_VIOLATION
  }

  template<class NumTraits, class Iter>
  static MultiSet<Atom> atoms(NumTraits n, Iter iter, AlascaPredicate p) {
    RStack<Atom> out;
    RStack<TermList> todo;
    todo->loadFromIterator(std::move(iter));
    auto atom = [&](auto t, auto sgn) -> Atom {
      return std::make_tuple(t, lvl(sgn, p));
    };

    while (todo->isNonEmpty()) {
      auto t = todo->pop();
      if (asig(n).isAdd(t)) {
        todo->push(t.term()->termArg(0));
        todo->push(t.term()->termArg(1));

      } else if (auto k = asig(n).tryNumeral(t)) {
        out->push(atom(n.one(), k->sign()));

      } else if (auto k = asig(n).tryLinMul(t)) {
        out->push(atom(t.term()->termArg(0), k->sign()));

      } else {
        out->push(atom(t, Sign::Pos));
      }
    }
    return MultiSet<Atom>::fromIterator(arrayIter(std::move(out)));
  }

  struct Atoms {
    MultiSet<Atom> atoms;
    SmallArray<TermList, 2> numTerms;
  };

  Option<Atoms> atoms(Literal* l) const {
    auto itpRes = forAnyNumTraits([&](auto n) -> Option<Atoms> {

#define TRY_INEQ(sym, check) \
        if (check(l)) { \
          ASS_EQ(l->termArg(1), n.zero()) \
          auto t = l->termArg(0); \
          return some(Atoms { atoms(n, iterItems(t), sym), SmallArray<TermList, 2>::fromItems(t) }); \
        } \

#define TRY_EQ(sym, check) \
        if (check(l)) { \
          auto t0 = l->termArg(1) == n.zero() ? l->termArg(0) : l->termArg(1); \
          auto t1 = l->termArg(1) == n.zero() ? l->termArg(1) : l->termArg(0); \
          if (t1 == n.zero()) { \
            return some(Atoms { atoms(n, iterItems(t0), sym), SmallArray<TermList, 2>::fromItems(t1, t0) }); \
          } else { \
            return some(Atoms { atoms(n, iterItems(t1, t0), sym), SmallArray<TermList, 2>::fromItems(t1, t0) }); \
          } \
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
      return some(Atoms {
          .atoms = iterItems(0, 1)
            .map([&](auto i) { return std::make_tuple(l->termArg(i), lvl(Sign::Pos, sym)); })
            .template collect<MultiSet>(),
            .numTerms = SmallArray<TermList,2>::fromItems() });
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
            [&](){ return AlascaOrderingUtils::cmpN(std::get<1>(a1), std::get<1>(a2)); }
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
            [&](){ return OrderingUtils::mulExt(atoms1->atoms, atoms2->atoms, [&](auto l, auto r) { return cmpAtom(l, r); }); },
            [&](){ 
              ASS(atoms1->numTerms.size() == atoms2->numTerms.size())
              return AlascaOrderingUtils::lexIter(
                  arrayIter(atoms1->numTerms).zip(arrayIter(atoms2->numTerms))
                  .map([this](auto ts) { return this->compare(ts.first, ts.second); })
                  );
            },
            [&](){ return cmpPrec(l1, l2); }
            );

    } else {
      ASS(atoms1.isNone() && atoms2.isNone())
      return compareUninterpreted(l1,l2);
    }
  }


};

using LAKBO = SkelOrd<KBO>;

template<class Inner>
SkelOrd(Inner) -> SkelOrd<Inner>;


#undef DEBUG_FN_RESULT
#undef DEBUG_RESULT

} // namespace Kernel

#endif // __ALASCA_ORDERING__
