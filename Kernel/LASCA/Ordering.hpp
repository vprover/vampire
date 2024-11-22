/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef __LASCA_ORDERING__
#define __LASCA_ORDERING__

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Kernel/LASCA.hpp"

#include "Kernel/Ordering.hpp"
#include "Lib/DArray.hpp"
#include "Kernel/LaLpo.hpp"
#include "Kernel/KBO.hpp"
#include "Kernel/OrderingUtils.hpp"

namespace Kernel {

using namespace Lib;
// TODO namespacing of all lasca stuff

struct LascaOrderingUtils {

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
        case Ordering::Result::GREATER_EQ:
        case Ordering::Result::LESS_EQ:
          ASSERTION_VIOLATION
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
  { ASSERTION_VIOLATION_REP("integers should be translated away in ALASCA+I") }

};


struct LAKBO {
  KBO _kbo;
  std::shared_ptr<LascaState> _state;

  LAKBO(Problem& prb, const Options& opt) : _kbo(prb, opt) {}
  void setState(std::shared_ptr<LascaState> s) { _state = std::move(s); }
  LascaState& shared() const { return *_state; }

  void show(std::ostream& out) const { return _kbo.show(out); }

  template<class NumTraits>
  Ordering::Result cmpSameSkeleton(MonomFactors<NumTraits> const& t0, MonomFactors<NumTraits> const& t1) const 
  { 
    return LascaOrderingUtils::lexIter(
        t0.iter().zip(t1.iter())
          .map([&](auto pair) { return cmpSameSkeleton(pair.first.term, pair.second.term); })
        );
  }

  template<class NumTraits>
  Ordering::Result cmpSameSkeleton(Monom<NumTraits> const& t0, Monom<NumTraits> const& t1) const 
  { 
    return LascaOrderingUtils::lexLazy(
        [&](){ return cmpSameSkeleton(*t0.factors, *t1.factors); },
        [&](){ return LascaOrderingUtils::cmpQ(t0.numeral, t1.numeral); }
    );
  }


  template<class NumTraits>
  Ordering::Result cmpSameSkeleton(Polynom<NumTraits> const& t0, Polynom<NumTraits> const& t1) const 
  { 
    if (t0.nSummands() == 1 && t1.nSummands() == 1) {
      return cmpSameSkeleton(t0.summandAt(0), t1.summandAt(0));
    } else {
      auto set = [](auto p) { return p.iterSummands().map([](auto& x) { return x; }).template collect<MultiSet>(); };
      return OrderingUtils2::mulExt(set(t0), set(t1), [&](auto& l, auto& r) { return compare(l, r); });
    }
  }

  template<class NumTraits>
  Ordering::Result cmpSameSkeleton(Polynom<NumTraits> const& t0, PolyNf const& t1) const 
  { return cmpSameSkeleton(t0, *t1.template wrapPoly<NumTraits>()); }

  Ordering::Result cmpSameSkeleton(AnyPoly const& t0, PolyNf const& t1) const 
  { return t0.apply([&](auto& t0) { return cmpSameSkeleton(*t0, t1); }); }

  Ordering::Result cmpSameSkeleton(PolyNf const& t0, PolyNf const& t1) const {
    if (auto p0 = t0.template as<AnyPoly>()) {
      return cmpSameSkeleton(*p0, t1);
    } else if (auto p1 = t1.template as<AnyPoly>()) {
      return Ordering::reverse(cmpSameSkeleton(*p1, t0));
    } else {
      ASS(t0.is<Perfect<FuncTerm>>() && t1.is<Perfect<FuncTerm>>())
      auto f0 = t0.as<Perfect<FuncTerm>>().unwrap();
      auto f1 = t1.as<Perfect<FuncTerm>>().unwrap();
      auto floor0 = f0->function().isFloor();
      auto floor1 = f1->function().isFloor();
      if (floor0 && floor1) {
        return cmpSameSkeleton(f0->arg(0), f1->arg(0));
      } else if (!floor0 && floor1) {
        return Ordering::Result::LESS;
      } else if (floor0 && !floor1) {
        return Ordering::Result::GREATER;
      } else {
        ASS(!floor0 && !floor1)
        return LascaOrderingUtils::lexIter(f0->iterArgs().zip(f1->iterArgs())
            .map([&](auto pair) { return cmpSameSkeleton(pair.first, pair.second); }));
      }
    }
  }

  Option<TermList> skeleton(Variable const& t) const {
    // TODO
    return {};
  }

  Option<TermList> skeleton(AnyPoly const& t) const 
  { return t.apply([&](auto& t) { return skeleton(*t); }); }

  template<class Iter>
  Option<RStack<TermList>> trySkeleton(Iter iter) const {
    auto out = RStack<TermList>();
    for (auto x : iter) {
      if (auto s = skeleton(x)) {
        out->push(*s);
      } else {
        return {};
      }
    }
    return some(std::move(out));
  }

  template<class NumTraits>
  Option<TermList> skeleton(Monom<NumTraits> const& t) const 
  { return skeleton(*t.factors); }

  template<class NumTraits>
  Option<TermList> skeleton(MonomFactors<NumTraits> const& t) const 
  { return trySkeleton(t.iter())
      .map([](auto skels) { return NumTraits::product(arrayIter(*skels)); }); }

  template<class NumTraits>
  Option<TermList> skeleton(MonomFactor<NumTraits> const& t) const 
  { 
    return skeleton(t.term)
      .map([&](auto skel) { 
          ASS(t.power >= 0) 
          return t.power == 1 
               ? skel
               : NumTraits::product(range(0, t.power).map([skel](auto) { return skel; }));
          });
  }

  template<class NumTraits>
  Option<TermList> skeleton(Polynom<NumTraits> const& t) const {
    if (auto summands = trySkeleton(t.iterSummands())) {
      auto maxIter = OrderingUtils2::maxElems(summands->size(), 
          [&](auto t0, auto t1) { return _kbo.compare((*summands)[t0], (*summands)[t1]);  }, 
          [&](auto i) { return (*summands)[i]; }, 
          SelectionCriterion::STRICTLY_MAX);
      if (!maxIter.hasNext()) {
        return {};
      } else {
        auto max = maxIter.next();
        if (maxIter.hasNext()) {
          // no unique max 
          // TODO theory (?)
          return {};
        } else {
          return some((*summands)[max]);
        }
      }
    } else {
      return {};
    }
  }

  Option<TermList> skeleton(Perfect<FuncTerm> const& t) const {
    return trySkeleton(t->iterArgs())
      .map([&](auto args) {
          if (t->function().isFloor()) {
            return args[0];
          } else {
            return TermList(Term::createFromIter(
                  t->function().id(),
                  concatIters(
                    t->function().iterTypeArgs(),
                    arrayIter(*args)
                    )));
          }
      });
  }

  Option<TermList> skeleton(PolyNf const& t) const 
  { return t.apply([&](auto& x) { return skeleton(x); }); }

  Ordering::Result compare(TermList t0, TermList t1) const {
    if (t0 == t1) return Ordering::Result::EQUAL;
    if (t0.isVar() && t1.isVar()) {
      return Ordering::Result::INCOMPARABLE;
    } else if (t0.isVar()) {
      return compareVar(t0.var(), t1.term());
    } else if (t1.isVar()) {
      return Ordering::reverse(compareVar(t1.var(), t0.term()));
    } else {
      return compare(shared().normalize(t0.term()), shared().normalize(t1.term()));
    }
  }

  // TODO atoms of equalities normalizing!!!


  template<class Term>
  Ordering::Result compare(Term const& t0, Term const& t1) const {
    auto s0 = skeleton(t0);
    auto s1 = skeleton(t1);
    if (s0.isSome() && s1.isSome()) {
      return LascaOrderingUtils::lexLazy(
          [&](){ return _kbo.compare(*s0, *s1); },
          [&](){ return cmpSameSkeleton(t0, t1); }
          );
    } else {
      //TODO
      return Ordering::Result::INCOMPARABLE;
    }
  }

  Ordering::Result compareVar(unsigned v, Term* t) const {
    // TODO firgure out theory for vars
    return Ordering::INCOMPARABLE;
  }
  int predicatePrecedence(unsigned pred) const { return _kbo.predicatePrecedence(pred); }

};

template<class TermOrdering>
class LiteralOrdering
  : public Ordering
{
  TermOrdering _termOrdering;

  Ordering::Result cmpPrecUninterpreted(Literal* l0, Literal* l1) const {
    return LascaOrderingUtils::cmpN(
        _termOrdering.predicatePrecedence(l0->functor()), 
        _termOrdering.predicatePrecedence(l1->functor()));
  }

  template<class NumTraits>
  static Ordering::Result cmpPrec(LascaPredicate p0, LascaPredicate p1) 
  {
    // TODO do we want a specific precedence on uninterpreted predicates?
    return LascaOrderingUtils::cmpN(p0, p1);
  }

  static Ordering::Result cmpPolarity(Literal* l0, Literal* l1) 
  { return cmpPolarity(l0->isPositive(), l1->isPositive()); }

  static Ordering::Result cmpPolarity(bool p0, bool p1) {
    return  p0 ==  p1 ? Ordering::Result::EQUAL
         : !p0 &&  p1 ? Ordering::Result::GREATER
         :  p0 && !p1 ? Ordering::Result::LESS
         : assertionViolation<Ordering::Result>();
  }

  template<class NumTraits>
  using Atom = std::tuple<Perfect<MonomFactors<NumTraits>>, unsigned, typename NumTraits::ConstantType>;

  unsigned lvl(LascaPredicate p) const {
    switch(p) {
      case LascaPredicate::EQ: return 0;
      case LascaPredicate::NEQ:
      case LascaPredicate::GREATER:
      case LascaPredicate::GREATER_EQ:
      case LascaPredicate::IS_INT_POS:
      case LascaPredicate::IS_INT_NEG: 
                               return 1;
    } ASSERTION_VIOLATION
  }

  template<class NumTraits>
  MultiSet<Atom<NumTraits>> atoms(LascaLiteral<NumTraits> const& l1) const {
    return l1.term().iterSummands()
      .map([&](auto monom) { return std::make_tuple(monom.factors, lvl(l1.symbol()), monom.numeral); })
      .template collect<MultiSet>();
  }

  template<class NumTraits>
  Ordering::Result cmpAtom(Atom<NumTraits> a1, Atom<NumTraits> a2) const {
    return LascaOrderingUtils::lexLazy(
            [&](){ return _termOrdering.compare(*std::get<0>(a1), *std::get<0>(a2)); },
            [&](){ return LascaOrderingUtils::cmpN(std::get<1>(a1), std::get<1>(a2)); },
            [&](){ return LascaOrderingUtils::cmpQ(std::get<2>(a1), std::get<2>(a2)); }
          );
  }

  template<class NumTraits>
  Result compare(LascaLiteral<NumTraits> const& l1, LascaLiteral<NumTraits> const& l2) const 
  {
    auto a1 = atoms(l1);
    auto a2 = atoms(l2);
    return LascaOrderingUtils::lexLazy(
          [&](){ return OrderingUtils2::mulExt(a1, a2, [&](auto l, auto r) { return cmpAtom<NumTraits>(l, r); }); },
          [&](){ return cmpPrec<NumTraits>(l1.symbol(), l2.symbol()); }
          );
  }

  Result cmpLascaLit(AnyLascaLiteral const& l1, AnyLascaLiteral const& l2) const {
    if (l1.tag() == l2.tag()) {
      return l1.applyWithIdx([&](auto& l1, auto N) { return compare(l1, l2.unwrap<N.value>()); });
    } else {
      return l1.tag() < l2.tag() ? Ordering::Result::LESS
                                 : Ordering::Result::GREATER;
    }
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

  Result compare(Literal* l1, Literal* l2) const override {
    auto lasca1 = _termOrdering.shared().normalizer.renormalize(l1);
    auto lasca2 = _termOrdering.shared().normalizer.renormalize(l2);
    if (lasca1.isNone() && lasca2.isSome()) {
      return Ordering::GREATER;

    } else if (lasca1.isSome() && lasca2.isNone()) {
      return Ordering::LESS;

    } else if (lasca1.isSome() && lasca2.isSome()) {
      return cmpLascaLit(*lasca1, *lasca2);

    } else {
      ASS(lasca1.isNone() && lasca2.isNone())
      return compareUninterpreted(l1,l2);
    }
  }

  Result compare(TermList t1, TermList t2) const final override 
  { return _termOrdering.compare(t1, t2); }

  void show(std::ostream& out) const final override 
  { _termOrdering.show(out); }

  void setState(std::shared_ptr<LascaState> s) { _termOrdering.setState(std::move(s)); }

private:

  Result compareUninterpreted(Literal* l1, Literal* l2) const {
    if (l1->functor() == l2->functor()) {
      // TODO think about the polymorphic case
      return LascaOrderingUtils::lexIter(concatIters(
            anyArgIter(l1).zip(anyArgIter(l2))
              .map([&](auto pair) { return _termOrdering.compare(pair.first, pair.second); }),
            iterItems([&](){ return cmpPolarity(l1, l2); }).eval()
      ));
    } else {
      return cmpPrecUninterpreted(l1, l2);
    }
  }
};

} // namespace Kernel

#endif // __LASCA_ORDERING__
