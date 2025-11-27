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

#include "Kernel/ALASCA.hpp"
#include "Kernel/KBO.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/OrderingUtils.hpp"

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

};


struct LAKBO {
  KBO _kbo;
  std::shared_ptr<InequalityNormalizer> _norm;

  LAKBO(KBO kbo, std::shared_ptr<InequalityNormalizer> norm) : _kbo(std::move(kbo)), _norm(std::move(norm)) {}
  LAKBO(Problem& prb, const Options& opt) : LAKBO(KBO(prb, opt), InequalityNormalizer::global()) {}

  InequalityNormalizer& norm() const { return *_norm; }

  void show(std::ostream& out) const { return _kbo.show(out); }

  template<class NumTraits>
  Ordering::Result cmpSameSkeleton(MonomFactors<NumTraits> const& t0, MonomFactors<NumTraits> const& t1) const 
  { 
    auto iterFlat = [](MonomFactors<NumTraits> const& m) {
      return m.iter()
        .flatMap([](auto& x) { return 
            range(0, x.power)
              .map([&](auto) -> auto& { return x.term; }); });
    };
    return AlascaOrderingUtils::lexIter(
        iterFlat(t0).zip(iterFlat(t1))
          .map([&](auto pair) { return cmpSameSkeleton(pair.first, pair.second); })
        );
  }

  template<class NumTraits>
  Ordering::Result cmpSameSkeleton(Monom<NumTraits> const& t0, Monom<NumTraits> const& t1) const 
  { 
    return AlascaOrderingUtils::lexLazy(
        [&](){ return cmpSameSkeleton(*t0.factors, *t1.factors); },
        [&](){ return AlascaOrderingUtils::cmpQ(t0.numeral, t1.numeral); }
    );
  }


  template<class NumTraits>
  Ordering::Result cmpSameSkeleton(Polynom<NumTraits> const& t0, Polynom<NumTraits> const& t1) const 
  { 
    if (t0.nSummands() == 1 && t1.nSummands() == 1) {
      return cmpSameSkeleton(t0.summandAt(0), t1.summandAt(0));
    } else {
      auto set = [](auto p) { return p.iterSummands().map([](auto& x) { return x; }).template collect<MultiSet>(); };
      return OrderingUtils::mulExt(set(t0), set(t1), [&](auto& l, auto& r) { return compare(l, r); });
    }
  }

  template<class NumTraits>
  Ordering::Result cmpSameSkeleton(Polynom<NumTraits> const& t0, PolyNf const& t1) const 
  { return cmpSameSkeleton(t0, *t1.template wrapPoly<NumTraits>()); }

  Ordering::Result cmpSameSkeleton(TermList t0, TermList t1) const 
  { return cmpSameSkeleton(norm().normalize(t0), norm().normalize(t1)); }

  Ordering::Result cmpSameSkeleton(AnyPoly const& t0, PolyNf const& t1) const 
  { return t0.apply([&](auto& t0) { return cmpSameSkeleton(*t0, t1); }); }

  Ordering::Result cmpSameSkeleton(PolyNf const& t0, PolyNf const& t1) const {
    if (t0 == t1) return Ordering::Result::EQUAL;
    if (auto p0 = t0.template as<AnyPoly>()) {
      return cmpSameSkeleton(*p0, t1);
    } else if (auto p1 = t1.template as<AnyPoly>()) {
      return Ordering::reverse(cmpSameSkeleton(*p1, t0));

    } else if (t0.is<Variable>() || t1.is<Variable>()) {
      return Ordering::Result::INCOMPARABLE;

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
        return AlascaOrderingUtils::lexIter(f0->iterArgs().zip(f1->iterArgs())
            .map([&](auto pair) { return cmpSameSkeleton(pair.first, pair.second); }));
      }
    }
  }

  Option<TermList> skeleton(Variable const& t) const {
    // TODO theory
    return some(TermList::var(t.id()));
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

#define DEBUG_RESULT(lvl, msg, ...)                                                       \
     auto impl = [&]() { __VA_ARGS__ };                                                   \
     auto res = impl();                                                                   \
     DEBUG_ALASCA_ORD(lvl, msg, res);                                                      \
     return res;                                                                          \

#define DEBUG_FN_RESULT(lvl, msg, ...)                                                    \
  { DEBUG_RESULT(lvl, msg, __VA_ARGS__) }

  template<class NumTraits>
  Option<TermList> skeleton(Monom<NumTraits> const& t) const 
  DEBUG_FN_RESULT(2, Output::cat("skeleton(", t, ") = "),
  { return skeleton(*t.factors); }
  )

  template<class NumTraits>
  Option<TermList> skeleton(MonomFactors<NumTraits> const& t) const 
  DEBUG_FN_RESULT(2, Output::cat("skeleton(", t, ") = "),
  { return trySkeleton(t.iter())
      .map([](auto skels) { return NumTraits::product(arrayIter(*skels)); }); }
  )

  template<class NumTraits>
  Option<TermList> skeleton(MonomFactor<NumTraits> const& t) const 
  DEBUG_FN_RESULT(2, Output::cat("skeleton(", t, ") = "),
  { 
    return skeleton(t.term)
      .map([&](auto skel) { 
          ASS(t.power >= 0) 
          return t.power == 1 
               ? skel
               : NumTraits::product(range(0, t.power).map([skel](auto) { return skel; }));
          });
  }
  )

  template<class NumTraits>
  Option<TermList> skeleton(Polynom<NumTraits> const& t) const 
  DEBUG_FN_RESULT(2, Output::cat("skeleton(", t, ") = "),
  {
    if (auto summands = trySkeleton(t.iterSummands())) {
      auto maxIter = OrderingUtils::maxElems(summands->size(), 
          [&](auto t0, auto t1) { return _kbo.compare((*summands)[t0], (*summands)[t1]);  }, 
          [&](auto i) { return (*summands)[i]; }, 
          SelectionCriterion::NOT_LESS, 
          /* dedup */ true);
      if (!maxIter.hasNext()) {
        return Option<TermList>{};
      } else {
        auto max = maxIter.next();
        if (maxIter.hasNext()) {
          // no unique max 
          // TODO theory (?)
          return Option<TermList>{};
        } else {
          return some((*summands)[max]);
        }
      }
    } else {
      return Option<TermList>{};
    }
  }
  )

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

  // TODO atoms of equalities normalizing!!!

  auto skeleton(TermList t) const 
  { return skeleton(norm().normalize(t)); }

  template<class Term>
  Ordering::Result compare(Term const& t0, Term const& t1) const 
  DEBUG_FN_RESULT(2, Output::cat("compare", std::tie(t0, t1), " = "),
  {
    if (t0 == t1) return Ordering::Result::EQUAL;
    auto s0 = skeleton(t0);
    auto s1 = skeleton(t1);
    DEBUG_ALASCA_ORD(1, "skel(", t0, ") = ", s0)
    DEBUG_ALASCA_ORD(1, "skel(", t1, ") = ", s1)
    if (s0.isSome() && s1.isSome()) {
      return AlascaOrderingUtils::lexLazy(
          [&](){ return _kbo.compare(*s0, *s1); },
          [&](){ return cmpSameSkeleton(t0, t1); }
          );
    } else {
      //TODO
      return Ordering::Result::INCOMPARABLE;
    }
  }
  )

  Ordering::Result compare(TermList t0, TermList t1) const {
    if (t0.isTerm() && t1.isTerm()) { ASS_EQ(t0.term()->isSort(), t1.term()->isSort()) }
    if ((t0.isTerm() && t0.term()->isSort()) 
      ||(t1.isTerm() && t1.term()->isSort())) {
      return _kbo.compare(t0, t1);
    } else {
      return compare(norm().normalize(t0), norm().normalize(t1));
    }
  }

  int predPrec(unsigned pred) const { return _kbo.predicatePrecedence(pred); }
  Ordering::Result cmpPredPrec(unsigned p0, unsigned p1) const { return AlascaOrderingUtils::cmpN(predPrec(p0), predPrec(p1)); }
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

  using Atom = std::tuple<PolyNf, unsigned , AnyNumeral>;

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

  MultiSet<Atom> atoms(AnyAlascaLiteral const& l) const 
  { return l.apply([&](auto l) { return atoms(l); }); }

  template<class NumTraits>
  MultiSet<Atom> atoms(AlascaLiteral<NumTraits> const& l1) const {
    return l1.term().iterSummands()
      .map([&](auto monom) { return std::make_tuple(PolyNf(monom.factors), lvl(l1.symbol()), AnyNumeral(monom.numeral)); })
      .template collect<MultiSet>();
  }

  Option<MultiSet<Atom>> atoms(Literal* l) const {
    if (auto alasca = _termOrdering.norm().tryNormalizeInterpreted(l)) {
      return some(atoms(*alasca));
    } else if (l->isEquality()) {
      auto sym = l->isPositive() ? AlascaPredicate::EQ : AlascaPredicate::NEQ;
      return some(iterItems(l->termArg(0), l->termArg(1))
        .map([&](auto t) { return std::make_tuple(_termOrdering.norm().normalize(t), lvl(sym), AnyNumeral(std::make_tuple())); })
        .template collect<MultiSet>());
    } else {
      return {};
    }
  }

  Ordering::Result cmpAtom(Atom a1, Atom a2) const {
    return AlascaOrderingUtils::lexLazy(
            [&](){ return _termOrdering.compare(std::get<0>(a1), std::get<0>(a2)); },
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

  ~LiteralOrdering() override {}

  Result compare(Literal* l1, Literal* l2) const override {
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

  Result compare(TermList t1, TermList t2) const final
  { return _termOrdering.compare(t1, t2); }

  void show(std::ostream& out) const final
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

} // namespace Kernel

#endif // __ALASCA_ORDERING__
