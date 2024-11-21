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
  LAKBO(Problem& prb, const Options& opt) {}
  void show(std::ostream& out) const {  }
  template<class NumTraits>
  Ordering::Result compare(Polynom<NumTraits> const& t0, Polynom<NumTraits> const& t1) const;
  Ordering::Result compare(PolyNf const& t0, PolyNf const& t1) const;
  Ordering::Result compare(TermList const& t0, TermList const& t1) const;
};

template<class TermOrdering>
class LiteralOrdering
  : public PrecedenceOrdering
{
  std::shared_ptr<LascaState> _shared;
  TermOrdering _termOrdering;

  Ordering::Result cmpPrecUninterpreted(Literal* l0, Literal* l1) const {
    return LascaOrderingUtils::cmpN(
        predicatePrecedence(l0->functor()), 
        predicatePrecedence(l1->functor()));
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
  using Atom = std::tuple<PolyNf, unsigned, typename NumTraits::ConstantType>;

  // TODO
  template<class NumTraits>
  MultiSet<Atom<NumTraits>> atoms(LascaLiteral<NumTraits> const& l1) const;

  template<class NumTraits>
  Ordering::Result cmpAtom(Atom<NumTraits> a1, Atom<NumTraits> a2) const {
    return LascaOrderingUtils::lexLazy(
            [&](){ return _termOrdering.compare(std::get<0>(a1), std::get<0>(a2)); },
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

  Result compare(AnyLascaLiteral const& l1, AnyLascaLiteral const& l2) const {
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
  LiteralOrdering(Problem& prb, const Options& opt) 
    : PrecedenceOrdering(prb, opt)
    , _termOrdering(prb, opt) { }
  // LiteralOrdering(Problem& prb, const Options& opts)
  //   : LiteralOrdering(TermOrdering(prb,opts)) {}

  virtual ~LiteralOrdering() {}

  // TODO fix class hierarchy top avoid this
  Result comparePredicates(Literal* l1, Literal* l2) const override { ASSERTION_VIOLATION_REP("unreachable as we override compare(Literal*,Literal*)") }

  Result compare(Literal* l1, Literal* l2) const override {
    auto lasca1 = _shared->normalizer.renormalize(l1);
    auto lasca2 = _shared->normalizer.renormalize(l2);
    if (lasca1.isNone() && lasca2.isSome()) {
      return Ordering::GREATER;

    } else if (lasca1.isSome() && lasca2.isNone()) {
      return Ordering::LESS;

    } else if (lasca1.isSome() && lasca2.isSome()) {
      return compare(*lasca1, *lasca2);

    } else if (lasca1.isNone()) {
      ASS(lasca1.isNone() && lasca2.isNone())
      return compare(*lasca1, *lasca2);
    } else {
      return compareUninterpreted(l1,l2);
    }
  }

  Result compare(TermList t1, TermList t2) const final override 
  { return _termOrdering.compare(t1, t2); }

  void showConcrete(std::ostream& out) const final override 
  { _termOrdering.show(out); }

  void setState(std::shared_ptr<LascaState> s) { _termOrdering.setState(std::move(s)); }

  // // TODO optimize?
  // Result compare(AppliedTerm t1, AppliedTerm t2) const override
  // { return compare(t1.apply(), t2.apply()); }
  //
  // // TODO more efficient impl (?)
  // bool isGreater(AppliedTerm t1, AppliedTerm t2) const override
  // { return compare(t1, t2) == Result::GREATER; }

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
