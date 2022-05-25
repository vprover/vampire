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
 * @file QKbo.hpp
 *
 * Defines a Knuth-Bendix Ordering for linear arithmetic. This ignores numeral multiplications,
 * (i.e. it considers terms t and nt where n is a numeral as equaivalent). Further it is not sensitive to
 * bracketing or permuting of multiplications and additions.
 */

#ifndef __QKBO__
#define __QKBO__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Kernel/IRC.hpp"

#include "Ordering.hpp"
#include "Lib/DArray.hpp"
#include "Kernel/LaLpo.hpp"
#include "Kernel/KBO.hpp"
#include "Kernel/OrderingUtils.hpp"

namespace Kernel {

using namespace Lib;


// TODO move to right place (IRC.hpp ?)
struct SignedTerm 
{
  Sign sign;
  TermList term;

  static SignedTerm pos(TermList t) 
  { return { .sign = Sign::Pos, .term = t, }; }

  static SignedTerm neg(TermList t) 
  { return { .sign = Sign::Neg, .term = t, }; }

  static SignedTerm zero(TermList t) 
  { return { .sign = Sign::Zero, .term = t, }; }

  friend std::ostream& operator<<(std::ostream& out, SignedTerm const& self)
  { return out << self.sign << self.term; }

  friend bool operator==(SignedTerm const& lhs, SignedTerm const& rhs)
  { return lhs.sign == rhs.sign && lhs.term == rhs.term; }

  friend bool operator!=(SignedTerm const& lhs, SignedTerm const& rhs)
  { return !(lhs == rhs); }

  friend bool operator<(SignedTerm const& l, SignedTerm const& r)
  { return std::tie(l.term, l.sign) < std::tie(r.term, r.sign); }

  friend bool operator> (SignedTerm const& l, SignedTerm const& r) { return r < l; }
  friend bool operator<=(SignedTerm const& l, SignedTerm const& r) { return l == r || l < r; }
  friend bool operator>=(SignedTerm const& l, SignedTerm const& r) { return l == r || l > r; }
};

// represents a tuple of a numeral (1/k), and a multiset { ti | i in I } of signed terms
// with the intended semantics that the term that has been normalized to this
// sigmaNf is equivalent to 1/k * ( t1 + t2 + ... + tn )
struct SigmaNf {
  unsigned k;
  MultiSet<SignedTerm> sum;
  SigmaNf(unsigned k, MultiSet<SignedTerm> sum) : k(k), sum(std::move(sum)) {}
  friend std::ostream& operator<<(std::ostream& out, SigmaNf const& self)
  { return out << "(1 / " << self.k << ") " << self.sum; }

  friend bool operator==(SigmaNf const& lhs, SigmaNf const& rhs)
  { return lhs.k == rhs.k && lhs.sum == rhs.sum; }

  friend bool operator!=(SigmaNf const& lhs, SigmaNf const& rhs)
  { return !(lhs == rhs); }
};


class QKbo 
  : public Ordering
{
public:
  CLASS_NAME(QKbo);
  USE_ALLOCATOR(QKbo);

  QKbo(QKbo&& kbo) = default;
  QKbo& operator=(QKbo&& kbo) = default;
  explicit QKbo(Precedence);

  QKbo(Problem& prb, const Options& opts) 
    : QKbo(Precedence(prb,opts)) {}

  virtual ~QKbo() {}

  Result compare(Literal* l1, Literal* l2) const override;
  Result compare(TermList, TermList) const final override;

  void show(ostream& out) const final override;

  Comparison compareFunctors(unsigned fun1, unsigned fun2) const override { ASSERTION_VIOLATION }

  void setState(std::shared_ptr<IrcState> s) { _shared = std::move(s); }

private:
  template<class NumTraits>
  SigmaNf rmNum(std::tuple<unsigned, Perfect<Polynom<NumTraits>>> t) const
  {
    auto multiSet = MultiSet<SignedTerm>::fromSortedStack(
        std::get<1>(t)->iterSummands()
          .map([](auto s) {
            auto count  = Int::safeAbs(ifOfType<IntegerConstantType>(s.numeral, 
                           [&](IntegerConstantType num) { return num; },
                            /* decltype(num) in { RatTraits, RealTraits } */
                           [&](auto num) { 
                             ASS_EQ(num.denominator(), IntegerConstantType(1))
                             return num.numerator();
                           }).toInner());
            SignedTerm term = { 
              .sign = s.numeral.sign(),
              .term = s.factors->denormalize(),
            };
            return std::make_tuple(term, count);
          })
          .template collect<Stack>()
      );
    return SigmaNf(std::get<0>(t), std::move(multiSet));
    ASSERTION_VIOLATION
  }

  std::tuple<unsigned, Perfect<Polynom<IntTraits>>> divNf(Perfect<Polynom<IntTraits>> t) const
  { return std::make_tuple(1, t); }

  template<class NumTraits>
  std::tuple<unsigned, Perfect<Polynom<NumTraits>>> divNf(Perfect<Polynom<NumTraits>> t) const
  {
    auto l = t->iterSummands()
      .map([](auto s) { return s.numeral.denominator(); })
      .fold(IntegerConstantType(1), [&](auto acc, auto next) 
               { return IntegerConstantType::lcm(acc, next); });
    return std::make_tuple(Int::safeAbs(l.toInner()), typename NumTraits::ConstantType(l, IntegerConstantType(1)) * t);
  }

  auto asClosure() const 
  { return [this](auto const& l, auto const& r) { return this->compare(l, r); }; }

#ifdef VDEBUG
public:
#endif
  template<class NumTraits>
  SigmaNf sigmaNf(TermList t) const
  {
    auto nf0 = _shared->normalize(TypedTermList(t, NumTraits::sort())).template wrapPoly<NumTraits>();
    return rmNum(divNf(nf0));
  }
  template<class NumTraits>
  MultiSet<SignedTerm> atomsStar(Literal* t) const
  {
    ASSERTION_VIOLATION
    // ASS_Eq(l->numTermArguments(), 2)
    // auto nf = sigmaNf<NumTraits>(t);
  }

private:
  Result compare(SigmaNf l, SigmaNf r) const;

  using FlatSum = Stack<std::tuple<Option<TermList>, RationalConstantType>>;
  Ordering::Result cmpSum(FlatSum const& l, FlatSum const& r) const;
  FlatSum flatWithCoeffs(TermList t) const;
  Result cmpNonAbstr(TermList, TermList) const;
  Option<TermList> abstr(TermList) const;

  Precedence _prec;
  std::shared_ptr<IrcState> _shared;
  KBO _kbo;
};

} // namespace Kernel

#endif // __QKBO__
