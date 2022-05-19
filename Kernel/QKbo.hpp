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

namespace Kernel {

using namespace Lib;

template<class T>
class MultiSet {
  Stack<std::tuple<T, unsigned>> _elems;
  void integrity() const {
    ASS(std::is_sorted(_elems.begin(), _elems.end(), [](auto l, auto r) { return std::get<0>(l) < std::get<0>(r); }))
    for (auto e : _elems) {
      ASS(get<1>(e) != 0)
    }
  }
public:
  MultiSet() : _elems() {}
  MultiSet(std::initializer_list<T> elems0) : _elems() {
    Stack<T> elems(elems0);
    std::sort(elems.begin(), elems.end());
    auto iter = elems.begin();
    while (iter != elems.end()) {
      auto elem = *iter++;
      unsigned n = 1;
      while (iter != elems.end() && *iter == elem) {
        n++;
        iter++;
      }
      _elems.push(std::make_tuple(elem, n));
    }
  }


  friend std::ostream& operator<<(std::ostream& out, MultiSet const& self)
  { 
    out << "{";
    for (auto& e : self._elems) {
      out << std::get<1>(e) << " x " << std::get<0>(e);
    }
    out << "}";
    return out; 
  }
  friend bool operator==(MultiSet const& lhs, MultiSet const& rhs)
  { 
    lhs.integrity();
    rhs.integrity();
    return lhs._elems == rhs._elems;
  }

  friend bool operator!=(MultiSet const& lhs, MultiSet const& rhs)
  { return !(lhs == rhs); }
};

enum class Sign : uint8_t {
  Zero = 0,
  Pos = 1,
  Neg = 2,
};

// bool operator<(Sign const& l, Sign const& r)
// { return (uint8_t) l < (uint8_t) r; }
//
// bool operator> (Sign const& l, Sign const& r) { return r < l; }
// bool operator<=(Sign const& l, Sign const& r) { return l == r || l < r; }
// bool operator>=(Sign const& l, Sign const& r) { return l == r || l > r; }


inline std::ostream& operator<<(std::ostream& out, Sign const& self)
{ 
  switch(self) {
    case Sign::Zero: return out << "0";
    case Sign::Pos: return out << "+";
    case Sign::Neg: return out << "-";
  }
  ASSERTION_VIOLATION
}



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

  static SigmaNf sigmaNf(TermList t);
  Result compare(SigmaNf const& l, SigmaNf const& r) const;

private:
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
