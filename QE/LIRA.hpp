/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __QE_LIRA__
#define __QE_LIRA__


#include "Debug/Assertion.hpp"
#include "Kernel/Formula.hpp"
#include "QE/ElimSet.hpp"

namespace QE {

using Numeral = RealConstantType;
using R = RealTraits;

namespace AutoSimplifyingRealOps {

  inline TermList operator-(TermList s) { 
    return R::isNumeral(s) ? R::constantTl(-(*R::tryNumeral(s)))
         : s.isTerm() && R::isMinus(s.term()->functor()) 
                           ? s.term()->termArg(0)
                           : R::minus(s);
  }

  inline TermList operator*(Numeral k, TermList t) { 
    return  k == 0 ? R::constantTl(0) 
          : k == 1 ? t
          : k == -1 ? -t
          : R::mul(R::constantTl(k), t); }

  inline TermList operator+(TermList s, TermList t) { 
    return R::tryNumeral(s) == some(Numeral(0)) ? t
         : R::tryNumeral(t) == some(Numeral(0)) ? s
         : R::add(s, t);
  }

  inline TermList operator-(TermList s, TermList t) { return s + (-t); }

#define WRAPPING_OPERATOR(OP, ToWrap, Wrapped, wrap) \
  inline auto operator OP(ToWrap l, Wrapped r) { return wrap(l) OP r; } \
  inline auto operator OP(Wrapped l, ToWrap r) { return l OP wrap(r); } \

  WRAPPING_OPERATOR(+, Numeral, TermList, R::constantTl);
  WRAPPING_OPERATOR(-, Numeral, TermList, R::constantTl);

  WRAPPING_OPERATOR(+, int, TermList, Numeral);
  WRAPPING_OPERATOR(-, int, TermList, Numeral);

  WRAPPING_OPERATOR(+, int, Numeral, Numeral);
  WRAPPING_OPERATOR(-, int, Numeral, Numeral);
  WRAPPING_OPERATOR(*, int, Numeral, Numeral);


} // namespace AutoSimplifyingRealOps


struct LinBounds {
  TermList lower;
  Numeral delta;
  TermList upper() const { 
    using namespace AutoSimplifyingRealOps;
    return lower + delta; }
  auto asTuple() const { return std::tie(lower, delta); }
  friend std::ostream& operator<<(std::ostream& out, LinBounds const& self)
  { return out << "[" << self.lower << " (+ " << self.delta << ") ]"; }
  IMPL_COMPARISONS_FROM_TUPLE(LinBounds);
};

struct LiraTermSummary {
  RealConstantType slope;
  RealConstantType   off;
  RealConstantType   per;
  LinBounds  linBounds;
  TermList    lim;
  Recycled<Stack<ElimTerm>> breaks;
  friend std::ostream& operator<<(std::ostream& out, LiraTermSummary const& self)
  { return out << "LiraTermSummary {...}"; }

  TermList dist(bool plus) const { return plus ? linBounds.upper() : linBounds.lower; }

  auto upperLowerX(bool lowerYBound) const
  {
    using namespace AutoSimplifyingRealOps;
    ASS(off != 0)
    return lowerYBound ? // 0 = off x + lower
                     // x = -lower / off
                     (-1 / off) * linBounds.lower
                   : // 0 = off x + lower + delta
                     // x = -(lower + delta) / off
                     (-1 / off) * (linBounds.lower + linBounds.delta);

  }

  auto lowerX() const 
  { return upperLowerX(off < 0); }

  auto upperX() const 
  { return upperLowerX(off > 0); }

  auto deltaX() const {
    using namespace AutoSimplifyingRealOps;
    ASS(off != 0)
    return (1/off.abs()) * linBounds.delta;
  }

  void integrity() const {
    using namespace AutoSimplifyingRealOps;
    ASS(per >= 0)
    ASS(linBounds.delta >= 0)
  }

  static LiraTermSummary from(TermList var, TermList term);
};



class LIRA {
public:
  static Stack<ElimSet> computeElimSet(unsigned var, Stack<Literal*> const& conjunction);
  static IterTraits<VirtualIterator<ElimTerm>> iterElimSet(unsigned var, Literal* conjunction);
  static auto iterElimSet(unsigned var, Stack<Literal*> const& conjunction)
  {
    return arrayIter(conjunction)
      .flatMap([var](auto l) { return iterElimSet(var, l); });
  }
};

namespace CDVS {

struct ConflictDrivenVirtualSubstitution {
  static bool decide(Stack<Literal*> conj);
};

} // namespace CDVS


} // namespace QE

#endif // __QE_LIRA__
