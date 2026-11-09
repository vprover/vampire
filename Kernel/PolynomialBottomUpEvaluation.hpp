/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

/*
 * specialisation of BottomUpEvaluation for PolyNF
 *
 * see BottomUpEvaluation.hpp and Polynomial.hpp
 */

#ifndef __LIB__POLYNOMIAL_BOTTOM_UP_EVALUATION_HPP__
#define __LIB__POLYNOMIAL_BOTTOM_UP_EVALUATION_HPP__

#include "BottomUpEvaluation.hpp"
#include "Polynomial.hpp"

namespace Lib {
// specialisation for PolyNf
template<>
struct BottomUpChildIter<Kernel::PolyNf>
{
  struct PolynomialBottomUpChildIter
  {
    Kernel::AnyPoly _self;
    unsigned _idx1;
    unsigned _idx2;
    unsigned _nChildren;

    PolynomialBottomUpChildIter(Kernel::AnyPoly self) : _self(self), _idx1(0), _idx2(0), _nChildren(0)
    {
      while (_idx1 < _self.nSummands() && _self.nFactors(_idx1) == 0) {
        _idx1++;
      }
      for (unsigned i = 0; i < _self.nSummands(); i++) {
        _nChildren += self.nFactors(i);
      }
    }

    bool hasNext() const
    { return _idx1 < _self.nSummands(); }

    Kernel::PolyNf next()
    {
      auto out = _self.termAt(_idx1, _idx2++);
      if (_idx2 >= _self.nFactors(_idx1)) {
        _idx1++;
        while (_idx1 < _self.nSummands() && _self.nFactors(_idx1) == 0) {
          _idx1++;
        }
        _idx2 = 0;
      }
      return out;
    }

    unsigned nChildren() const
    { return _nChildren; }

    friend std::ostream& operator<<(std::ostream& out, PolynomialBottomUpChildIter const& self)
    { return out << self._self << "@(" << self._idx1 << ", " << self._idx2 << ")"; }
  };

  struct FuncTermBottomUpChildIter
  {

    Perfect<Kernel::FuncTerm> _self;
    unsigned _idx;

    FuncTermBottomUpChildIter(Perfect<Kernel::FuncTerm> self) : _self(self), _idx(0) {}

    bool hasNext() const
    { return _idx < _self->numTermArguments(); }

    Kernel::PolyNf next()
    { return _self->arg(_idx++); }

    unsigned nChildren() const
    { return _self->numTermArguments(); }

    friend std::ostream& operator<<(std::ostream& out, FuncTermBottomUpChildIter const& self)
    { return out << self._self << "@" << self._idx; }
  };


  struct VariableBottomUpChildIter
  {
    Kernel::Variable _self;
    VariableBottomUpChildIter(Kernel::Variable self) : _self(self) {}

    bool hasNext() const
    { return false; }

    Kernel::PolyNf next()
    { ASSERTION_VIOLATION }

    unsigned nChildren() const
    { return 0; }

    friend std::ostream& operator<<(std::ostream& out, VariableBottomUpChildIter const& self)
    { return out << self._self; }
  };

  using Inner = Coproduct<FuncTermBottomUpChildIter, VariableBottomUpChildIter, PolynomialBottomUpChildIter>;
  Inner _self;

  BottomUpChildIter(Kernel::PolyNf self, EmptyContext = EmptyContext()) : _self(self.match(
        [&](Perfect<Kernel::FuncTerm> self) { return Inner(FuncTermBottomUpChildIter( self ));            },
        [&](Kernel::Variable                  self) { return Inner(VariableBottomUpChildIter( self ));            },
        [&](Kernel::AnyPoly           self) { return Inner(PolynomialBottomUpChildIter(std::move(self))); }
      ))
  {}

  Kernel::PolyNf next(EmptyContext = EmptyContext())
  { ALWAYS(hasNext()); return _self.apply([](auto& x) -> Kernel::PolyNf { return x.next(); }); }

  bool hasNext(EmptyContext = EmptyContext()) const
  { return _self.apply([](auto& x) { return x.hasNext(); }); }

  unsigned nChildren(EmptyContext = EmptyContext()) const
  { return _self.apply([](auto& x) { return x.nChildren(); }); }

  Kernel::PolyNf self(EmptyContext = EmptyContext()) const
  { return _self.apply([](auto& x) { return Kernel::PolyNf(x._self); }); }

  friend std::ostream& operator<<(std::ostream& out, BottomUpChildIter const& self)
  { return out << self._self; }
};

} // namespace Lib


#endif
