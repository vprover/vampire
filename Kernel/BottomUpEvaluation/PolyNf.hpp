/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __BOTTOM_UP_EVALUATION__POLY_NF_HPP__
#define __BOTTOM_UP_EVALUATION__POLY_NF_HPP__

#include "Kernel/BottomUpEvaluation.hpp"

namespace Lib {

template<>
struct BottomUpChildIter<Kernel::PolyNf>
{
  struct PolynomialBottomUpChildIter 
  {
    Kernel::AnyPoly _self;
    decltype(_self.immediateSubterms()) _childIter;
    unsigned _nChildren;

    PolynomialBottomUpChildIter(Kernel::AnyPoly self) 
      : _self(std::move(self))
      , _childIter(_self.immediateSubterms())
      , _nChildren(_self.immediateSubterms().count())
    { }

    bool hasNext()        { return _childIter.hasNext(); }
    Kernel::PolyNf next() { return _childIter.next(); }

    unsigned nChildren() const
    { return _nChildren; }

    friend ostream& operator<<(ostream& out, PolynomialBottomUpChildIter const& self) 
    { return out << self._self; }
  };

  struct FuncTermBottomUpChildIter 
  {

    Kernel::FuncTerm _self;
    unsigned _idx;

    FuncTermBottomUpChildIter(Kernel::FuncTerm self) : _self(std::move(self)), _idx(0) {}

    bool hasNext() const
    { return _idx < _self.numTermArguments(); }

    Kernel::PolyNf next() 
    { return _self.arg(_idx++); }

    unsigned nChildren() const
    { return _self.numTermArguments(); }

    friend ostream& operator<<(ostream& out, FuncTermBottomUpChildIter const& self) 
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

    friend ostream& operator<<(ostream& out, VariableBottomUpChildIter const& self) 
    { return out << self._self; }
  };

  using Inner = Coproduct<FuncTermBottomUpChildIter, VariableBottomUpChildIter, PolynomialBottomUpChildIter>;
  Inner _self;

  BottomUpChildIter(Kernel::PolyNf self) : _self(self.match(
        [&](Kernel::FuncTerm self) { return Inner( FuncTermBottomUpChildIter(std::move(self))); },
        [&](Kernel::Variable self) { return Inner( VariableBottomUpChildIter(std::move(self))); },
        [&](Kernel::AnyPoly  self) { return Inner(PolynomialBottomUpChildIter(std::move(self))); }
      ))
  {}

  Kernel::PolyNf next() 
  { ALWAYS(hasNext()); return _self.apply([](auto& x) -> Kernel::PolyNf { return x.next(); }); }

  bool hasNext()
  { return _self.apply([](auto& x) { return x.hasNext(); }); }

  unsigned nChildren() const 
  { return _self.apply([](auto& x) { return x.nChildren(); }); }

  Kernel::PolyNf self() const 
  { return _self.apply([](auto& x) { return Kernel::PolyNf(x._self); }); }

  friend ostream& operator<<(ostream& out, BottomUpChildIter const& self) 
  { return out << self._self; }
};

} // namespace Lib

#endif//__BOTTOM_UP_EVALUATION__POLY_NF_HPP__
