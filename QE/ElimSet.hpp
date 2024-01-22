/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __QE_ElimSet__
#define __QE_ElimSet__


#include "Lib/Reflection.hpp"
#include "Lib/Stack.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/NumTraits.hpp"

namespace QE {

using namespace Kernel;
using namespace Lib;

// #define S_EPSILON "\u03B5"
//
// enum class Lim {
//   Infinity,
//   Epsilon,
// };
//
// inline std::ostream& operator<<(std::ostream& out, Lim const& self)
// { 
//   switch(self) {
//     // case Lim::Infinity: return out << "\u221E";
//     case Lim::Epsilon:  return out << "\u03B5";
//   } 
// }


struct Epsilon
{
  friend std::ostream& operator<<(std::ostream& out, Epsilon const& self)
  { return out << "\u03B5"; }
  auto asTuple() const { return std::tie(); }
  IMPL_COMPARISONS_FROM_TUPLE(Epsilon);
};

struct Period
{ 
  RealConstantType p; 
  explicit Period(RealConstantType p) : p(p) { ASS(p > 0) }
  friend std::ostream& operator<<(std::ostream& out, Period const& self)
  { return out << self.p << "\u2124"; }
  auto asTuple() const { return std::tie(p); }
  IMPL_COMPARISONS_FROM_TUPLE(Period);
};

enum class Sign { Plus, Minus, };

inline std::ostream& operator<<(std::ostream& out, Sign const& self)
{ 
  switch(self) {
    case Sign::Plus:  return out << "+";
    case Sign::Minus: return out << "-";
  } 
}

class FiniteElimTerm 
{
  TermList _term;
  Option<Epsilon> _epsilon;
  Option<Period> _period;
  friend class ElimTerm;
public: 
  FiniteElimTerm(TermList term, Option<Epsilon> epsilon, Option<Period> period) : _term(term), _epsilon(std::move(epsilon)), _period(std::move(period)) {  }
  Option<Period > const& period () const { return _period ; }
  Option<Epsilon> const& epsilon() const { return _epsilon; }
  friend FiniteElimTerm operator+(FiniteElimTerm t, Epsilon e);
  friend FiniteElimTerm operator+(FiniteElimTerm t, Period  p);
  explicit FiniteElimTerm(TermList term) : FiniteElimTerm(term, {}, {}) {  }
  TermList const& term() const { return _term; }

  friend std::ostream& operator<<(std::ostream& out, FiniteElimTerm const& self)
  { 
    bool first = true;
    auto output = [&](auto& x) { 
      if (first) { 
        first = false; 
        out << x; 
      } else {
        out << " + " << x;
      } 
    };
    if (!RealTraits::isZero(self._term)) {
      output(self._term);
    }
    if (self._epsilon.isSome()) { output(self._epsilon); }
    if (self._period.isSome()) { output(self._period); }
    if (first) { out << "0"; }
    return out; 
  }

  auto asTuple() const { return std::tie(_term, _epsilon, _period); }
  IMPL_COMPARISONS_FROM_TUPLE(FiniteElimTerm);
};

class MinusInfinity { 
  friend class ElimTerm; 
  friend std::ostream& operator<<(std::ostream& out, MinusInfinity const& self)
  { return out << "-\u221E"; }
  auto asTuple() const { return std::tie(); }
  IMPL_COMPARISONS_FROM_TUPLE(MinusInfinity);
};

class ElimTerm 
{
  Coproduct<FiniteElimTerm, MinusInfinity> _self;
public: 
  ElimTerm(FiniteElimTerm t) : _self(t) {}
  ElimTerm(MinusInfinity  t) : _self(t) {}
  Option<FiniteElimTerm const&> asFinite() const { return _self.template as<FiniteElimTerm>(); }
  bool                          isFinite() const { return _self.template is<FiniteElimTerm>(); }
  explicit ElimTerm(TermList term) : ElimTerm(FiniteElimTerm(term, {}, {})) {  }
  static ElimTerm minusInfinity() { return ElimTerm(FiniteElimTerm(RealTraits::zero(), {}, some(Period(RealConstantType(1))))); }
  // static ElimTerm minusInfinity() { return ElimTerm(MinusInfinity{}); }
  friend std::ostream& operator<<(std::ostream& out, ElimTerm const& self)
  { self._self.apply([&](auto& x) { out << x; }); return out; }
  auto asTuple() const { return std::tie(_self); }
  IMPL_COMPARISONS_FROM_TUPLE(ElimTerm);
};

inline FiniteElimTerm operator+(FiniteElimTerm t, Epsilon e) { return FiniteElimTerm(t.term(), some(e), t.period()); }
inline FiniteElimTerm operator+(FiniteElimTerm t, Period  p) { return FiniteElimTerm(t.term(), t.epsilon(), some(p)); }
inline ElimTerm operator+(ElimTerm t, Epsilon e) { ASS(t.isFinite()) return ElimTerm(*t.asFinite() + e); }
inline ElimTerm operator+(ElimTerm t, Period  p) { ASS(t.isFinite()) return ElimTerm(*t.asFinite() + p); }
inline ElimTerm operator+(TermList t, Epsilon e) { return ElimTerm(t) + e; }
inline ElimTerm operator+(TermList t, Period  p) { return ElimTerm(t) + p; }

class ElimSet {
  Stack<ElimTerm> _ts;
public:
  explicit ElimSet(Stack<ElimTerm> ts) : _ts(std::move(ts)) {}
  template<class Iter>
  static ElimSet fromIter(Iter iter) 
  { return ElimSet(iterTraits(std::move(iter)).template collect<Stack>()); }
  static ElimSet empty() { return ElimSet(Stack<ElimTerm>()); }
  friend std::ostream& operator<<(std::ostream& out, ElimSet const& self)
  { return out << self._ts; }

  ElimTerm const& operator[](unsigned i) const { return _ts[i]; }
  unsigned size() const { return _ts.size(); }
};

} // namespace QE

#endif // __QE_ElimSet__
