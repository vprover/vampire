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


#include "Lib/Stack.hpp"
#include "Kernel/Term.hpp"

namespace QE {

using namespace Kernel;
using namespace Lib;

enum class Lim {
  Infinity,
  Epsilon,
};

inline std::ostream& operator<<(std::ostream& out, Lim const& self)
{ 
  switch(self) {
    case Lim::Infinity: return out << "\u221E";
    case Lim::Epsilon:  return out << "\u03B5";
  } 
}

enum class Sign { Plus, Minus, };

inline std::ostream& operator<<(std::ostream& out, Sign const& self)
{ 
  switch(self) {
    case Sign::Plus:  return out << "+";
    case Sign::Minus: return out << "-";
  } 
}

class ElimTerm {

  TermList _term;
  Option<std::pair<Sign, Lim>> _lim;
  ElimTerm(TermList term, Sign s, Lim l) : _term(term), _lim(std::make_pair(s, l)) {  }
public: 
  explicit ElimTerm(TermList term) : _term(term), _lim() {  }
  friend ElimTerm operator+(TermList t, Lim l);
  friend ElimTerm operator-(TermList t, Lim l);
  TermList const& term() const { return _term; }
  Option<std::pair<Sign, Lim>> const& lim() const { return _lim; }
  friend std::ostream& operator<<(std::ostream& out, ElimTerm const& self)
  { 
    out << self._term; 
    if (self._lim.isSome()) { out << " " << self._lim->first << " " << self._lim->second; } 
    return out; 
  }
};

inline ElimTerm operator+(TermList t, Lim l) { return ElimTerm(t, Sign::Plus , l); }
inline ElimTerm operator-(TermList t, Lim l) { return ElimTerm(t, Sign::Minus, l); }

class ElimSet {
  Stack<ElimTerm> _ts;
public:
  explicit ElimSet(Stack<ElimTerm> ts) : _ts(std::move(ts)) {}
  static ElimSet empty() { return ElimSet(Stack<ElimTerm>()); }
  friend std::ostream& operator<<(std::ostream& out, ElimSet const& self)
  { return out << self._ts; }

  ElimTerm const& operator[](unsigned i) const { return _ts[i]; }
  unsigned size() const { return _ts.size(); }
};

} // namespace QE

#endif // __QE_ElimSet__
