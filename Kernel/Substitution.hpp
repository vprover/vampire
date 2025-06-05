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
 * @file Substitution.hpp
 * Defines class Substitution.
 *
 * @since 08/07/2007 Manchester, flight Manchester-Cork
 * @since 30/12/2007 Manchester, reimplemented from scratch using a skip list like structure
 * @since 28/05/2025 Southampton, simplify, inline methods, conform to interfaces
 */

#ifndef __Substitution__
#define __Substitution__

#include "Lib/Allocator.hpp"
#include "Lib/DHMap.hpp"

#include "Term.hpp"

namespace Kernel {

/**
 * The class Substitution implementing substitutions.
 * @since 30/12/2007 Manchester
 *
 * This is a simple map from variables to terms.
 * If you want something with 'banks' to implement renaming variables apart, you probably want RobSubstitution.
 */
class Substitution
{
public:
  USE_ALLOCATOR(Substitution)

  /**
   * Bind `v` to `t`.
   * If v was already present, do nothing and return false.
   */
  bool bind(unsigned v, TermList t) { return _map.insert(v, t); }
  bool bind(unsigned int v, Term *t) { return bind(v, TermList(t)); }

  /**
   * Bind `v` to `t`, regardless of what was there before (if anything).
   */
  void rebind(unsigned v, TermList t) { _map.set(v,t); }
  void rebind(unsigned v, Term *t) { rebind(v, TermList(t)); }

  /**
   * If @c var is bound, assign binding into @c res and return true.
   * Otherwise return false and do nothing.
   */
  bool findBinding(unsigned v, TermList &out) const { return _map.find(v, out); }

  /**
   * Return result of application of the substitution to variable @c var
   *
   * This function is to allow use of the @c Substitution class in the
   * methods of the @c SubstHelper class for applying substitutions.
   */
  TermList apply(unsigned var) const {
    TermList res(var, false);
    findBinding(var, res);
    return res;
  }
  void specVar(unsigned var, TermList term) { ASSERTION_VIOLATION; }

  void reset() { _map.reset(); }
  bool isEmpty() const { return _map.isEmpty(); }
  unsigned size() const { return _map.size(); }

  friend std::ostream& operator<<(std::ostream& out, Substitution const &self) {
    out << '[';
    auto items = self._map.items();
    bool first = true;
    for(auto [x, t] : iterTraits(self._map.items())) {
      if(!first)
        out << ",";
      first = false;
      out << x << " -> " << t;
    }
    return out << ']';
  }

private:
  DHMap<unsigned,TermList> _map;
}; // class Substitution
} // namespace Kernel

#endif // __Substitution__

