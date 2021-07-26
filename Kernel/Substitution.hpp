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
 * @since 30/12/2007 Manchester, reimplemented from scratch using a skip list
 * like structure
 */

#ifndef __Substitution__
#define __Substitution__

#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/VString.hpp"

#include "Lib/Allocator.hpp"

#include "Term.hpp"

namespace Kernel {

using namespace std;
using namespace Lib;

/**
 * The class Substitution implementing substitutions.
 * @since 30/12/2007 Manchester
 */
class Substitution
{
public:
  CLASS_NAME(Substitution);
  USE_ALLOCATOR(Substitution);
  DECLARE_PLACEMENT_NEW;

  Substitution() {}

  void bind(int v,Term* t);
  void bind(int v,TermList t);
  void rebind(int v, Term* t);
  void rebind(int v, TermList t);
  bool findBinding(int var, TermList& res) const;
  TermList apply(unsigned var);
  void unbind(int var);
  void reset();
  bool isEmpty() const { return _map.isEmpty(); }

  /** applies the function f to every term */
  template<class F> 
  void mapTerms(F f) 
  { return _map.mapValues(f); }

#if VDEBUG
  vstring toString() const;
#endif
  friend std::ostream& operator<<(std::ostream& out, Substitution const&);
private:
  DHMap<unsigned,TermList> _map;
}; // class Substitution


}

#endif // __Substitution__

