
/*
 * File Substitution.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
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

  /** Compose substitution 'this' with substitution 'other' such such that
   *  { sub.compose(other); term->apply(sub) } equals term->apply(sub)->apply(with).
   *
   *  Computationally, each mapping v -> term in 'this' is replaced with the mapping
   *  v -> term->apply(other). Every mapping v -> term in 'other' where v is
   *  unbound in 'this' is added to it.
   */
  void compose(Substitution& other);
  
#if VDEBUG
  vstring toString() const;
#endif
private:
  DHMap<unsigned,TermList> _map;
}; // class Substitution


}

#endif // __Substitution__

