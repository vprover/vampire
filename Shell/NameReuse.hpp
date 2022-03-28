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
 * @file NameReuse.hpp
 * Attempt to reuse names introduced to represent formulae, e.g. Skolems or naming
 */

#ifndef __NameReuse__
#define __NameReuse__

#include "Forwards.hpp"
#include "Kernel/Renaming.hpp"
#include "Lib/DHMap.hpp"

using namespace Kernel;

namespace Shell {

/**
 * Reuse "definition" terms used in place of formulae.
 * Use for Skolemisation, naming, possibly others.
 */
class NameReuse {
public:
  CLASS_NAME(NameReuse)
  USE_ALLOCATOR(NameReuse)

  // singletons for...
  // skolems
  static NameReuse *skolemInstance();
  // definitions
  static NameReuse *definitionInstance();

  // convert `f` to a string in some way to use as a key
  vstring key(Formula *f);

  // try and reuse a symbol for `key`
  // false if not seen before
  // true (and symbol filled out) if we have
  bool get(const vstring &key, unsigned &symbol);

  // remember that we've used a symbol to stand for `key`
  void put(vstring key, unsigned symbol);

  // free variables in the order they occur in the key for `f`
  VirtualIterator<unsigned> freeVariablesInKeyOrder(Formula *f);

private:
  // convert `ts` to a string in some way to use as a key, writing into `buf`
  void key(vstringstream &buf, TermList ts);
  // convert `t`'s arguments to a string in some way to use as a key, writing into `buf`
  void key(vstringstream &buf, Term *t);

  // canonical renaming, reset in every call to key(Formula *)
  Renaming _renaming;

  // map from keys to ids
  DHMap<vstring, unsigned> _map;
};

} // namespace Shell

#endif