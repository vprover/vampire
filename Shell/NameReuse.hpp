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
 * @file NameReuse.cpp
 * Defines definition-reuse policies, configured by an option
 */

#ifndef __NameReuse__
#define __NameReuse__

#include "Forwards.hpp"
#include "Shell/Rectify.hpp"
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

  // normalise `f` in some way to use as a key: saves recomputing it later
  Formula *normalise(Formula *f);

  // try and reuse a symbol for `normalised`
  // false if not seen before
  // true (and symbol filled out) if we have
  bool get(Formula *normalised, unsigned &symbol);

  // remember that we've used a symbol to stand for `normalised`
  void put(Formula *normalised, unsigned symbol);

private:
  DHMap<vstring, unsigned> _map;
};

} // namespace Shell

#endif