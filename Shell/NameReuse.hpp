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
#include "Lib/DHMap.hpp"

using namespace Kernel;

namespace Shell {

/**
 * Abstract base class: reuse "definition" terms used in place of formulae
 * Use for Skolemisation, naming, possibly others.
 */
class NameReuse {
public:
  // singleton: look at env.options and return a suitable policy for...
  // skolems
  static NameReuse *skolemInstance();
  // definitions
  static NameReuse *definitionInstance();

  // normalise `f` in some way to use as a key: saves recomputing it later
  virtual Formula *normalise(Formula *f) = 0;

  // try and reuse a symbol for `normalised`
  // false if not seen before
  // true (and symbol filled out) if we have
  virtual bool get(Formula *normalised, unsigned &symbol) = 0;

  // remember that we've used a symbol to stand for `normalised`
  virtual void put(Formula *normalised, unsigned symbol) = 0;

  // do we use formulae at all? - only false for NoNameReuse
  // allows skipping work sometimes
  virtual bool requiresFormula() { return true; };
};

/**
 * do not attempt to reuse definitions
 */
class NoNameReuse : public NameReuse {
public:
  CLASS_NAME(NoNameReuse)
  USE_ALLOCATOR(NoNameReuse)
  inline Formula *normalise(Formula *f) override { return nullptr; }
  inline bool get(Formula *normalised, unsigned &symbol) override { return false; }
  inline void put(Formula *normalised, unsigned symbol) override {}
  inline bool requiresFormula() override { return false; }
};

/**
 * reuse definitions if they match exactly
 */
class ExactNameReuse : public NameReuse {
public:
  CLASS_NAME(ExactNameReuse)
  USE_ALLOCATOR(ExactNameReuse)
  Formula *normalise(Formula *f) override;
  bool get(Formula *f, unsigned &symbol) override;
  void put(Formula *f, unsigned symbol) override;

private:
  DHMap<vstring, unsigned> _map;
};

} // namespace Shell

#endif