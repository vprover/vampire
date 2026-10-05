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
 * @file SymbolUsage.hpp
 * Answers questions about how the symbols of the signature are used by a set of clauses.
 */

#ifndef __SymbolUsage__
#define __SymbolUsage__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"

namespace Kernel {

using namespace Lib;

/**
 * Record in @c usedFunctions / @c usedPredicates which symbols occur in @c clauses.
 * Both arrays are (re)sized to the current signature and zeroed first, so a symbol
 * introduced after the call is simply out of range; see the note at the definition.
 *
 * Only presence is recorded, never a count, and that is what lets the traversal stop at a
 * subterm it has already seen: whether a symbol occurs somewhere below a shared term does
 * not depend on how many times that term occurs. So this walks the term DAG rather than
 * the tree it unfolds to. Anything wanting magnitudes needs a different traversal.
 */
void collectUsedSymbols(ClauseIterator clauses, DArray<bool>& usedFunctions, DArray<bool>& usedPredicates);

/**
 * How often each symbol of the signature occurs in a set of clauses.
 */
struct SymbolCounts {
  /** indexed by functor; an index past the end means a symbol younger than the count */
  DArray<unsigned> functions;
  DArray<unsigned> predicates;
  DArray<unsigned> typeCons;

  /**
   * Count occurrences in @c clauses: one per occurrence of a function or type constructor
   * as a subterm, one per occurrence of a non-equality literal for a predicate. All three
   * arrays are (re)sized to the current signature and zeroed first.
   *
   * Unlike collectUsedSymbols this must NOT skip a subterm it has already seen: the answer
   * is a multiplicity, so every occurrence of a shared term has to be counted again, once
   * for each way the term DAG reaches it. Adding a visited set here would silently change
   * every count on a problem with any sharing.
   *
   * The counting rule is the one Property::scan maintained as a side effect on
   * Signature::Symbol::usageCnt, so that callers moving off that counter keep their
   * behaviour.
   */
  void countIn(ClauseIterator clauses);

  /** false until countIn has run; see PrecedenceOrdering::symbolCounts() */
  bool isInitialised() const { return _initialised; }

private:
  bool _initialised = false;
};

}

#endif // __SymbolUsage__
