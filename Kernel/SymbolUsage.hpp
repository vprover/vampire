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

}

#endif // __SymbolUsage__
