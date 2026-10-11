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
 * @file TermShifter.hpp
 */

#ifndef __TermShifter__
#define __TermShifter__

#include "Kernel/HOL/HOL.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Kernel/Term.hpp"

using namespace Kernel;

/**
 * The class TermShifter implements functionality to increment or decrement free de Bruijn indices
 * occurring in a given term.
 * A de Bruijn index is free, if it points "outside" the term.
 * For example, in the nameless term t = "(λ. f db_0) db_0", only the rightmost occurrence of db_0 is free.
 *
 * The shift function returns a pair consisting of the transformed term
 * as well the minimum free de Bruijn index found while traversing the term.
 *
 * Example:
 * TermTransformer::shift(t, 2) ~> { "(λ. f db_0) db_2", Option<unsigned>(0) }
 *
 * See also tHOL_TermShifter.cpp for accompanying unit tests of this class.
 */
namespace TermShifter
{
  // positive value -> shift up
  // negative -> shift down
  inline TermList shift(TermList term, int shiftBy) {
    return holTermTransform(term,
      [shiftBy](TermList t, unsigned lambdaLevel) {
        auto dbi = t.deBruijnIndex();
        if (dbi.isSome()) {
          unsigned index = dbi.unwrap();
          // free index. lift
          if (index >= lambdaLevel && shiftBy != 0) {
            TermList sort = SortHelper::getResultSort(t.term());
            ASS(shiftBy >= 0 || index >= std::abs(shiftBy));
            return HOL::getDeBruijnIndex(static_cast<int>(index) + shiftBy, sort);
          }
        }
        return t;
      },
      [](TermList orig, TermList newTerm) {
        // already shifted, so must be DB index and won't have subterms anyway
        return orig == newTerm && newTerm.containsLooseDBIndex();
      });
  }

  // returns the index of the minimal free DB index, otherwise UINT_MAX
  inline unsigned minFreeDBIndex(TermList t) {
    return t.freeDBIndices() ? t.freeDBIndices()->head() : UINT_MAX;
  }
};

#endif // __TermShifter__
