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
 * @file RedexReducer.hpp
 */

#ifndef __RedexReducer__
#define __RedexReducer__

#include "Kernel/HOL/TermShifter.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Lib/SharedSet.hpp"

#include "Kernel/TermTransformer.hpp"

using namespace Kernel;

namespace RedexReducer {
  inline TermList reduce(TermList head, TermList arg) {
    ASS(head.isLambdaTerm());

    return holTermTransform(head.lambdaBody(),
      [arg](TermList t, unsigned lambdaLevel) {
        if (t.deBruijnIndex().isSome()) {
          unsigned index = t.deBruijnIndex().unwrap();
          if (index == lambdaLevel) {
            // any free indices in _t2 need to be lifted by the number of extra lambdas
            // that now surround them
            return lambdaLevel == 0 ? arg : TermShifter::shift(arg, lambdaLevel);
          }
          if (index > lambdaLevel) {
            // free index. replace by index 1 less as now surrounded by one fewer lambdas
            TermList sort = SortHelper::getResultSort(t.term());
            return HOL::getDeBruijnIndex(index - 1, sort);
          }
        }
        return t;
      },
      [](TermList orig, TermList newTerm, unsigned lambdaLevel) {
        // do not replace inside the substituted term, or in terms without any DB index
        // return orig == newTerm && newTerm.containsLooseDBIndex();
        return orig == newTerm && newTerm.freeDBIndices()->containsGreaterOrEqual(lambdaLevel);
      });
  }
}

#endif // __RedexReducer__
