/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "SAT/SATSolver.hpp"
#include "Shell/Shuffling.hpp"

namespace SAT {

// TODO this could be done much more efficiently
SATLiteralStack SATSolver::explicitlyMinimizedFailedAssumptions(unsigned conflictCountLimit, bool randomize) {
  // assumes solveUnderAssumptions(...,conflictCountLimit,...) just returned UNSAT

  SATLiteralStack failed = failedAssumptions();
  unsigned sz = failed.size();

  if (!sz) { // a special case. Because of the bloody unsigned (see below)!
    return failed;
  }

  if (randomize) {
    // randomly permute the content of _failedAssumptionBuffer
    // not to bias minimization from one side or another
    Shell::Shuffling::shuffleArray(failed,sz);
  }

  SATLiteralStack assumptions;
  unsigned i = 0;
  while (i < sz) {
    assumptions.reset();
    // load all but i-th
    for (unsigned j = 0; j < sz; j++) {
      if (j != i) {
        assumptions.push(failed[j]);
      }
    }

    if (solveUnderAssumptionsLimited(assumptions, conflictCountLimit) == Status::UNSATISFIABLE) {
      // leave out forever by overwriting by the last one (buffer shrinks implicitly)
      failed[i] = failed[--sz];
    } else {
      // move on
      i++;
    }
  }

  failed.truncate(sz);
  return failed;
}

}
