/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "ProofProducingSATSolver.hpp"

#include "CadicalInterfacing.hpp"

namespace SAT {

SATClause *ProofProducingSATSolver::proof() {
#if VDEBUG
  for(SATClause *cl : iterTraits(_addedClauses->iter()))
    // should not be an empty clause in the input (?)
    ASS(cl->length())
#endif
  return CadicalInterfacing::proof(_addedClauses);
}

}
