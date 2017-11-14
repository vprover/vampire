
/*
 * File GroundingIndex.hpp.
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
 * @file GroundingIndex.hpp
 * Defines class GroundingIndex.
 */

#ifndef __GroundingIndex__
#define __GroundingIndex__

#include "Forwards.hpp"

#include "Lib/ScopedPtr.hpp"

#include "SAT/SATSolver.hpp"

#include "Index.hpp"

namespace Indexing {

using namespace SAT;
using namespace Shell;

class GroundingIndex : public Index {
public:
  CLASS_NAME(GroundingIndex);
  USE_ALLOCATOR(GroundingIndex);

  GroundingIndex(const Options& opt);

  SATSolverWithAssumptions& getSolver() { return *_solver; }
  GlobalSubsumptionGrounder& getGrounder() { return *_grounder; }

protected:
  virtual void handleClause(Clause* c, bool adding);

private:
  ScopedPtr<SATSolverWithAssumptions> _solver;
  ScopedPtr<GlobalSubsumptionGrounder> _grounder;
};

}

#endif // __GroundingIndex__
