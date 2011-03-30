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

class GroundingIndex {
public:
  GroundingIndex();

  SATSolver& getSolver() { return _solver; }

protected:
  virtual void handleClause(Clause* c, bool adding);

private:
  SATSolverSCP _solver;
};

}

#endif // __GroundingIndex__
