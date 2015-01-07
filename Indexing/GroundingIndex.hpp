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

  GroundingIndex(Grounder* gnd, const Options& opt);

  SATSolverWithAssumptions& getSolver() { return *_solver; }
  Grounder& getGrounder() { return *_grounder; }

protected:
  virtual void handleClause(Clause* c, bool adding);

private:
  ScopedPtr<SATSolverWithAssumptions> _solver;
  GrounderSCP _grounder;
};

}

#endif // __GroundingIndex__
