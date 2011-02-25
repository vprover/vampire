/**
 * @file SATSolver.hpp
 * Defines class SATSolver.
 */

#ifndef __SATSolver__
#define __SATSolver__

namespace SAT {

class SATSolver {
public:
  enum Status {
    SATISFIABLE,
    UNSATISFIABLE,
    TIME_LIMIT
  };

  virtual ~SATSolver() {}

  virtual void addClauses(SATClauseIterator cit) = 0;
  virtual Status getStatus() = 0;
  virtual void ensureVarCnt(unsigned newVarCnt) {}
};

}

#endif // __SATSolver__
