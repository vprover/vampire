/**
 * @file SATSolver.hpp
 * Defines class SATSolver.
 */

#ifndef __SATSolver__
#define __SATSolver__

#include "SATLiteral.hpp"

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
  /**
   * If status is @c SATISFIABLE, return assignment of variable @c var
   */
  virtual bool getAssignment(unsigned var) = 0;
  virtual void ensureVarCnt(unsigned newVarCnt) {}

  /**
   * If status is @c SATISFIABLE, return assignment of variable @c var
   */
  bool trueInAssignment(SATLiteral lit)
  {
    CALL("SATSolver::trueInAssignment");

    return getAssignment(lit.var())==lit.polarity();
  }
};

}

#endif // __SATSolver__
