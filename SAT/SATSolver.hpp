/**
 * @file SATSolver.hpp
 * Defines class SATSolver.
 */

#ifndef __SATSolver__
#define __SATSolver__

#include "Lib/MaybeBool.hpp"

#include "SATLiteral.hpp"

namespace SAT {

class SATSolver {
public:
  enum Status {
    SATISFIABLE,
    UNSATISFIABLE,
    /**
     * This value is used when new clauses or assumptions are added to
     * the SAT solver, but the full saturation hasn't been performed
     */
    UNKNOWN
  };

  virtual ~SATSolver() {}

  /**
   * Can be called only when all assumptions are retracted
   */
  virtual void addClauses(SATClauseIterator cit, bool onlyPropagate=false) = 0;
  virtual Status getStatus() = 0;
  /**
   * If status is @c SATISFIABLE, return assignment of variable @c var
   */
  virtual MaybeBool getAssignment(unsigned var) = 0;
  virtual void ensureVarCnt(unsigned newVarCnt) {}

  virtual void addAssumption(SATLiteral lit, bool onlyPropagate=false) = 0;
  virtual void retractAllAssumptions() = 0;
  virtual bool hasAssumptions() const = 0;

  virtual SATClause* getRefutation() = 0;

  /**
   * If status is @c SATISFIABLE, return assignment of variable @c var
   */
  bool trueInAssignment(SATLiteral lit)
  {
    CALL("SATSolver::trueInAssignment");

    MaybeBool asgn = getAssignment(lit.var());

    return asgn.known() && asgn.value()==lit.polarity();
  }

  /**
   * If status is @c SATISFIABLE, return assignment of variable @c var
   */
  bool falseInAssignment(SATLiteral lit)
  {
    CALL("SATSolver::trueInAssignment");

    MaybeBool asgn = getAssignment(lit.var());

    return asgn.known() && asgn.value()!=lit.polarity();
  }
};

}

#endif // __SATSolver__
