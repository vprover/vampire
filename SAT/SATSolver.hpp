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
  enum VarAssignment {
    TRUE,
    FALSE,
    DONT_CARE,
    NOT_KNOWN
  };
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
   *
   * A requirement is that in each clause, each variable occurrs at most once.
   */
  virtual void addClauses(SATClauseIterator cit, bool onlyPropagate=false) = 0;
  virtual Status getStatus() = 0;
  /**
   * If status is @c SATISFIABLE, return assignment of variable @c var
   */
  virtual VarAssignment getAssignment(unsigned var) = 0;

  /**
   * If status is @c SATISFIABLE, return 0 if the assignment of @c var is
   * implied only by unit propagation (i.e. does not depend on any decisions)
   */
  virtual bool isZeroImplied(unsigned var) = 0;

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

    VarAssignment asgn = getAssignment(lit.var());
    VarAssignment desired = lit.polarity() ? TRUE : FALSE;
    return asgn==desired;
  }

  /**
   * If status is @c SATISFIABLE, return assignment of variable @c var
   */
  bool falseInAssignment(SATLiteral lit)
  {
    CALL("SATSolver::trueInAssignment");

    VarAssignment asgn = getAssignment(lit.var());
    VarAssignment desired = lit.polarity() ? FALSE: TRUE;
    return asgn==desired;
  }
};

}

#endif // __SATSolver__
