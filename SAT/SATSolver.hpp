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
   * Try to find another assignment which is likely to be different from the current one
   *
   * @pre Solver must be in SATISFIABLE status
   */
  virtual void randomizeAssignment() = 0;

  /**
   * If status is @c SATISFIABLE, return 0 if the assignment of @c var is
   * implied only by unit propagation (i.e. does not depend on any decisions)
   */
  virtual bool isZeroImplied(unsigned var) = 0;
  /**
   * Collect zero-implied literals.
   *
   * Can be used in SATISFIABLE and UNKNOWN state.
   *
   * @see isZeroImplied()
   */
  virtual void collectZeroImplied(SATLiteralStack& acc) = 0;

  virtual void ensureVarCnt(unsigned newVarCnt) {}

  void addAssumption(SATLiteral lit, bool onlyPropagate=false) {
    CALL("SATSolver::addAssumption(SATLiteral,bool)");
    addAssumption(lit, onlyPropagate ? 0 : UINT_MAX);
  }
  /**
   * Add an assumption into the solver. If conflictCountLimit==0,
   * do only unit propagation, if conflictCountLimit==UINT_MAX, do
   * full satisfiability check, and for values in between, restrict
   * the number of conflicts, and in case it is reached, stop with
   * solving and assign the status to UNKNOWN.
   */
  virtual void addAssumption(SATLiteral lit, unsigned conflictCountLimit) = 0;
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
