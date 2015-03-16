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

  // TODO: since addClauses does not cause solve anymore, 
  // a simple addClause would be an option too (and arguably a simpler)
  
  /**
   * Can be called only when all assumptions are retracted
   *
   * A requirement is that in each clause, each variable occurs at most once.
   */
  virtual void addClauses(SATClauseIterator cit) = 0;
  
  /**
   * When a solver supports partial models (via DONT_CARE values in the assignment),
   * a partial model P computed must satisfy all the clauses added to the solver
   * via addClauses and there must be a full model extending P which also 
   * satisfies clauses added via addClausesIgnoredInPartialModel.
   * 
   * This is a default implementation of addClausesIgnoredInPartialModel 
   * for all the solvers which return total models
   * for which addClauses and addClausesIgnoredInPartialModel 
   * naturally coincide.
   */  
  virtual void addClausesIgnoredInPartialModel(SATClauseIterator cit) { addClauses(cit); }
  
  /**
   * Establish Status of the clause set inserted so far.
   * 
   * If conflictCountLimit==0,
   * do only unit propagation, if conflictCountLimit==UINT_MAX, do
   * full satisfiability check, and for values in between, restrict
   * the number of conflicts, and in case it is reached, stop with
   * solving and assign the status to UNKNOWN.
   */
  virtual Status solve(unsigned conflictCountLimit) = 0;
  
  Status solve(bool onlyPropagate=false) { return solve(onlyPropagate ? 0 : UINT_MAX); }
    
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
  /**
   * Return a valid clause that contains the zero-implied literal
   * and possibly the assumptions that implied it. Return 0 if @c var
   * was an assumption itself.
   * If called on a proof producing solver, the clause will have
   * a proper proof history.
   */
  virtual SATClause* getZeroImpliedCertificate(unsigned var) = 0;

  virtual void ensureVarCnt(unsigned newVarCnt) {}
  virtual void suggestPolarity(unsigned var, unsigned pol) {}
  virtual void forcePolarity(unsigned var, unsigned pol) {}

  virtual SATClause* getRefutation() = 0;

  /**
  * Record the association between a SATLiteral var and a Literal
  * In TWLSolver this is used for computing niceness values
  * 
  * TODO: an experimental hack; test it, and then either incorporate properly or remove
  */
  virtual void recordSource(unsigned satlitvar, Literal* lit) = 0;
  
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

class SATSolverWithAssumptions: 
      public SATSolver {
public:  
  // TODO: instead of storing assumptions internally,
  // consider just adding an overload of solve
  // with a set of assumptions as an argument
  
  // TODO: support for assumption UNSAT core (explicit minimisation on top?)
  
  /**
   * Add an assumption into the solver. 
   */
  virtual void addAssumption(SATLiteral lit) = 0;
  virtual void retractAllAssumptions() = 0;
  virtual bool hasAssumptions() const = 0;
};

}

#endif // __SATSolver__
