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
  enum VarAssignment {
    TRUE,
    FALSE,
    DONT_CARE,  // to represent partial models
    NOT_KNOWN
  };
  enum Status {
    SATISFIABLE,
    UNSATISFIABLE,
    /**
     * Solving for just a bounded number of conflicts may return UNKNOWN.
     **/
    UNKNOWN
  };

  virtual ~SATSolver() {}
  
  /**
   * Add a clause to the solver.
   *
   * In the clause each variable occurs at most once. (No repeated literals, no tautologies.)
   *
   * Memory-wise, the clause is NOT owned by the solver. Yet it shouldn't be destroyed while the solver lives.
   * TODO: This is not ideal and should be addressed! (reference counting?)
   */
  virtual void addClause(SATClause* cl) = 0;

  // TODO: rename to addClauses later on
  void addClausesIter(SATClauseIterator cit) {
    CALL("SATSolver::addClauses");
    while (cit.hasNext()) {
      addClause(cit.next());
    }
  }

  /**
   * When a solver supports partial models (via DONT_CARE values in the assignment),
   * a partial model P computed must satisfy all the clauses added to the solver
   * via addClause and there must be a full model extending P which also
   * satisfies clauses added via addClauseIgnoredInPartialModel.
   * 
   * This is a default implementation of addClauseIgnoredInPartialModel
   * for all the solvers which return total models
   * for which addClause and addClauseIgnoredInPartialModel
   * naturally coincide.
   */  
  virtual void addClauseIgnoredInPartialModel(SATClause* cl) { addClause(cl); }
  
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
   * If status is @c SATISFIABLE, return true if the assignment of @c var is
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

  /**
   * Ensure that clauses mentioning variables 1..newVarCnt can be handled.
   */
  virtual void ensureVarCount(unsigned newVarCnt) {}
  virtual void suggestPolarity(unsigned var, unsigned pol) = 0;

  /**
   * Suggest random polarity for variables up to maxVar (inclusive),
   * so that the next call to solver will tend to produce
   * a different model (provided the status will be satisfiable).
   */
  virtual void randomizeForNextAssignment(unsigned maxVar) {
    CALL("SATSolver::randomizeForNextAssignment");
    for (unsigned var=1; var <= maxVar; var++) {
      suggestPolarity(var,Random::getBit());
    }
  }

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
