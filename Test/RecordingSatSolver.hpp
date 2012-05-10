/**
 * @file RecordingSatSolver.hpp
 * Defines class RecordingSatSolver.
 */

#ifndef __RecordingSatSolver__
#define __RecordingSatSolver__

#include "Forwards.hpp"

#include "Lib/ScopedPtr.hpp"

#include "SAT/SATSolver.hpp"



namespace Test {

using namespace SAT;

class RecordingSatSolver : public SATSolver {
public:
  RecordingSatSolver(SATSolver* inner) : _inner(inner) {}

  virtual void addClauses(SATClauseIterator cit, bool onlyPropagate=false) = 0;
  virtual Status getStatus() { return _inner->getStatus(); }
  virtual VarAssignment getAssignment(unsigned var) { return _inner->getAssignment(var); }

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

private:
  SATSolverSCP _inner;
};

}

#endif // __RecordingSatSolver__
