/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file SATSolver.hpp
 * Defines class SATSolver.
 */

#ifndef __SATSolver__
#define __SATSolver__

#include "SATLiteral.hpp"
#include "Lib/Random.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VirtualIterator.hpp"

#include <climits>

namespace SAT {

enum class VarAssignment {
  TRUE,
  FALSE,
  DONT_CARE,  // to represent partial models
  NOT_KNOWN
};

inline std::ostream& operator<<(std::ostream& out, VarAssignment const& a)
{
  switch (a)  {
    case VarAssignment::TRUE: return out << "TRUE";
    case VarAssignment::FALSE: return out << "FALSE";
    case VarAssignment::DONT_CARE: return out << "DONT_CARE";
    case VarAssignment::NOT_KNOWN: return out << "NOT_KNOWN";
    default: ASSERTION_VIOLATION; return  out << "INVALID STATUS";
  }
}

enum class Status {
  SATISFIABLE,
  UNSATISFIABLE,
  /**
   * Solving for just a bounded number of conflicts may return UNKNOWN.
   **/
  UNKNOWN
};

inline std::ostream& operator<<(std::ostream& out, Status const& s)
{
  switch (s)  {
    case Status::SATISFIABLE: return out << "SATISFIABLE";
    case Status::UNSATISFIABLE: return out << "UNSATISFIABLE";
    case Status::UNKNOWN: return out << "UNKNOWN";
    default: ASSERTION_VIOLATION; return  out << "INVALID STATUS";
  }
}

class SATSolver {
public:
  virtual ~SATSolver() = default;

  /**
   * Add a clause to the solver.
   *
   * In the clause each variable occurs at most once. (No repeated literals, no tautologies.)
   *
   * Memory-wise, the clause is NOT owned by the solver. Yet it shouldn't be destroyed while the solver lives.
   * TODO: This is not ideal and should be addressed! (reference counting?)
   */
  virtual void addClause(SATClause* cl) = 0;

  void addClausesIter(SATClauseIterator cit) {
    while (cit.hasNext()) {
      addClause(cit.next());
    }
  }

  /**
   * Solve under the given set of assumptions @b assumps.
   *
   * If UNSATISFIABLE is returned, a subsequent call to
   * failedAssumptions() returns a subset of these
   * that are already sufficient for the unsatisfiability.
   *
   * If conflictCountLimit==0,
   * do only unit propagation, if conflictCountLimit==UINT_MAX, do
   * full satisfiability check, and for values in between, restrict
   * the number of conflicts, and in case it is reached, stop with
   * solving and assign the status to UNKNOWN.
   *
   */
  virtual Status solveUnderAssumptionsLimited(const SATLiteralStack& assumps, unsigned conflictCountLimit) = 0;

  /**
   * Return a list of failed assumptions from the last solverUnderAssumptions call.
   * Assumes the last call returned UNSAT
   *
   * Usually corresponds to the solver's internal unsat core.
   */
  virtual SATLiteralStack failedAssumptions() = 0;

  // various shorthands for `solveUnderAssumptionsLimited`
  Status solveUnderAssumptions(const SATLiteralStack& assumps, bool onlyPropagate=false) {
    return solveUnderAssumptionsLimited(assumps, onlyPropagate ? 0u : UINT_MAX);
  }

  Status solveLimited(unsigned conflictCountLimit) {
    SATLiteralStack assumptions;
    return solveUnderAssumptionsLimited(assumptions, conflictCountLimit);
  }

  Status solve(bool onlyPropagate = false) {
    return solveLimited(onlyPropagate ? 0 : std::numeric_limits<unsigned>::max());
  }

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
   * Ensure that clauses mentioning variables 1..newVarCnt can be handled.
   *
   * See also newVar for a different (and conceptually incompatible)
   * way for managing variables in the solver.
   */
  virtual void ensureVarCount(unsigned newVarCnt) = 0;

  /**
   * Allocate a slot for a new (previously unused) variable in the solver
   * and return the variable.
   *
   * Variables start from 1 and keep increasing by 1.
   */
  virtual unsigned newVar() = 0;

  virtual void suggestPolarity(unsigned var, unsigned pol) = 0;

  /**
   * Suggest random polarity for variables up to maxVar (inclusive),
   * so that the next call to solver will tend to produce
   * a different model (provided the status will be satisfiable).
   */
  virtual void randomizeForNextAssignment(unsigned maxVar) {
    for (unsigned var=1; var <= maxVar; var++) {
      suggestPolarity(var,Random::getBit());
    }
  }

  /**
   * If status is @c SATISFIABLE, return assignment of variable @c var
   */
  bool trueInAssignment(SATLiteral lit)
  {
    VarAssignment asgn = getAssignment(lit.var());
    VarAssignment desired = lit.positive() ? VarAssignment::TRUE : VarAssignment::FALSE;
    return asgn==desired;
  }

  /**
   * Apply fixpoint minimization to already obtained failed assumption set
   * and return the result (as failedAssumptions).
   */
  SATLiteralStack explicitlyMinimizedFailedAssumptions(bool onlyPropagate=false, bool randomize = false) {
    return explicitlyMinimizedFailedAssumptions(onlyPropagate ? 0u : UINT_MAX, randomize);
  }

  SATLiteralStack explicitlyMinimizedFailedAssumptions(unsigned conflictCountLimit, bool randomize);

  /**
   * Assuming that the last solving call was unsatisfiable,
   * try to produce a minimal set of premises that it still unsatisfiable
   * (with respect to assumptions)
   *
   * `premises` should be all the clauses asserted so far:
   * usually you would get this from ProofProducingSATSolver.
   */
  virtual SATClauseList *minimizePremises(SATClauseList *premises) = 0;
};
}

#endif // __SATSolver__
