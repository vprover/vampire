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
#include "Shell/Shuffling.hpp"

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
   * Establish Status of the clause set inserted so far.
   *
   * If conflictCountLimit==0,
   * do only unit propagation, if conflictCountLimit==UINT_MAX, do
   * full satisfiability check, and for values in between, restrict
   * the number of conflicts, and in case it is reached, stop with
   * solving and assign the status to UNKNOWN.
   *
   * TODO do this in terms of solveUnderAssumptions
   */
  virtual Status solveLimited(unsigned conflictCountLimit) = 0;

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
   * Solve under the given set of assumptions @b assumps.
   *
   * If UNSATISFIABLE is returned, a subsequent call to
   * failedAssumptions() returns a subset of these
   * that are already sufficient for the unsatisfiability.
   */
  virtual Status solveUnderAssumptionsLimited(const SATLiteralStack& assumps, unsigned conflictCountLimit) = 0;

  Status solveUnderAssumptions(const SATLiteralStack& assumps, bool onlyPropagate=false) {
    return solveUnderAssumptionsLimited(assumps,onlyPropagate ? 0u : UINT_MAX);
  }

  /**
   * Return a list of failed assumptions from the last solverUnderAssumptions call.
   * Assumes the last call returned UNSAT
   *
   * Usually corresponds to the solver's internal unsat core.
   */
  virtual SATLiteralStack failedAssumptions() = 0;

  /**
   * Apply fixpoint minimization to already obtained failed assumption set
   * and return the result (as failedAssumptions).
   */
  SATLiteralStack explicitlyMinimizedFailedAssumptions(bool onlyPropagate=false, bool randomize = false) {
    return explicitlyMinimizedFailedAssumptions(onlyPropagate ? 0u : UINT_MAX, randomize);
  }

  // TODO this could be done much more efficiently
  SATLiteralStack explicitlyMinimizedFailedAssumptions(unsigned conflictCountLimit, bool randomize) {
    // assumes solveUnderAssumptions(...,conflictCountLimit,...) just returned UNSAT

    SATLiteralStack failed = failedAssumptions();
    unsigned sz = failed.size();

    if (!sz) { // a special case. Because of the bloody unsigned (see below)!
      return failed;
    }

    if (randomize) {
      // randomly permute the content of _failedAssumptionBuffer
      // not to bias minimization from one side or another
      Shell::Shuffling::shuffleArray(failed,sz);
    }

    SATLiteralStack assumptions;
    unsigned i = 0;
    while (i < sz) {
      assumptions.reset();
      // load all but i-th
      for (unsigned j = 0; j < sz; j++) {
        if (j != i) {
          assumptions.push(failed[j]);
        }
      }

      if (solveUnderAssumptionsLimited(assumptions, conflictCountLimit) == Status::UNSATISFIABLE) {
        // leave out forever by overwriting by the last one (buffer shrinks implicitly)
        failed[i] = failed[--sz];
      } else {
        // move on
        i++;
      }
    }

    failed.truncate(sz);
    return failed;
  }
};
}

#endif // __SATSolver__
