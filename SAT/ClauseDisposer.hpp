
/*
 * File ClauseDisposer.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file ClauseDisposer.hpp
 * Defines class ClauseDisposer.
 */

#ifndef __ClauseDisposer__
#define __ClauseDisposer__

#include "Forwards.hpp"

#include "SATClause.hpp"
#include "TWLSolver.hpp"

namespace SAT {

/**
 * Class that is responsible for removal of learnt clauses in the SAT solver
 */
class ClauseDisposer
{
public:
  CLASS_NAME(ClauseDisposer);
  USE_ALLOCATOR(ClauseDisposer);

  typedef SATClause::ActivityType ActivityType;

  ClauseDisposer(TWLSolver& solver) : _solver(solver) {}
  virtual ~ClauseDisposer() {}

  /**
   * This is a point at which it is safe to remove learnt
   * clauses.
   */
  virtual void onRestart() {}
  /**
   * This is a point at which it is safe to remove learnt
   * clauses.
   */
  virtual void onSafeSpot() {}
  virtual void onNewInputClause(SATClause* cl) {}
  virtual void onConflict() {}
  virtual void onClauseInConflict(SATClause* cl) {}
protected:
  unsigned decisionLevel();
  unsigned varCnt() const;
  SATClauseStack& getLearntStack();
  DArray<WatchStack>& getWatchedStackArray();
  SATClause* getAssignmentPremise(unsigned var);

  void markAllRemovableUnkept();
  void removeUnkept();
  void keepMostActive(size_t numberOfKept, ActivityType minActivity);
  void keepBinary();

  TWLSolver& _solver;
};

/**
 * This class takes care of increasing clause activity, but doesn't
 * perform clause deletion
 */
class DecayingClauseDisposer : public ClauseDisposer
{
public:
  CLASS_NAME(DecayingClauseDisposer);
  USE_ALLOCATOR(DecayingClauseDisposer);

  DecayingClauseDisposer(TWLSolver& solver, ActivityType decayFactor = 1.001)
   : ClauseDisposer(solver), _decayFactor(decayFactor), _inc(1e-30) {}

  virtual void onConflict();

  virtual void onClauseInConflict(SATClause* cl) {
    cl->activity()+=_inc;
  }
protected:
  ActivityType _decayFactor;
  ActivityType _inc;
};

/**
 * Performs clause disposal according to the MiniSAT strategy
 *
 * We maintain phases of the run according to the number of conflicts. The length
 * of successive phases is always increased by 50%. Position in phase increases with
 * each conflict.
 *
 * We keep taget number of survivor clauses. Starting at zero, we increase this
 * number by one for each four learned clauses. Also, after each phase we increase
 * the number by 10%.
 *
 * When the number of learnt clauses is greater than the nmber of survivors, we
 * perform clause removal. We mark for removal the least active half of learnt
 * clauses, but we stop marking when we reach clauses with activity at least
 * @c _inc/learntCnt (_inc is the clause activity increment). When clauses are
 * marked for removal, we unmark binary clauses, and remove the clauses that
 * remained marked.
 */
class MinisatClauseDisposer : public DecayingClauseDisposer
{
public:
  CLASS_NAME(MinisatClauseDisposer);
  USE_ALLOCATOR(MinisatClauseDisposer);

  MinisatClauseDisposer(TWLSolver& solver, ActivityType decayFactor = 1.001f)
   : DecayingClauseDisposer(solver, decayFactor), _phaseIdx(0), _phaseLen(100), _clauseCntAcc(0), _survivorCnt(0) {}

  virtual void onNewInputClause(SATClause* cl);
  virtual void onSafeSpot();
  virtual void onConflict();
protected:

  size_t _phaseIdx;
  size_t _phaseLen;

  unsigned _clauseCntAcc;
  size_t _survivorCnt;
};

/**
 * Performs learnt clause disposal
 *
 * We ignore clauses of length less than three.
 *
 * At the end of each phase, clause removal is performed. The length of successive
 * phase is always increased by 50%. Position in phase increases with each conflict.
 *
 * We keep taget number of survivor clauses. Starting at zero, we increase this
 * number by one for each four learned clauses (only clauses of length greater than
 * two are counted).
 *
 * When the number of learnt clauses is greater than the nmber of survivors, we
 * perform clause removal. We mark for removal the least active half of learnt
 * clauses, but we stop marking when we reach clauses with activity at least
 * @c _inc/learntCnt (_inc is the clause activity increment). When clauses are
 * marked for removal, we unmark binary clauses, and remove the clauses that
 * remained marked.
 */
class GrowingClauseDisposer : public DecayingClauseDisposer
{
public:
  CLASS_NAME(GrowingClauseDisposer);
  USE_ALLOCATOR(GrowingClauseDisposer);

  GrowingClauseDisposer(TWLSolver& solver, ActivityType decayFactor = 1.001f)
   : DecayingClauseDisposer(solver, decayFactor), _phaseIdx(0), _phaseLen(100), _clauseCntAcc(0), _survivorCnt(0) {}

  virtual void onNewInputClause(SATClause* cl);
  virtual void onRestart();
  virtual void onConflict();
protected:

  size_t _phaseIdx;
  size_t _phaseLen;

  unsigned _clauseCntAcc;
  size_t _survivorCnt;
};

}

#endif // __ClauseDisposer__
