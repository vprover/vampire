/**
 * @file TWLSolver.hpp
 * Defines class TWLSolver of two-watched-literals SAT solver.
 */


#ifndef __TWLSolver__
#define __TWLSolver__

#include "Forwards.hpp"

#include "Lib/Array.hpp"
#include "Lib/ArrayMap.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Stack.hpp"

#include "SATSolver.hpp"

namespace SAT {

using namespace Lib;

class TWLSolver : public SATSolver {
public:
  TWLSolver();
  ~TWLSolver();

  virtual void addClauses(SATClauseIterator cit);
  virtual Status getStatus() { return _status; };
  virtual void ensureVarCnt(unsigned newVarCnt);

  void assertValid();
  void printAssignment();
private:

  enum AsgnVal {
    //the true and false value also correspond to positive
    //and negative literal polarity values
    AS_FALSE = 0u,
    AS_TRUE = 1u,
    AS_UNDEFINED = 2u
  };

  typedef Stack<SATClause*> WatchStack;

  WatchStack& getWatchStack(SATLiteral lit);
  WatchStack& getWatchStack(unsigned var, unsigned polarity);
  WatchStack& getTriggeredWatchStack(unsigned var, AsgnVal assignment);

  bool isTrue(SATLiteral lit) const;
  bool isFalse(SATLiteral lit) const;
  bool isUndefined(SATLiteral lit) const;
  bool isFalse(SATClause* cl) const;

  unsigned getAssignmentLevel(SATLiteral lit) const;


  unsigned selectTwoNonFalseLiterals(SATClause* cl) const;
  void addClause(SATClause* cl);
  void addUnitClause(SATClause* cl);

  void addMissingWatchLitClause(SATClause* cl);

  void backtrack(unsigned tgtLevel);

  void runSatLoop();

  void setAssignment(unsigned var, unsigned polarity);

  void makeChoiceAssignment(unsigned var, unsigned polarity);
  void makeForcedAssignment(SATLiteral lit, SATClause* premise);

  enum ClauseVisitResult {
    /** Visited clause is a conflict clause */
    VR_CONFLICT,
    /** Do nothing */
    VR_NONE,
    /** Propagate literal at @c litIndex position */
    VR_PROPAGATE,
    /** Replace the current watch by watching literal at @c litIndex position */
    VR_CHANGE_WATCH
  };

  ClauseVisitResult visitWatchedClause(SATClause* cl, unsigned var, unsigned& litIndex);

  SATClause* propagate(unsigned var);
  void propagateAndBacktrackIfNeeded(unsigned var);

  void incorporateUnprocessed();
  unsigned getBacktrackLevel(SATClause* conflictClause);
  SATClause* getLearntClause(SATClause* conflictClause);

  void insertIntoWatchIndex(SATClause* cl);

  void recordClauseActivity(SATClause* cl);
  void sweepLearntClauses();

  void recordVariableActivity(unsigned var);
  bool chooseVar(unsigned& var);

  void schedulePropagation(unsigned var);
  void resetPropagation();
  bool pickForPropagation(unsigned& var);

  /** Unit-stack record */
  struct USRec
  {
    unsigned var;
    unsigned choice : 1;
    unsigned mark : 1;
    unsigned markedIsDefining : 1;
    unsigned markTgtLevel : 29;
    USRec() {}
    USRec(unsigned var, bool choice, bool mark=false,
	    bool markedIsDefining=false, unsigned markTgtLevel=0)
    : var(var), choice(choice), mark(mark), markedIsDefining(markedIsDefining),
    markTgtLevel(markTgtLevel)
    {}

  };


  Status _status;
  DArray<AsgnVal> _assignment;
  DArray<unsigned> _assignmentLevels;

  /**
   * If a clause was determined at a choice point, its entry
   * is 0, otherwise it's the Clause that led to the assignment
   * by unit propagation.
   */
  DArray<SATClause*> _assignmentPremises;

  /**
   * Stack of assignment records.
   */
  Stack<USRec> _unitStack;
  /**
   * The two-watched-literals index.
   *
   * Invariant: each clause is either true,
   * or it's two watched literals are undefined.
   */
  DArray<WatchStack> _windex;

  /**
   * Clauses that aren't part of the _windex.
   *
   * These clauses can't be added until we backtrack to certain level.
   */
  DArray<SATClauseStack > _unprocessed;

  ZIArray<unsigned> _chosenVars;

  unsigned _varCnt;

  /** Level 1 is the first level which is not preceded by any choice point */
  unsigned _level;

  /** truth values that were assigned to each variable most recently */
  DArray<AsgnVal> _lastAssignments;

  DArray<unsigned> _variableActivity;

  SATClauseStack _learntClauses;

  ArrayMap<EmptyStruct> _propagationScheduled;
  Stack<unsigned> _toPropagate;

  unsigned _numberOfSurvivingLearntClauses;
  unsigned _numberOfSurvivingLearntClausesIncrease;

  class UnsatException : public Exception
  {};

};

}

#endif /* __TWLSolver__ */
