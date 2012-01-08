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
#include "Lib/Deque.hpp"
#include "Lib/Exception.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "SATLiteral.hpp"
#include "SATClause.hpp"
#include "SATSolver.hpp"

namespace SAT {

using namespace Lib;
using namespace Shell;

struct Watch
{
  Watch() {}
  Watch(SATClause* cl, SATLiteral blocker) : blocker(blocker), cl(cl)
  {
    CALL("Watch::Watch/2");
    ASS((*cl)[0]==blocker || (*cl)[1]==blocker);
  }
  SATLiteral blocker;
  SATClause* cl;
};

typedef Stack<Watch> WatchStack;


class TWLSolver : public SATSolver {
  friend class ClauseDisposer;
  friend class VariableSelector;
  friend class RLCVariableSelector;
public:
  TWLSolver(const Options& opt, bool generateProofs=false);
  ~TWLSolver();

  virtual void addClauses(SATClauseIterator cit, bool onlyPropagate);
  virtual Status getStatus() { return _status; };
  virtual void ensureVarCnt(unsigned newVarCnt);
  virtual VarAssignment getAssignment(unsigned var);

  virtual void addAssumption(SATLiteral lit, bool onlyPropagate);
  virtual void retractAllAssumptions();
  virtual bool hasAssumptions() const { return _assumptionsAdded; }

  virtual SATClause* getRefutation() { return _refutation; }

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
  typedef char PackedAsgnVal;

  WatchStack& getWatchStack(SATLiteral lit);
  WatchStack& getWatchStack(unsigned var, unsigned polarity);
  WatchStack& getTriggeredWatchStack(unsigned var, PackedAsgnVal assignment);

  bool isTrue(SATLiteral lit) const;
  bool isFalse(SATLiteral lit) const;
  bool isUndefined(SATLiteral lit) const;

  /** Return true iff variable @c var is undefined in the current assignment */
  bool isUndefined(unsigned var) const {
    return _assignment[var] == AS_UNDEFINED;
  }
  /** Return true iff variable @c var is true in the current assignment */
  bool isTrue(unsigned var) const {
    return _assignment[var] == AS_TRUE;
  }

  bool isFalse(SATClause* cl) const;
  bool isTrue(SATClause* cl) const;


  unsigned getAssignmentLevel(SATLiteral lit) const;
  unsigned getAssignmentLevel(unsigned var) const;


  unsigned selectTwoNonFalseLiterals(SATClause* cl) const;
  void addClause(SATClause* cl);
  void addUnitClause(SATClause* cl);

  void handleTopLevelConflict(SATClause* cl);
  void handleConflictingAssumption(SATLiteral assumpt);

  void backtrack(unsigned tgtLevel);

  void doBaseLevelPropagation();
  void runSatLoop();

  void setAssignment(unsigned var, unsigned polarity);

  void makeAssumptionAssignment(SATLiteral lit);
  void makeChoiceAssignment(unsigned var, unsigned polarity);
  void makeForcedAssignment(SATLiteral lit, SATClause* premise);
  void undoAssignment(unsigned var);

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

  ClauseVisitResult visitWatchedClause(Watch watch, unsigned var, unsigned& litIndex);

  SATClause* propagate(unsigned var);

  unsigned getBacktrackLevel(SATClause* conflictClause);

  void doSubsumptionResolution(SATLiteralStack& lits, SATClauseList*& premises);
  void doShallowMinimize(SATLiteralStack& lits, ArraySet& seenVars);
  void doDeepMinimize(SATLiteralStack& lits, ArraySet& seenVars, SATClauseList*& premises);
  bool isRedundant(SATLiteral lit, ArraySet& seenVars, SATClauseList*& premises);
  SATClause* getLearntClause(SATClause* conflictClause);

  void insertIntoWatchIndex(SATClause* cl);

  void recordClauseActivity(SATClause* cl);

  void recordVariableActivity(unsigned var);
  bool chooseVar(unsigned& var);

  void schedulePropagation(unsigned var);
  void resetPropagation();
  bool anythingToPropagate() { return _toPropagate.isNonEmpty(); }
  unsigned pickForPropagation();

  /** Unit-stack record */
  struct USRec
  {
    unsigned var;
    unsigned choice : 1;
    unsigned assumption : 1;

    USRec() {}
    USRec(unsigned var, bool choice, bool assumption=false)
    : var(var), choice(choice), assumption(assumption)
    {
      CALL("TWLSolver::USRec::USRec");
      ASS(!assumption || !choice);
    }

  };

  const Options& _opt;

  bool _generateProofs;
  SATClause* _refutation;

  Status _status;
//  DArray<AsgnVal> _assignment;
  DArray<PackedAsgnVal> _assignment;
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

  unsigned _varCnt;

  /** Level 1 is the first level which is not preceded by any choice point */
  unsigned _level;

  /** True it used added assumptions and they weren't retracted yet.
   * If false, _assumptionCnt==0, but te converse doesn't need to hold,
   * as the user assumptions might not have been put on the stack due
   * to redundancy. */
  bool _assumptionsAdded;
  /** Number of assumptions that are currently on the unit stack */
  unsigned _assumptionCnt;
  /**
   * Some unsatisfiable assumptions were added.
   *
   * This variable can be true even if @c _assumptionCnt is zero, since
   * conflicting assumtions aren't added on the unit stack.
   */
  bool _unsatisfiableAssumptions;

  /** truth values that were assigned to each variable most recently */
  DArray<PackedAsgnVal> _lastAssignments;

  /**
   * Stack of learnt clauses
   *
   * The most recently learn clauses are at the top
   */
  SATClauseStack _learntClauses;

  ArrayMap<EmptyStruct> _propagationScheduled;
  Deque<unsigned> _toPropagate;

  VariableSelectorSCP _variableSelector;
  RestartStrategySCP _restartStrategy;
  ClauseDisposerSCP _clauseDisposer;

  struct UnsatException : public Exception
  {
    UnsatException(SATClause* refutation=0) : refutation(refutation) {}
    SATClause* refutation;
  };

};

}

#endif /* __TWLSolver__ */
