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
#include "Lib/Allocator.hpp"

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


class TWLSolver : public SATSolverWithAssumptions {
  friend class ClauseDisposer;
  friend class VariableSelector;
  friend class RLCVariableSelector;
public:
  CLASS_NAME(TWLSolver);
  USE_ALLOCATOR(TWLSolver);

  TWLSolver(const Options& opt, bool generateProofs=false);
  ~TWLSolver();

  virtual void addClauses(SATClauseIterator cit);
  virtual Status solve(unsigned conflictCountLimit) override;
  
  /*
   * Because variables are integers greater than zero and we use them for indexing,
   * we always need one dummy variable slot for 0.
   * 
   * TODO: See whether the assumption about vars > 0 is essential in some way
   * and if not update everything accordingly to save this slot.
   */
  virtual void ensureVarCnt(unsigned newVarCnt);
  virtual void suggestPolarity(unsigned var, unsigned pol) override {
    CALL("TWLSolver::suggestPolarity");
    ASS_L(var,_varCnt);
    _lastAssignments[var] = pol;
  }
  virtual VarAssignment getAssignment(unsigned var);
  virtual bool isZeroImplied(unsigned var);
  virtual void collectZeroImplied(SATLiteralStack& acc);
  virtual SATClause* getZeroImpliedCertificate(unsigned var);

  virtual void addAssumption(SATLiteral lit);
  virtual void retractAllAssumptions();
  virtual bool hasAssumptions() const { return _assumptionsAdded; }

  virtual SATClause* getRefutation() {
    CALL("TWLSolver::getRefutation");
    ASS_EQ(_status,SATSolver::UNSATISFIABLE);
    return _refutation;
  }

  virtual void randomizeAssignment();

  void assertValid();
  void printAssignment();

  virtual void recordSource(unsigned satlit, Literal* lit);

private:

  void doSolving(unsigned conflictNumberLimit);

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

  bool isTrue(const SATLiteral& lit) const;
  bool isFalse(const SATLiteral& lit) const;
  bool isUndefined(const SATLiteral& lit) const;

  /** Return true iff variable @c var is undefined in the current assignment */
  bool isUndefined(unsigned var) const {
    ASS(var <= _varCnt);
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
  enum SatLoopResult {
    SLR_UNKNOWN,
    SLR_SATISFIABLE,
    SLR_CONFLICT_LIMIT_REACHED
  };
  SatLoopResult runSatLoop(unsigned conflictCountLimit);

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

  void getTwoHighestAssignmentLevels(SATClause* cl, unsigned& highestAL, unsigned& secondHighestAL);
  unsigned getBacktrackLevel(SATClause* conflictClause);
  unsigned getLearntBacktrackLevel(SATClause* conflictClause);

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

  bool _doLearntMinimization;
  bool _doLearntSubsumptionResolution;

  bool _generateProofs;
  SATClause* _refutation;

  Status _status;
//  DArray<AsgnVal> _assignment;
  DArray<PackedAsgnVal> _assignment;
  DArray<unsigned> _assignmentLevels;

  /**
   * For each var, if non-zero, contains clause that lead to the
   * assignment of the variable by unit propagation. If zero and
   * _assignmentLevels[var]==1, variable is an assumption, if
   * _assignmentLevels[var]>1, it is a choice point.
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
   * If false, _assumptionCnt==0, but the converse doesn't need to hold,
   * as the user assumptions might not have been put on the stack due
   * to redundancy. */
  bool _assumptionsAdded;
  /** Number of assumptions that are currently on the unit stack */
  unsigned _assumptionCnt;
  /**
   * Some unsatisfiable assumptions were added.
   *
   * This variable can be true even if @c _assumptionCnt is zero, since
   * conflicting assumptions aren't added on the unit stack.
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
  
  /**
   * Stack of added clauses
   * 
   * We remember them separately to delete them at the end.
  */
  SATClauseStack _addedClauses;

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
