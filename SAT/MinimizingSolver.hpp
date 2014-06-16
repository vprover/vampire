/**
 * @file MinimizingSolver.hpp
 * Defines class MinimizingSolver.
 */

#ifndef __MinimizingSolver__
#define __MinimizingSolver__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "SATSolver.hpp"



namespace SAT {

using namespace Lib;

class MinimizingSolver : public SATSolver {
public:
  MinimizingSolver(SATSolver* inner);

  virtual Status getStatus() { return _inner->getStatus(); }
  virtual SATClause* getRefutation() { return _inner->getRefutation(); }
  virtual bool hasAssumptions() const { return _inner->hasAssumptions(); }
  virtual void randomizeAssignment() { _inner->randomizeAssignment(); _assignmentValid = false; }


  virtual void addClauses(SATClauseIterator cit, bool onlyPropagate=false);
  virtual VarAssignment getAssignment(unsigned var);
  virtual bool isZeroImplied(unsigned var);
  virtual void collectZeroImplied(SATLiteralStack& acc) { _inner->collectZeroImplied(acc); }
  virtual SATClause* getZeroImpliedCertificate(unsigned var) { return _inner->getZeroImpliedCertificate(var); }

  virtual void ensureVarCnt(unsigned newVarCnt);

  virtual void addAssumption(SATLiteral lit, unsigned conflictCountLimit);
  virtual void retractAllAssumptions();

  virtual void recordSource(unsigned var, Literal* lit){
    _inner->recordSource(var,lit);
  }

private:

  static bool isNonEmptyClause(SATClause* cl);

  SATLiteral getMostSatisfyingTrueLiteral();
  void selectLiteral(SATLiteral lit);

  bool tryPuttingToAnExistingWatch(SATClause* cl);
  void putIntoIndex(SATClause* cl);

  void processInnerAssignmentChanges();
  void processUnprocessed();
  void updateAssignment();


  unsigned _varCnt;
  SATSolverSCP _inner;

  DHMap<unsigned, bool> _assumptions;

  /**
   * If true, _asgn assignment corresponds to the assignment in
   * the inner solver
   */
  bool _assignmentValid;


  /**
   * Clauses of which we yet need to ensure they are satisfied
   *
   * Invariant: outside of this object when _assignmentValid, the stack is empty.
   */
  SATClauseStack _unprocessed;

  /**
   * A total extension of the current assignment. A variable is
   * don't-care in the current assignment if its _watcher stack
   * is empty.
   */
  DArray<bool> _asgn;

  /**
   * Array of clauses kept satisfied by selecting or non-selecting
   * a particular variable
   *
   * The length of the array is _varCnt.
   */
  DArray<SATClauseStack> _watcher;

  /**
   * Number of unsatisfied clauses for each literal.
   *
   * The length of the array is _varCnt*2.
   */
  DArray<unsigned> _unsClCnt;

  /**
   * Not yet satisfied clauses indexed by their literals
   *
   * A clause appears once for every literal.
   * Index in the array translates as SatLiteral::content()
   *
   * The length of the array is _varCnt*2.
   */
  DArray<SATClauseStack> _clIdx;

  DHSet<SATClause*> _satisfiedClauses;

};

}

#endif // __MinimizingSolver__
