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
#include "Lib/DynamicHeap.hpp"
#include "Lib/ArrayMap.hpp"

#include "SATSolver.hpp"



namespace SAT {

using namespace Lib;

class MinimizingSolver : public SATSolver {
public:
  CLASS_NAME(MinimizingSolver);
  USE_ALLOCATOR(MinimizingSolver);

  MinimizingSolver(SATSolver* inner,bool splitclausesonly);

  virtual Status getStatus() { return _inner->getStatus(); }
  virtual SATClause* getRefutation() { return _inner->getRefutation(); }
  virtual bool hasAssumptions() const { return _inner->hasAssumptions(); }
  virtual void randomizeAssignment() { _inner->randomizeAssignment(); _assignmentValid = false; }

  virtual void addClauses(SATClauseIterator cit, bool onlyPropagate,bool useInPartialModel);
  virtual VarAssignment getAssignment(unsigned var);
  virtual bool isZeroImplied(unsigned var);
  virtual void collectZeroImplied(SATLiteralStack& acc) { _inner->collectZeroImplied(acc); }
  virtual SATClause* getZeroImpliedCertificate(unsigned var) { return _inner->getZeroImpliedCertificate(var); }

  virtual void ensureVarCnt(unsigned newVarCnt);
  virtual void suggestPolarity(unsigned var, unsigned pol) override { _inner->suggestPolarity(var,pol); }
  virtual void forcePolarity(unsigned var, unsigned pol) override { _inner->forcePolarity(var,pol); }

  virtual void addAssumption(SATLiteral lit, unsigned conflictCountLimit);
  virtual void retractAllAssumptions();

  virtual void recordSource(unsigned var, Literal* lit){
    _inner->recordSource(var,lit);
  }

private:
  static bool isNonEmptyClause(SATClause* cl);

  bool admitsDontcare(unsigned var) { 
    return _watcher[var].isEmpty() && !_inner->isZeroImplied(var);
    
    /**
     * TODO: as an optimization, the _watcher stack for isZeroImplied
     * vars could be reset. It will not be needed anymore.
     */
  }
  
  void selectVariable(unsigned var);

  bool tryPuttingToAnExistingWatch(SATClause* cl);
  void putIntoIndex(SATClause* cl);

  void processInnerAssignmentChanges();
  void processUnprocessedAndFillHeap();
  void updateAssignment();

  unsigned _varCnt;
  SATSolverSCP _inner;
  bool _splitclausesonly;

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
   * A total extension of the current assignment. 
   * The current assignment will report don't-care for those variables
   * for which admitsDontcare is true.
   * 
   * We define a literal "corresponding to variable var in _asgn"
   * as SATLiteral(var,_asgn[var]). Used below.
   */
  DArray<bool> _asgn;

  /**
   * Array of clauses made satisfied by giving up the don't-care value
   * for a particular variable and using the value dictated by _asgn instead.   
   *
   * The length of the array is _varCnt.
   */
  DArray<SATClauseStack> _watcher;

  typedef DArray<unsigned> CntArray;
  
  /**
   * Number of unsatisfied clauses for each literal
   * corresponding to a variable in _asgn.
   * 
   * Indexed by literal's var.
   *
   * The length of the array is _varCnt.
   */
  CntArray _unsClCnt;

  struct CntComparator
  {
    CntComparator(CntArray& ctr) : _ctr(ctr) {}

    Comparison compare(unsigned v1, unsigned v2)
    {
      // DynamicHeap is minimal and we want maximum, 
      // so we need to swap the arguments
      return Int::compare(_ctr[v2], _ctr[v1]);
    }
    CntArray& _ctr;
  };
  
  /**
   * Heap "on top of" _unsClCnt to facilitate fast "extract max" operation.
   * 
   * Heap is empty when _assignmentValid.
   */  
  DynamicHeap<unsigned, CntComparator, ArrayMap<size_t> > _heap;
  
  /**
   * Not yet satisfied clauses indexed by each variable
   * whose corresponding literal in _asgn can make the clause true.
   *
   * A clause appears once for every such literal.
   * All entries should be empty when _assignmentValid.
   *
   * The length of the array is _varCnt.
   */
  DArray<SATClauseStack> _clIdx;

  /**
   * A set of satisfied clauses. To correctly maintain
   * _unsClCnt, when there is more than one way to make clause
   * satisfied.
   */  
  DHSet<SATClause*> _satisfiedClauses;
  
};

}

#endif // __MinimizingSolver__
