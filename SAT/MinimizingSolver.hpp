
/*
 * File MinimizingSolver.hpp.
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
 * @file MinimizingSolver.hpp
 * 
 * Defines class MinimizingSolver which supports partial models.
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

class MinimizingSolver : public SATSolverWithAssumptions {
public:
  CLASS_NAME(MinimizingSolver);
  USE_ALLOCATOR(MinimizingSolver);

  MinimizingSolver(SATSolverWithAssumptions* inner);

  virtual SATClause* getRefutation() override { return _inner->getRefutation(); }
  virtual SATClauseList* getRefutationPremiseList() override {
    return _inner->getRefutationPremiseList();
  }
  virtual void randomizeForNextAssignment(unsigned maxVar) override {
    _inner->randomizeForNextAssignment(maxVar); _assignmentValid = false;
  }

  virtual void addClause(SATClause* cl) override;
  virtual void addClauseIgnoredInPartialModel(SATClause* cl) override;
  virtual Status solve(unsigned conflictCountLimit) override;
  
  virtual VarAssignment getAssignment(unsigned var) override;
  virtual bool isZeroImplied(unsigned var) override;
  virtual void collectZeroImplied(SATLiteralStack& acc) override { _inner->collectZeroImplied(acc); }
  virtual SATClause* getZeroImpliedCertificate(unsigned var) override { return _inner->getZeroImpliedCertificate(var); }

  virtual void ensureVarCount(unsigned newVarCnt) override;

  void addAssumption(SATLiteral lit) override {
    _inner->addAssumption(lit);
  }
  void retractAllAssumptions() override {
    _inner->retractAllAssumptions();
  }
  bool hasAssumptions() const override {
    return _inner->hasAssumptions();
  }
  Status solveUnderAssumptions(const SATLiteralStack& assumps, unsigned conflictCountLimit, bool b) override {
    return _inner->solveUnderAssumptions(assumps,conflictCountLimit,b);
  }
  // because SATSolverWithAssumptions is not just an interface, now MinimizingSolver actually has it's own _failedAssumptionBuffer, but we wan't to use _inner's
  const SATLiteralStack& failedAssumptions() override {
    return _inner->failedAssumptions();
  }

  virtual unsigned newVar() override {
    CALL("MinimizingSolver::newVar");
    unsigned oldVC = _varCnt;
    ensureVarCount(_varCnt+1);
    ASS_EQ(_varCnt,oldVC+1);
    return _varCnt;
  }

  virtual void suggestPolarity(unsigned var, unsigned pol) override { _inner->suggestPolarity(var,pol); }
  virtual void recordSource(unsigned var, Literal* lit) override {
    _inner->recordSource(var,lit);
  }

private:
  bool admitsDontcare(unsigned var) { 
    CALL("MinimizingSolver::admitsDontcare");
    ASS_G(var,0); ASS_LE(var,_varCnt);

    return _watcher[var].isEmpty() && !_inner->isZeroImplied(var);
    
    /**
     * TODO: as an optimization, the _watcher stack for zero implied variables
     * could be reset. It will not be needed anymore.
     */
  }
  
  void selectVariable(unsigned var);

  bool tryPuttingToAnExistingWatch(SATClause* cl);
  void putIntoIndex(SATClause* cl);

  void processInnerAssignmentChanges();
  void processUnprocessedAndFillHeap();
  void updateAssignment();

  unsigned _varCnt;
  ScopedPtr<SATSolverWithAssumptions> _inner;

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
