/**
 * @file BufferedSolver.hpp
 * Defines class BufferedSolver.
 *
 * The idea is to buffer clauses that are true, or can be made true, by the ground model
 *
 * @author Giles
 */

#ifndef __BufferedSolver__
#define __BufferedSolver__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "SATSolver.hpp"

namespace SAT {

using namespace Lib;

class BufferedSolver : public SATSolver {
public:
  CLASS_NAME(BufferedSolver);
  USE_ALLOCATOR(BufferedSolver);

  BufferedSolver(SATSolver* inner);

  virtual SATClause* getRefutation() { return _inner->getRefutation(); }
  virtual void randomizeForNextAssignment(unsigned varLimit) override {
    _inner->randomizeForNextAssignment(varLimit);

    // This is not ideal, but we can't wait till solve, because
    // BufferedSolver would not be forced to consult inner if it already "has an assignment in mind"
    flushUnadded();
    _lastStatus = _inner->solve();
  }

  virtual void addClauses(SATClauseIterator cit);
  virtual Status solve(unsigned conflictCountLimit) override;
  virtual VarAssignment getAssignment(unsigned var);

  virtual bool isZeroImplied(unsigned var) {
    CALL("BufferedSolver::isZeroImplied");
    return (var > _maxVar) ? false : _inner->isZeroImplied(var);
  }
  virtual void collectZeroImplied(SATLiteralStack& acc) { _inner->collectZeroImplied(acc); }
  virtual SATClause* getZeroImpliedCertificate(unsigned var) { return _inner->getZeroImpliedCertificate(var); }

  virtual void ensureVarCnt(unsigned newVarCnt){ _inner->ensureVarCnt(newVarCnt);_tmaxVar=newVarCnt; }
  virtual void suggestPolarity(unsigned var,unsigned pol) override { _inner->suggestPolarity(var,pol); }
  virtual void recordSource(unsigned var, Literal* lit){
    _inner->recordSource(var,lit);
  }

private:

  // check if @cl is implied by current model, and record it
  // if we choose not to add it at this point
  bool checkAndRecordImplied(SATClause* cl);

  // Add any clauses that have been buffered to _inner and solve.
  void flushUnadded();

  SATSolverSCP _inner;

 /**
  * A buffer for new literals that do not yet appear in the solver
  */
  DHMap<unsigned, bool> _literalBuffer;

  /**
   * Clauses that have not been added to _inner as they are either implied by the assignment of _inner
   * or the variables implicitly set in _literalBuffer
   */
  SATClauseStack _unadded;
  
  /**
   * Index (to _unadded) of the least clause not yet checked wrt the current model.
   */ 
  unsigned _checkedIdx;

  /**
   * Remember the last status returned by solve.
   */
  Status _lastStatus;
  
 /**
  * The maximum variable added to the SATSolver, used to detect new variables
  *
  * Obviously relies on variable numbers being increasing 
  */
  unsigned _maxVar;
  // We use a temp to track the max added since last flush
  unsigned _tmaxVar;

};

}

#endif // __BufferedSolver__
