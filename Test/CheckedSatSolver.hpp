/**
 * @file CheckedSatSolver.hpp
 * Defines class CheckedSatSolver.
 */

#ifndef __CheckedSatSolver__
#define __CheckedSatSolver__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "SAT/SATClause.hpp"
#include "SAT/SATSolver.hpp"

namespace Test {

using namespace SAT;

class CheckedSatSolver : public SATSolver {
public:
  CLASS_NAME(CheckedSatSolver);
  USE_ALLOCATOR(CheckedSatSolver);
  
  CheckedSatSolver(SATSolver* inner);

  virtual SATClause* getRefutation() { 
    // TODO: consider checking the proof
    return _inner->getRefutation(); 
  }
  virtual void randomizeForNextAssignment(unsigned varLimit) override {
    _inner->randomizeForNextAssignment(varLimit); _checked = false;
  }

  virtual void addClause(SATClause* cl) override;
  virtual void addClauseIgnoredInPartialModel(SATClause* cl) override;
  virtual Status solve(unsigned conflictCountLimit) override;
  virtual VarAssignment getAssignment(unsigned var);
  virtual bool isZeroImplied(unsigned var) { return _inner->isZeroImplied(var); }
  virtual void collectZeroImplied(SATLiteralStack& acc) { _inner->collectZeroImplied(acc); }
  virtual SATClause* getZeroImpliedCertificate(unsigned var) { return _inner->getZeroImpliedCertificate(var); }
  virtual void ensureVarCount(unsigned newVarCnt) override;
  virtual void suggestPolarity(unsigned var,unsigned pol) override { _inner->suggestPolarity(var,pol); }

  // the interface of SATSolverWithAssumptions not needed now
  // virtual bool hasAssumptions() const { return _inner->hasAssumptions(); }
  // virtual void addAssumption(SATLiteral lit, unsigned conflictCountLimit);
  // virtual void retractAllAssumptions();

  virtual void recordSource(unsigned var, Literal* lit){
    _inner->recordSource(var,lit);
  }

private:

  bool isSatisfied(SATClause* cl);

  void ensureChecked() {
    CALL("CheckedSatSolver::ensureChecked");
    if(!_checked) {
      doCheck();
      _checked = true;
    }
  }

  void doCheck();

  SATSolverSCP _inner;

  bool _checked;
  unsigned _varCnt;

  DHMap<unsigned, bool> _assumptions;
  SATClauseStack _clauses;

};

}

#endif // __CheckedSatSolver__
