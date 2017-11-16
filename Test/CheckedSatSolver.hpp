
/*
 * File CheckedSatSolver.hpp.
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

  virtual SATClause* getRefutation() override {
    // TODO: consider checking the proof
    return _inner->getRefutation(); 
  }
  virtual SATClauseList* getRefutationPremiseList() override {
    return _inner->getRefutationPremiseList();
  }

  virtual void randomizeForNextAssignment(unsigned varLimit) override {
    _inner->randomizeForNextAssignment(varLimit); _checked = false;
  }

  virtual void addClause(SATClause* cl) override;
  virtual void addClauseIgnoredInPartialModel(SATClause* cl) override;
  virtual Status solve(unsigned conflictCountLimit) override;
  virtual VarAssignment getAssignment(unsigned var) override;
  virtual bool isZeroImplied(unsigned var) override { return _inner->isZeroImplied(var); }
  virtual void collectZeroImplied(SATLiteralStack& acc) override { _inner->collectZeroImplied(acc); }
  virtual SATClause* getZeroImpliedCertificate(unsigned var) override { return _inner->getZeroImpliedCertificate(var); }
  virtual void ensureVarCount(unsigned newVarCnt) override;

  virtual unsigned newVar() override {
    CALL("CheckedSatSolver::newVar");

    ALWAYS(_inner->newVar() == ++_varCnt);
    return _varCnt;
  }

  virtual void suggestPolarity(unsigned var,unsigned pol) override { _inner->suggestPolarity(var,pol); }

  // the interface of SATSolverWithAssumptions not needed now
  // virtual bool hasAssumptions() const { return _inner->hasAssumptions(); }
  // virtual void addAssumption(SATLiteral lit, unsigned conflictCountLimit);
  // virtual void retractAllAssumptions();

  virtual void recordSource(unsigned var, Literal* lit) override {
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
