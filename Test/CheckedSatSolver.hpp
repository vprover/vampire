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
  CheckedSatSolver(SATSolver* inner);

  virtual Status getStatus() { ensureChecked(); return _inner->getStatus(); }
  virtual SATClause* getRefutation() { ensureChecked(); return _inner->getRefutation(); }
  virtual bool hasAssumptions() const { return _inner->hasAssumptions(); }
  virtual void randomizeAssignment() { _inner->randomizeAssignment(); _checked = false; ensureChecked(); }

  virtual void addClauses(SATClauseIterator cit, bool onlyPropagate=false);
  virtual VarAssignment getAssignment(unsigned var);
  virtual bool isZeroImplied(unsigned var) { return _inner->isZeroImplied(var); }
  virtual void collectZeroImplied(SATLiteralStack& acc) { _inner->collectZeroImplied(acc); }
  virtual SATClause* getZeroImpliedCertificate(unsigned var) { return _inner->getZeroImpliedCertificate(var); }
  virtual void ensureVarCnt(unsigned newVarCnt);

  virtual void addAssumption(SATLiteral lit, unsigned conflictCountLimit);
  virtual void retractAllAssumptions();

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
