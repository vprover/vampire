/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __ProofProducingSATSolver__
#define __ProofProducingSATSolver__

#include "Lib/ScopedPtr.hpp"

#include "SATInference.hpp"
#include "SATSolver.hpp"

namespace SAT {

/**
 * A wrapper for solvers to track asserted premises and thereby reconstruct proofs.
 *
 * SAT solvers do not in general "remember" what they are given
 * and do not report this in e.g. DRAT proofs, so we have to remember ourselves.
 * This is actually a good thing, as we want to remember how we derived a certain clause ourselves.
 */
class ProofProducingSATSolver final : public SATSolver {
public:
  ProofProducingSATSolver() = default;
  explicit ProofProducingSATSolver(SATSolver *inner) :
    _inner(inner),
    _addedClauses(nullptr) {}

  void addClause(SATClause* cl) override
  {
    SATClauseList::push(cl,_addedClauses);
    _inner->addClause(cl);
  }

  VarAssignment getAssignment(unsigned var) override {
    return _inner->getAssignment(var);
  }

  bool isZeroImplied(unsigned var) override {
    return _inner->isZeroImplied(var);
  }

  void ensureVarCount(unsigned newVarCnt) override {
    _inner->ensureVarCount(newVarCnt);
  }

  unsigned newVar() override {
    return _inner->newVar();
  }

  void suggestPolarity(unsigned var, unsigned pol) override {
    _inner->suggestPolarity(var, pol);
  }

  void randomizeForNextAssignment(unsigned maxVar) override {
    _inner->randomizeForNextAssignment(maxVar);
  }

  Status solveUnderAssumptionsLimited(const SATLiteralStack &assumps, unsigned conflictCountLimit) override {
    return _inner->solveUnderAssumptionsLimited(assumps, conflictCountLimit);
  }

  SATLiteralStack failedAssumptions() override {
    return _inner->failedAssumptions();
  }

  // only to conform with SATSolver, would be a bit weird to call this
  SATClauseList *minimizePremises(SATClauseList *premises) override {
    return _inner->minimizePremises(premises);
  }

  // all premises ever added
  SATClauseList *premiseList() const { return _addedClauses; }

  /*
   * Returns only those premises required to get unsat from the last solve() call.
   * This may be a superset of those actually necessary depending on
   * how well the minimisation process goes.
   */
  SATClauseList *minimizedPremises() { return _inner->minimizePremises(_addedClauses); }

  /*
   * run CaDiCaL on `premiseList` to get a DRAT proof
   */
  SATClause *proof();

private:
  ScopedPtr<SATSolver> _inner;

  // to be used for the premises of a refutation
  SATClauseList* _addedClauses = nullptr;
};

}

#endif
