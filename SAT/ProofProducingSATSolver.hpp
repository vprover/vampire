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
 * A convenience wrapper for solvers which do not track actual refutations
 * and so return the whole set of clauses added so far as refutations.
 */
class ProofProducingSATSolver final : public SATSolver {
public:
  ProofProducingSATSolver() = default;
  explicit ProofProducingSATSolver(SATSolver *inner, bool canMinimize) :
    _inner(inner),
    _addedClauses(0),
    _refutation(new(0) SATClause(0)),
    _refutationInference(new PropInference(SATClauseList::empty())),
    _canMinimize(canMinimize)
    {
      _refutation->setInference(_refutationInference);
    }

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

  SATClause* getRefutation()
  {
    // connect the added clauses ...
    SATClauseList* prems = _addedClauses;

    // ... with the current assumptions

    // TODO: the assumption set will be empty after a call to solveUnderAssumptions()
    // This does not matter much since refutations are only ever passed to collectFOPremises
    // and there are no FO premises of assumption inferences

    // So the below is commented out to prevent useless leaking

    /*
    for (size_t i=0; i < _assumptions.size(); i++) {
      SATClause* unit = new(1) SATClause(1);
      (*unit)[0] = _assumptions[i];
      unit->setInference(new AssumptionInference());
      SATClauseList::push(unit,prems);
    }
    */

    _refutationInference->setPremises(prems);

    return _refutation;
  }

  SATClauseList* getRefutationPremiseList() {
    return _canMinimize ? _addedClauses : nullptr;
  }

private:
  ScopedPtr<SATSolver> _inner;

  // to be used for the premises of a refutation
  SATClauseList* _addedClauses = nullptr;

  /**
   * Empty clause to be returned by the getRefutation call.
   * Recycled between consecutive getRefutation calls.
   */
  SATClause* _refutation = nullptr;
  /**
   * The inference inside _refutation.
   */
  PropInference* _refutationInference = nullptr;

  /**
   * Z3Interfacing cannot minimize its premises via Minisat because it's an SMT solver,
   * so we set this false for Z3.
   *
   * In that case we should return nullptr from getRefutationPremiseList (?!).
   * TODO make this neater.
   */
  bool _canMinimize = true;
};

}

#endif
