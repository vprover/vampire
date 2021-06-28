/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file LockedSolver.hpp
 *
 * LockedSolver: wrap a SAT solver instance with a coarse lock
 *
 * @author Michael
 */

#ifndef __LockedSolver__
#define __LockedSolver__

#include "Lib/Threading.hpp"

#if VTHREADED

namespace SAT {

class LockedSolver : public SATSolver {
public:
  CLASS_NAME(LockedSolver);
  USE_ALLOCATOR(LockedSolver);

  LockedSolver(SATSolver *inner) : _inner(inner) {}

  virtual SATClause *getRefutation() override {
    std::lock_guard<std::mutex> guard(_lock);
    return _inner->getRefutation();
  }

  virtual SATClauseList *getRefutationPremiseList() override {
    std::lock_guard<std::mutex> guard(_lock);
    return _inner->getRefutationPremiseList();
  }

  virtual void randomizeForNextAssignment(unsigned maxVar) override {
    std::lock_guard<std::mutex> guard(_lock);
    _inner->randomizeForNextAssignment(maxVar);
  }

  virtual void addClause(SATClause *cl) override {
    std::lock_guard<std::mutex> guard(_lock);
    _inner->addClause(cl);
  }

  virtual Status solve(unsigned conflictCountLimit) override {
    std::lock_guard<std::mutex> guard(_lock);
    return _inner->solve(conflictCountLimit);
  }

  virtual VarAssignment getAssignment(unsigned var) override {
    std::lock_guard<std::mutex> guard(_lock);
    return _inner->getAssignment(var);
  }

  virtual bool isZeroImplied(unsigned var) override
  {
    std::lock_guard<std::mutex> guard(_lock);
    return _inner->isZeroImplied(var);
  }

  virtual void collectZeroImplied(SATLiteralStack &acc) override {
    std::lock_guard<std::mutex> guard(_lock);
    _inner->collectZeroImplied(acc);
  }

  virtual SATClause * getZeroImpliedCertificate(unsigned var) override {
    std::lock_guard<std::mutex> guard(_lock);
    return _inner->getZeroImpliedCertificate(var);
  }

  virtual void ensureVarCount(unsigned newVarCnt) override {
    std::lock_guard<std::mutex> guard(_lock);
    _inner->ensureVarCount(newVarCnt);
  }

  virtual unsigned newVar() override {
    std::lock_guard<std::mutex> guard(_lock);
    return _inner->newVar();
  }

  virtual void suggestPolarity(unsigned var, unsigned pol) override {
    std::lock_guard<std::mutex> guard(_lock);
    _inner->suggestPolarity(var, pol);
  }

private:
  std::mutex _lock;
  SATSolverSCP _inner;
};
}; // namespace SAT

#endif

#endif