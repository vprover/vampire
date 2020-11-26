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
 * @file ShortConflictMetaDP.hpp
 * Defines class ShortConflictMetaDP.
 */

#ifndef __ShortConflictMetaDP__
#define __ShortConflictMetaDP__

#include "Forwards.hpp"

#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "SAT/SAT2FO.hpp"
#include "SAT/SATSolver.hpp"

#include "DecisionProcedure.hpp"


namespace DP {

using namespace Lib;
using namespace Kernel;
using namespace SAT;

class ShortConflictMetaDP : public DecisionProcedure {
public:
  CLASS_NAME(ShortConflictMetaDP);
  USE_ALLOCATOR(ShortConflictMetaDP);

  /**
   * Create object using @c inner decision procedure. Object takes ownership of the @c inner object.
   */
  ShortConflictMetaDP(DecisionProcedure* inner, SAT2FO& sat2fo, SATSolver& solver)
  : _inner(inner), _sat2fo(sat2fo), _solver(solver) {}

  virtual void addLiterals(LiteralIterator lits, bool onlyEqualites) override {
    CALL("ShortConflictMetaDP::addLiterals");
    _inner->addLiterals(lits, onlyEqualites);
  }

  virtual void reset() override {
    CALL("ShortConflictMetaDP::reset");
    _inner->reset();
    _unsatCores.reset();
  }

  virtual Status getStatus(bool getMultipleCores) override;

  void getModel(LiteralStack& model) override {
    _inner->getModel(model);
  }

  /**
   * Return number of unsatisfiable cores that can be retrieved.
   * 0 is returned if the status is SATISFIABLE or UNKNOWN. If UNSATISFIABLE,
   * number greater than zero is returned.
   *
   * Can be called only after getStatus before any next call to addLiterals.
   */
  virtual unsigned getUnsatCoreCount() override { return _unsatCores.size(); }
  virtual void getUnsatCore(LiteralStack& res, unsigned coreIndex) override;


private:
  unsigned getCoreSize(const LiteralStack& core);


  Stack<LiteralStack> _unsatCores;

  ScopedPtr<DecisionProcedure> _inner;
  SAT2FO& _sat2fo;
  SATSolver& _solver;
};

}

#endif // __ShortConflictMetaDP__
