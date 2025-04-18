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
 * @file GlobalSubsumption.hpp
 * Defines class GlobalSubsumption.
 */

#ifndef __GlobalSubsumption__
#define __GlobalSubsumption__

#include "Forwards.hpp"
#include "Shell/Options.hpp"
#include "Kernel/Grounder.hpp"
#include "SAT/SATSolver.hpp"

#include "InferenceEngine.hpp"

namespace Saturation { class Splitter; }

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace SAT;

class GlobalSubsumption : public ForwardSimplificationEngine
{
public:
  GlobalSubsumption(const Options& opts);

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;

  Clause* perform(Clause* cl, Stack<Unit*>& prems);
  virtual const char* name() const override { return "GlobalSubsumption"; }

private:
  struct Unit2ClFn;

  ScopedPtr<SATSolverWithAssumptions> _solver;
  ScopedPtr<GlobalSubsumptionGrounder> _grounder;

  /**
   * Call the SAT solver using the cheap, unit-propagation-only calls.
   */
  bool _uprOnly;

  /**
   * Explicitly minimize the obtained assumption set.
   */
  bool _explicitMinim;

  /**
   * Randomize order for explicit minimization.
   */
  bool _randomizeMinim;

  /**
   * Implement conditional GS when running with AVATAR.
   */
  bool _splittingAssumps;

  /*
   * GS needs a splitter when FULL_MODEL value is specified for the interaction with AVATAR.
   *
   * In fact, _splitter!=0 iff we want to do the FULL_MODEL option.
   */
  Splitter* _splitter;

  /**
   * A map binding split levels to variables assigned to them in our SAT solver.
   *
   * (Should this be rather a part of _index?)
   */
  DHMap<unsigned, unsigned> _splits2vars;

  /**
   * An inverse of the above map, for convenience.
   */
  DHMap<unsigned, unsigned> _vars2splits;

protected:
  unsigned splitLevelToVar(SplitLevel lev) {
    unsigned* pvar;

    if(_splits2vars.getValuePtr(lev, pvar)) {
      *pvar = _solver->newVar();
      ALWAYS(_vars2splits.insert(*pvar,lev));
    }

    return *pvar;
  }

  bool isSplitLevelVar(unsigned var, SplitLevel& lev) {
    return _vars2splits.find(var,lev);
  }
};

};

#endif // __GlobalSubsumption__
