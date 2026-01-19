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
#include "Kernel/Grounder.hpp"
#include "SAT/ProofProducingSATSolver.hpp"

#include "InferenceEngine.hpp"

namespace Saturation { class Splitter; }

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace SAT;

// TODO consider making this an ImmediateSimplificationEngine if it really doesn't depend on any indices
class GlobalSubsumption : public ForwardSimplificationEngine
{
public:
  GlobalSubsumption(SaturationAlgorithm& salg);

  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;

  Clause* perform(Clause* cl, Stack<Unit*>& prems);

private:
  struct Unit2ClFn;

  ScopedPtr<ProofProducingSATSolver> _solver;
  ScopedPtr<GlobalSubsumptionGrounder> _grounder;

  /**
   * Randomize order for explicit minimization.
   */
  bool _randomizeMinim;

  /**
   * A map binding split levels to variables assigned to them in our SAT solver.
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
