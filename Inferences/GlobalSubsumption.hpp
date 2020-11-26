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
#include "Indexing/GroundingIndex.hpp"
#include "Shell/Options.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace SAT;

class GlobalSubsumption
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(GlobalSubsumption);
  USE_ALLOCATOR(GlobalSubsumption);

  GlobalSubsumption(const Options& opts) : _index(0),
      _uprOnly(opts.globalSubsumptionSatSolverPower()==Options::GlobalSubsumptionSatSolverPower::PROPAGATION_ONLY),
      _explicitMinim(opts.globalSubsumptionExplicitMinim()!=Options::GlobalSubsumptionExplicitMinim::OFF),
      _randomizeMinim(opts.globalSubsumptionExplicitMinim()==Options::GlobalSubsumptionExplicitMinim::RANDOMIZED),
      _splittingAssumps(opts.globalSubsumptionAvatarAssumptions()!= Options::GlobalSubsumptionAvatarAssumptions::OFF),
      _splitter(0) {}

  /**
   * The attach function must not be called when this constructor is used.
   */
  GlobalSubsumption(const Options& opts, GroundingIndex* idx) : GlobalSubsumption(opts) { _index = idx; }

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;
  
  Clause* perform(Clause* cl, Stack<Unit*>& prems);
 
private:  
  struct Unit2ClFn;
      
  GroundingIndex* _index;

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
    CALL("GlobalSubsumption::splitLevelToVar");
    unsigned* pvar;
              
    if(_splits2vars.getValuePtr(lev, pvar)) {
      SATSolver& solver = _index->getSolver();
      *pvar = solver.newVar();
      ALWAYS(_vars2splits.insert(*pvar,lev));
    }
    
    return *pvar;
  }  
  
  bool isSplitLevelVar(unsigned var, SplitLevel& lev) {
    CALL("GlobalSubsumption::isSplitLevelVar");
    
    return _vars2splits.find(var,lev);
  }
};

};

#endif // __GlobalSubsumption__
