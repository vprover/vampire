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
      _avatarAssumptions(opts.globalSubsumptionAvatarAssumptions()!= Options::GlobalSubsumptionAvatarAssumptions::OFF),
      _splitter(0) {}

  /**
   * The attach function must not be called when this constructor is used.
   */
  GlobalSubsumption(const Options& opts, GroundingIndex* idx) : GlobalSubsumption(opts) { _index = idx; }

  void attach(SaturationAlgorithm* salg);
  void detach();
  void perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer);
  Clause* perform(Clause* cl);
private:
  void addClauseToIndex(Clause* cl, SATLiteralStack& satLits);

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
  bool _avatarAssumptions;

  /*
   * GS needs a splitter when FULL_MODEL value is specified for the interaction with AVATAR.
   */
  Splitter* _splitter;
};

};

#endif // __GlobalSubsumption__
