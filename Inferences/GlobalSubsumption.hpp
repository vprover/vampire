/**
 * @file GlobalSubsumption.hpp
 * Defines class GlobalSubsumption.
 */

#ifndef __GlobalSubsumption__
#define __GlobalSubsumption__

#include "Forwards.hpp"
#include "Indexing/GroundingIndex.hpp"

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

  GlobalSubsumption(bool full) : _index(0), _allowExtraAttachment(false), _uprOnly(!full) {}
  /**
   * The attach function must not be called when the constructor is used
   */
  GlobalSubsumption(GroundingIndex* idx, bool full, bool allowExtraAttachment=false)
  : _index(idx), _allowExtraAttachment(allowExtraAttachment), _uprOnly(!full) {}

  void attach(SaturationAlgorithm* salg);
  void detach();
  void perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer);
  Clause* perform(Clause* cl);
private:
  void addClauseToIndex(Clause* cl, SATLiteralStack& satLits);

  GroundingIndex* _index;
  /**
   * If true, the attach and detach functions do nothing, so that the rule can
   * be attached to multiple saturation algorithms
   */
  bool _allowExtraAttachment;

  /**
   * Call the SAT solver using the cheap, unit-propagation-only calls.
   */
  bool _uprOnly;
};

};

#endif // __GlobalSubsumption__
