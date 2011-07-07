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
  GlobalSubsumption() : _index(0), _allowExtraAttachment(false) {}
  /**
   * The attach function must not be called when the constructor is used
   */
  GlobalSubsumption(GroundingIndex* idx, bool allowExtraAttachment=false)
  : _index(idx), _allowExtraAttachment(allowExtraAttachment) {}

  void attach(SaturationAlgorithm* salg);
  void detach();
  void perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer);
  Clause* perform(Clause* cl);
private:
  void addClauseToIndex(Clause* cl);


  GroundingIndex* _index;
  /**
   * If true, the attach and detach functions do nothing, so that the rule can
   * be attached to multiple saturation algorithms
   */
  bool _allowExtraAttachment;
};

};

#endif // __GlobalSubsumption__
