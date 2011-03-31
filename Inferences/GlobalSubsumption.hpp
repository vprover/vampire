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

class GlobalSubsumption
: public ForwardSimplificationEngine
{
public:
  void attach(SaturationAlgorithm* salg);
  void detach();
  void perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer);
private:
  bool addClauseToIndex(Clause* cl);

  GroundingIndex* _index;
};

};

#endif // __GlobalSubsumption__
