/**
 * @file SLQueryForwardSubsumption.hpp
 * Defines class SLQueryForwardSubsumption
 *
 */

#ifndef __SLQueryForwardSubsumption__
#define __SLQueryForwardSubsumption__

#include "../Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

/**
 * @deprecated Use ForwardSubsumptionAndResolution instead.
 */
class SLQueryForwardSubsumption
: public ForwardSimplificationEngine
{
public:
  void attach(SaturationAlgorithm* salg);
  void detach();
  void perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer);
private:
  SimplifyingLiteralIndex* _index;
};

};

#endif /*__SLQueryForwardSubsumption__*/
