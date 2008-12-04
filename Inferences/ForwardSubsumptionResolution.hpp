/**
 * @file ForwardSubsumptionResolution.hpp
 * Defines class ForwardSubsumptionResolution.
 */


#ifndef __ForwardSubsumptionResolution__
#define __ForwardSubsumptionResolution__


#include "../Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ForwardSubsumptionResolution
: public ForwardSimplificationEngine
{
public:
  void attach(SaturationAlgorithm* salg);
  void detach();
  void perform(Clause* cl, bool& keep, ClauseIterator& toAdd);
private:
  Index* _index;
};


};

#endif /* __ForwardSubsumptionResolution__ */
