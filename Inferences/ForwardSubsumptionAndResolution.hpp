/**
 * @file ForwardSubsumptionAndResolution.hpp
 * Defines class ForwardSubsumptionAndResolution.
 */


#ifndef __ForwardSubsumptionAndResolution__
#define __ForwardSubsumptionAndResolution__


#include "../Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ForwardSubsumptionAndResolution
: public ForwardSimplificationEngine
{
public:
  void attach(SaturationAlgorithm* salg);
  void detach();
  void perform(Clause* cl, bool& keep, ClauseIterator& toAdd);
private:
  UnitClauseSimplifyingLiteralIndex* _unitIndex;
  FwSubsSimplifyingLiteralIndex* _fwIndex;
};


};

#endif /* __ForwardSubsumptionAndResolution__ */
