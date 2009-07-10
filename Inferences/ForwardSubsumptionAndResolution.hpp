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
  ForwardSubsumptionAndResolution(bool subsumptionResolution=true)
  : _subsumptionResolution(subsumptionResolution) {}

  void attach(SaturationAlgorithm* salg);
  void detach();
  void perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer);
private:
  UnitClauseSimplifyingLiteralIndex* _unitIndex;
  FwSubsSimplifyingLiteralIndex* _fwIndex;

  bool _subsumptionResolution;
};


};

#endif /* __ForwardSubsumptionAndResolution__ */
