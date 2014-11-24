/**
 * @file BackwardSubsumptionResolution.hpp
 * Defines class BackwardSubsumptionResolution.
 */


#ifndef __BackwardSubsumptionResolution__
#define __BackwardSubsumptionResolution__

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Indexing;

class BackwardSubsumptionResolution
: public BackwardSimplificationEngine
{
public:
  CLASS_NAME(BackwardSubsumptionResolution);
  USE_ALLOCATOR(BackwardSubsumptionResolution);

  BackwardSubsumptionResolution(bool byUnitsOnly) : _byUnitsOnly(byUnitsOnly) {}

  void attach(SaturationAlgorithm* salg);
  void detach();

  void perform(Clause* premise, BwSimplificationRecordIterator& simplifications);
private:
  struct ClauseExtractorFn;
  struct ClauseToBwSimplRecordFn;

  bool _byUnitsOnly;
  SimplifyingLiteralIndex* _index;
};

};

#endif /* __BackwardSubsumptionResolution__ */
