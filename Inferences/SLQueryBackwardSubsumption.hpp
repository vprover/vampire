/**
 * @file SLQueryBackwardSubsumption.hpp
 * Defines class SLQueryBackwardSubsumption.
 */


#ifndef __SLQueryBackwardSubsumption__
#define __SLQueryBackwardSubsumption__

#include "InferenceEngine.hpp"

namespace Inferences {

class SLQueryBackwardSubsumption
: public BackwardSimplificationEngine
{
public:
  void attach(SaturationAlgorithm* salg);
  void detach();

  void perform(Clause* premise, BwSimplificationRecordIterator& simplifications);
private:
  SimplifyingLiteralIndex* _index;
};

};

#endif /* __SLQueryBackwardSubsumption__ */
