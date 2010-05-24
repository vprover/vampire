/**
 * @file SLQueryBackwardSubsumption.hpp
 * Defines class SLQueryBackwardSubsumption.
 */


#ifndef __BackwardDemodulation__
#define __BackwardDemodulation__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Indexing;
using namespace Kernel;

class BackwardDemodulation
: public BackwardSimplificationEngine
{
public:
  void attach(SaturationAlgorithm* salg);
  void detach();

  void perform(Clause* premise, BwSimplificationRecordIterator& simplifications);
private:
  struct RemovedIsNonzeroFn;
  struct RewritableClausesFn;
  struct ResultFn;

  DemodulationSubtermIndex* _index;
};

};

#endif /* __BackwardDemodulation__ */
