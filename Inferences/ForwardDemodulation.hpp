/**
 * @file ForwardDemodulation.hpp
 * Defines class ForwardDemodulation
 *
 */

#ifndef __ForwardDemodulation__
#define __ForwardDemodulation__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ForwardDemodulation
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(ForwardDemodulation);
  USE_ALLOCATOR(ForwardDemodulation);

  void attach(SaturationAlgorithm* salg);
  void detach();
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;
private:
  bool _preorderedOnly;
  DemodulationLHSIndex* _index;
};

};

#endif /*__ForwardDemodulation__*/
