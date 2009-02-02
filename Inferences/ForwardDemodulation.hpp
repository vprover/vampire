/**
 * @file ForwardDemodulation.hpp
 * Defines class ForwardDemodulation
 *
 */

#ifndef __ForwardDemodulation__
#define __ForwardDemodulation__

#include "../Forwards.hpp"
#include "../Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

/**
 * @deprecated Use ForwardSubsumptionAndResolution instead.
 */
class ForwardDemodulation
: public ForwardSimplificationEngine
{
public:
  void attach(SaturationAlgorithm* salg);
  void detach();
  void perform(Clause* cl, bool& keep, ClauseIterator& toAdd);
private:
  DemodulationLHSIndex* _index;
};

};

#endif /*__ForwardDemodulation__*/
