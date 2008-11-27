/**
 * @file AtomicClauseForwardSubsumption.hpp
 * Defines class AtomicClauseForwardSubsumption
 *
 */

#ifndef __AtomicClauseForwardSubsumption__
#define __AtomicClauseForwardSubsumption__

#include "../Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class AtomicClauseForwardSubsumption
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

#endif /*__AtomicClauseForwardSubsumption__*/
