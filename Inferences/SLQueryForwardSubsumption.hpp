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

class SLQueryForwardSubsumption
: public ForwardSimplificationEngine
{
public:
  void attach(SaturationAlgorithm* salg);
  void detach();
  void perform(Clause* cl, bool& keep, ClauseIterator& toAdd);
private:
  bool canBeMatched(unsigned baseLen, DArray<Literal*>& baseLits,
	  DArray<List<Literal*>*>& matches);

  Index* _index;
};

};

#endif /*__SLQueryForwardSubsumption__*/
