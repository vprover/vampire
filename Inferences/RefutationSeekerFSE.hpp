/**
 * @file RefutationSeekerFSE.hpp
 * Defines class RefutationSeekerFSE.
 */


#ifndef __RefutationSeekerFSE__
#define __RefutationSeekerFSE__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class RefutationSeekerFSE
: public ForwardSimplificationEngine
{
public:
  void attach(SaturationAlgorithm* salg);
  void detach();
  void perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer);
private:
  /** Simplification unit index */
  UnitClauseLiteralIndex* _index;
};

};
#endif /* __RefutationSeekerFSE__ */
