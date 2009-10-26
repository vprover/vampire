/**
 * @file ForwardLiteralRewriting.hpp
 * Defines class ForwardLiteralRewriting.
 */


#ifndef __ForwardLiteralRewriting__
#define __ForwardLiteralRewriting__

#include "../Forwards.hpp"
#include "../Indexing/LiteralIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ForwardLiteralRewriting
: public ForwardSimplificationEngine
{
public:
  void attach(SaturationAlgorithm* salg);
  void detach();
  void perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer);
private:
  RewriteRuleIndex* _index;
};

};

#endif /* __ForwardLiteralRewriting__ */
