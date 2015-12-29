/**
 * @file InnerRewriting.hpp
 * Defines class InnerRewriting.
 */

#ifndef __InnerRewriting__
#define __InnerRewriting__

#include "Forwards.hpp"
#include "Shell/Options.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Saturation;

class InnerRewriting
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(InnerRewriting);
  USE_ALLOCATOR(InnerRewriting);
  
  void perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer) override;
};

};

#endif // __InnerRewriting__
