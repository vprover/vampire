/**
 * @file InterpretedSimplification.hpp
 * Defines class InterpretedSimplification.
 */


#ifndef __InterpretedSimplification__
#define __InterpretedSimplification__

#include "../Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class InterpretedSimplification
: public ForwardSimplificationEngine
{
public:
  void perform(Clause* cl, bool& keep, ClauseIterator& toAdd);
};

};

#endif /* __InterpretedSimplification__ */
