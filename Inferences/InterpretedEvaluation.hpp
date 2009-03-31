/**
 * @file InterpretedEvaluation.hpp
 * Defines class InterpretedEvaluation.
 */


#ifndef __InterpretedEvaluation__
#define __InterpretedEvaluation__

#include "../Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class InterpretedEvaluation
: public ForwardSimplificationEngine
{
public:
  void perform(Clause* cl, bool& keep, ClauseIterator& toAdd);
};

};

#endif /* __InterpretedEvaluation__ */
