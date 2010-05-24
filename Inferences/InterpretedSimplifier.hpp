/**
 * @file InterpretedSimplifier.hpp
 * Defines class InterpretedSimplifier.
 */

#ifndef __InterpretedSimplifier__
#define __InterpretedSimplifier__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Indexing;

class InterpretedSimplifier
: public ForwardSimplificationEngine
{
public:
  InterpretedSimplifier();
  ~InterpretedSimplifier();

  void attach(SaturationAlgorithm* salg);
  void detach();
  void perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer);
private:

  class ClauseSimplifier;

  ClauseSimplifier* _simpl;
  ArithmeticIndex* _ai;
};

}

#endif // __InterpretedSimplifier__
