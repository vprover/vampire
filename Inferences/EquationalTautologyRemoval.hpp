/**
 * @file EquationalTautologyRemoval.hpp
 * Defines class EquationalTautologyRemoval.
 */

#ifndef __EquationalTautologyRemoval__
#define __EquationalTautologyRemoval__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"

#include "DP/SimpleCongruenceClosure.hpp"

namespace Inferences {

class EquationalTautologyRemoval
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(EquationalTautologyRemoval);
  USE_ALLOCATOR(EquationalTautologyRemoval);

  EquationalTautologyRemoval() : _cc(nullptr) {}

  Clause* simplify(Clause* cl) override;
private:
  DP::SimpleCongruenceClosure _cc;
};

}

#endif // __EquationalTautologyRemoval__
