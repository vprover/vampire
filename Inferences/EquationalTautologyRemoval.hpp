
/*
 * File EquationalTautologyRemoval.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
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
