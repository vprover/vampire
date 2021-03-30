/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Condensation.hpp
 * Defines class Condensation
 *
 */

#ifndef __Condensation__
#define __Condensation__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

/**
 * Condensation simplification rule.
 */
class Condensation
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(Condensation);
  USE_ALLOCATOR(Condensation);

  Clause* simplify(Clause* cl);
};

};

#endif /*__Condensation__*/
