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
 * @file FastCondensation.hpp
 * Defines class FastCondensation
 *
 */

#ifndef __FastCondensation__
#define __FastCondensation__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

/**
 * Condensation simplification rule that performs only
 * condensations that are easy to check for.
 *
 * Literal L[X1,...XN] with variables X1,...,XN can be deleted,
 * if another literal in the clause is its instance L[t1,...tN]
 * such that each Xi either only appears in the deleted literal,
 * or ti=Xi.
 *
 * This condition ensures that matching the two above literals
 * will lead to change only in the literal that is being deleted.
 */
class FastCondensation
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(FastCondensation);
  USE_ALLOCATOR(FastCondensation);

  Clause* simplify(Clause* cl);
private:
  struct CondensationBinder;
};

};

#endif /*__FastCondensation__*/
