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
 * @file RewritingByRule.hpp
 * Defines class RewritingByRule.
 */


#ifndef __RewritingByRule__
#define __RewritingByRule__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Inferences {

class DemodulationByRule
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(DemodulationByRule);
  USE_ALLOCATOR(DemodulationByRule);

  Clause* simplify(Clause* cl);
};

};

#endif /* __RewritingByRule__ */
