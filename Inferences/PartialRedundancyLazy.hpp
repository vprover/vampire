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
 * @file PartialRedundancyLazy.hpp
 * Defines class PartialRedundancyLazy
 *
 */

#ifndef __PartialRedundancyLazy__
#define __PartialRedundancyLazy__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class PartialRedundancyLazy
: public ForwardSimplificationEngine
{
public:
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;
};

};

#endif /*__PartialRedundancyLazy__*/
