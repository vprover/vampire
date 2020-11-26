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
  
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;
};

};

#endif // __InnerRewriting__
