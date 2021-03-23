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
 * @file EqualityResolution.hpp
 * Defines class EqualityResolution.
 */


#ifndef __NegativeExt__
#define __NegativeExt__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "Shell/Options.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class NegativeExt
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(NegativeExt);
  USE_ALLOCATOR(NegativeExt);

  ClauseIterator generateClauses(Clause* premise);
private:
  struct ResultFn;
  struct IsNegativeEqualityFn;
};


};

#endif /* __NegativeExt__ */
