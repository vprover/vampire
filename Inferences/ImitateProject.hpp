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


#ifndef __ImitateProject__
#define __ImitateProject__

#if VHOL

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "Shell/Options.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ImitateProject
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(ImitateProject);
  USE_ALLOCATOR(ImitateProject);

  ClauseIterator generateClauses(Clause* premise);
private:
  struct ResultFn;
  struct CanImitateAndProject;

};


};

#endif

#endif /* __ImitateProject__ */
