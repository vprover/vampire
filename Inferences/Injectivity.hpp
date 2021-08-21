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
 * @file Injectivty.hpp
 * Defines class Injectivty.
 */

#ifndef __Injectivity__
#define __Injectivity__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class Injectivity : public GeneratingInferenceEngine {
  public:
    CLASS_NAME(Injectivity);
    USE_ALLOCATOR(Injectivity);
    ClauseIterator generateClauses(Clause* premise);

  private:
  	TermList createNewLhs(TermList oldhead, TermStack& termArgs, unsigned index);
};

}

#endif
