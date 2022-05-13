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
 * @file FOOLParamodulation.hpp
 * Defines class FOOLParamodulation.
 */

#ifndef __CHAIN_UNROLLING__
#define __CHAIN_UNROLLING__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class ChainUnrolling : public ImmediateSimplificationEngine {
  public:
    CLASS_NAME(ChainUnrolling);
    USE_ALLOCATOR(ChainUnrolling);

    Clause* simplify(Clause* premise);

  private:
    TermList unroll(TermList term, int len); 
};

}

#endif
