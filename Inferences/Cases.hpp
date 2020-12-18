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

#ifndef __Cases__
#define __Cases__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class Cases : public GeneratingInferenceEngine {
  public:
    CLASS_NAME(Cases);
    USE_ALLOCATOR(Cases);
    
    Clause* performParamodulation(Clause* cl, Literal* lit, TermList t);
    ClauseIterator generateClauses(Clause* premise);
    struct RewriteableSubtermsFn;
    struct ResultFn;
};

}

#endif
