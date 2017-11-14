
/*
 * File FOOLParamodulation.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file FOOLParamodulation.hpp
 * Defines class FOOLParamodulation.
 */

#ifndef __FOOL_PARAMODULATION__
#define __FOOL_PARAMODULATION__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class FOOLParamodulation : public GeneratingInferenceEngine {
  public:
    CLASS_NAME(FOOLParamodulation);
    USE_ALLOCATOR(FOOLParamodulation);
    ClauseIterator generateClauses(Clause* premise);
};

}

#endif
