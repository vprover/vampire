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