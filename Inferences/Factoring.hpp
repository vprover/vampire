/**
 * @file Factoring.hpp
 * Defines class Factoring.
 */


#ifndef __Factoring__
#define __Factoring__

#include "../Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class Factoring
: public GeneratingInferenceEngine
{
public:
  ClauseIterator generateClauses(Clause* premise);
};


};

#endif /* __Factoring__ */
