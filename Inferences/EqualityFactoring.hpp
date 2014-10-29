/**
 * @file EqualityFactoring.hpp
 * Defines class EqualityFactoring.
 */


#ifndef __EqualityFactoring__
#define __EqualityFactoring__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class EqualityFactoring
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(EqualityFactoring);
  USE_ALLOCATOR(EqualityFactoring);

  ClauseIterator generateClauses(Clause* premise);
private:
  struct IsPositiveEqualityFn;
  struct IsDifferentPositiveEqualityFn;
  struct FactorablePairsFn;
  struct ResultFn;

};


};

#endif /* __EqualityFactoring__ */
