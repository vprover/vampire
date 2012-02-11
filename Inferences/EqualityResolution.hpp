/**
 * @file EqualityResolution.hpp
 * Defines class EqualityResolution.
 */


#ifndef __EqualityResolution__
#define __EqualityResolution__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class EqualityResolution
: public GeneratingInferenceEngine
{
public:
  ClauseIterator generateClauses(Clause* premise);
  static Clause* tryResolveEquality(Clause* cl, Literal* toResolve);
private:
  struct ResultFn;
  struct IsNegativeEqualityFn;

};


};

#endif /* __EqualityResolution__ */
