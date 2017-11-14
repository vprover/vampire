
/*
 * File EqualityFactoring.hpp.
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
