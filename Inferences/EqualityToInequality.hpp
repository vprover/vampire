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


#ifndef __EqualityToInequality__
#define __EqualityToInequality__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class EqualityToInequality
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(EqualityToInequality);
  USE_ALLOCATOR(EqualityToInequality);

  // carries out the following simple infernce
  // given a unit clause t1 = t2
  // where t1 = t + m  and t2 = s + n
  // it attempts to create clauses t != s
  // and $less(t, s) as appropriate
  // This inference dovetails with InequalityResolution

  ClauseIterator generateClauses(Clause* premise);
};


};

#endif /* __ArgCong__ */
