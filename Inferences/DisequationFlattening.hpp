/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#ifndef __DISEQUATION_FLATTENING_H__
#define __DISEQUATION_FLATTENING_H__

#include "InferenceEngine.hpp"

namespace Inferences {

class DisequationFlattening : public GeneratingInferenceEngine
{
public:
  CLASS_NAME(DisequationFlattening);
  USE_ALLOCATOR(DisequationFlattening);

  virtual ~DisequationFlattening();
  static bool eligibleForFlattening(Literal *l);
  ClauseIterator generateClauses(Clause* cl);
};

};

#endif /* __DISEQUATION_FLATTENING_H__ */
