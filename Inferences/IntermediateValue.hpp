/*
 * File Induction 
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
 * @file Induction.hpp
 * Defines class Induction
 *
 */

#ifndef __IntermediateValue__
#define __IntermediateValue__

#include <math.h>

#include "Forwards.hpp"

#include "Kernel/TermTransformer.hpp"

#include "Indexing/LiteralIndex.hpp"

#include "Saturation/LimitClauseContainer.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Saturation;


class IntermediateValue
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(IntermediateValue);
  USE_ALLOCATOR(IntermediateValue);

  void attach(SaturationAlgorithm* salg);
  void detach();

  ClauseIterator generateClauses(Clause* premise);

private:

  ClauseIterator produceConsequences(TermList lhs, TermList rhs, TermList leftLimit, TermList nlTerm,
                      Clause* prem1, Clause* prem2, Clause* prem3, unsigned f1, unsigned f2);

  struct ValidRightHandSide;
  struct RightLimitExists;
  struct ResultFn;
  struct NotZero;
  
  IntermediateValueLimitClauseIndex* _leftLimitIndex;
};

};
#endif /*__IntermediateValue__*/
