
/*
 * File SLQueryForwardSubsumption.hpp.
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
 * @file SLQueryForwardSubsumption.hpp
 * Defines class SLQueryForwardSubsumption
 *
 */

#ifndef __SLQueryForwardSubsumption__
#define __SLQueryForwardSubsumption__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

/**
 * @deprecated Use ForwardSubsumptionAndResolution instead.
 */
class SLQueryForwardSubsumption
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(SLQueryForwardSubsumption);
  USE_ALLOCATOR(SLQueryForwardSubsumption);

  void attach(SaturationAlgorithm* salg);
  void detach();
  void perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer);
private:
  SimplifyingLiteralIndex* _index;
};

};

#endif /*__SLQueryForwardSubsumption__*/
