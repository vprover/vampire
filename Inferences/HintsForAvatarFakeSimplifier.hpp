
/*
 * File HintsForAvatarFakeSimplifier.hpp.
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
 * @file HintsForAvatarFakeSimplifier.hpp
 * Defines class HintsForAvatarFakeSimplifier.
 */

#ifndef __HintsForAvatarFakeSimplifier__
#define __HintsForAvatarFakeSimplifier__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"

#include "Inferences/ForwardSubsumptionAndResolution.hpp"
#include "Saturation/ClauseContainer.hpp"

namespace Inferences {

class HintsForAvatarFakeSimplifier
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(HintsForAvatarFakeSimplifier);
  USE_ALLOCATOR(HintsForAvatarFakeSimplifier);

  HintsForAvatarFakeSimplifier();

  void addHintClause(Clause* cl) {
    _hintClauseContainer.add(cl);
  }

  Clause* simplify(Clause* cl) override;
private:
  ForwardSubsumptionAndResolutionImplementation _impl;
  Saturation::PlainClauseContainer _hintClauseContainer;
};

}

#endif // __HintsForAvatarFakeSimplifier__
