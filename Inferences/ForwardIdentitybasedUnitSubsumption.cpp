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
 * @file ForwardIdentitybasedUnitSubsumption.cpp
 * Implements class ForwardIdentitybasedUnitSubsumption.
 */

#include "ForwardIdentitybasedUnitSubsumption.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/UnitHashingIndex.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

namespace Inferences {
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void ForwardIdentitybasedUnitSubsumption::attach(SaturationAlgorithm *salg)
{
  ForwardSimplificationEngine::attach(salg);
  _units = static_cast<UnitHashingIndex *>(
      _salg->getIndexManager()->request(UNIT_HASHING_INDEX));\
}

void ForwardIdentitybasedUnitSubsumption::detach()
{
  _units = 0;
  _salg->getIndexManager()->release(UNIT_HASHING_INDEX);
  ForwardSimplificationEngine::detach();
}

bool ForwardIdentitybasedUnitSubsumption::perform(Clause *cl, Clause *&replacement, ClauseIterator &premises)
{
  Clause* theOther = _units->getUnitLikeThis(cl,/* opposite = */ false);

  if (theOther) {
    premises = pvi(getSingletonIterator(theOther));
    // TODO: add statistics
    return true;
  }

  theOther = _units->getUnitLikeThis(cl,/* opposite = */ true);
  if (theOther) {
    replacement = new (0) Clause(0,SimplifyingInference2(InferenceRule::SUBSUMPTION_RESOLUTION, cl, theOther));
    premises = pvi(getSingletonIterator(theOther));
    // TODO: add statistics
    return true;
  }

  return false;
}

} // namespace Inferences
