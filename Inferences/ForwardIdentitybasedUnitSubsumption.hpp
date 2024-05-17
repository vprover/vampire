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
 * @file ForwardIdentitybasedUnitSubsumption.hpp
 * Defines class ForwardIdentitybasedUnitSubsumption.
 */


#ifndef __ForwardIdentitybasedUnitSubsumption__
#define __ForwardIdentitybasedUnitSubsumption__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Indexing {
  class UnitHashingIndex;
}

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ForwardIdentitybasedUnitSubsumption
: public ForwardSimplificationEngine
{
public:
  ForwardIdentitybasedUnitSubsumption() : _units(0) {}

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;

private:
  /** The hashing index */
  Indexing::UnitHashingIndex* _units;
};


};

#endif /* __ForwardIdentitybasedUnitSubsumption__ */
