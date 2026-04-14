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
 * @file SubsumptionEqualityResolution.hpp
 * Defines class SubsumptionEqualityResolution.
 */


#ifndef __SubsumptionEqualityResolution__
#define __SubsumptionEqualityResolution__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "Inferences/ProofExtra.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class SubsumptionEqualityResolution
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl) override;
};

using SubsumptionEqualityResolutionExtra = LiteralInferenceExtra;

};

#endif /* __SubsumptionEqualityResolution__ */
