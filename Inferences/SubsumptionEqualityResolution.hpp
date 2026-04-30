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

namespace Inferences {

/**
 * This inference tries to perform an equality resolution that only
 * succeeds if the resulting clause subsumes the premise. It is also
 * similar to subsumption resolution, but performs it with the equation
 * x = x that is only implicitly present in the search space.
 */
class SubsumptionEqualityResolution
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl) override;
};

};

#endif /* __SubsumptionEqualityResolution__ */
