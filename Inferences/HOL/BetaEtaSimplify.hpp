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
 * @file BetaEtaSimplify.hpp
 * Defines class BetaEtaSimplify.
 */

#ifndef __BetaEtaSimplify__
#define __BetaEtaSimplify__

#include "Forwards.hpp"
#include "Inferences/InferenceEngine.hpp"

namespace Inferences {

class BetaEtaSimplify
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl) override;
};

};

#endif /* __BetaEtaSimplify__ */
