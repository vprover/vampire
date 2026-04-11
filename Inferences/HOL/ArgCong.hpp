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
 * @file ArgCong.hpp
 * Defines class ArgCong.
 */

#ifndef __ArgCong__
#define __ArgCong__

#include "Inferences/InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;

class ArgCong
: public GeneratingInferenceEngine
{
public:
  ArgCong(SaturationAlgorithm& salg) : _salg(salg) {}
  ClauseIterator generateClauses(Clause* premise) override;
private:
  const SaturationAlgorithm& _salg;
};

}

#endif /* __ArgCong__ */
