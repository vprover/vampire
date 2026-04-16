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
 * @file ImitateProject.hpp
 * Defines class ImitateProject.
 */

#ifndef __ImitateProject__
#define __ImitateProject__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;

class ImitateProject
: public GeneratingInferenceEngine
{
public:
  ImitateProject(SaturationAlgorithm&) {}
  ClauseIterator generateClauses(Clause* premise) override;
};

}

#endif /* __ImitateProject__ */
