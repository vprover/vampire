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
 * @file PositiveExtensionality.hpp
 * Defines class PositiveExtensionality.
 */

#ifndef __PositiveExtensionality__
#define __PositiveExtensionality__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;

class PositiveExtensionality
: public GeneratingInferenceEngine
{
public:
  ClauseIterator generateClauses(Clause* premise) override;
};

};

#endif /* __PositiveExtensionality__ */
