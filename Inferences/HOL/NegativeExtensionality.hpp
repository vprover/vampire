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
 * @file NegativeExtensionality.hpp
 * Defines class NegativeExtensionality.
 */

#ifndef __NegativeExtensionality__
#define __NegativeExtensionality__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;

class NegativeExtensionality
: public GeneratingInferenceEngine
{
public:
  ClauseIterator generateClauses(Clause* premise) override;
};

};

#endif /* __NegativeExtensionality__ */
