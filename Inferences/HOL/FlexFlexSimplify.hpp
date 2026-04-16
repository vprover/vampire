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
 * @file FlexFlexSimplify.hpp
 * Defines class FlexFlexSimplify.
 */

#ifndef __FlexFlexSimplify__
#define __FlexFlexSimplify__

#include "Inferences/InferenceEngine.hpp"

namespace Inferences {

class FlexFlexSimplify
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl) override;
};

};

#endif /* __FlexFlexSimplify__ */
