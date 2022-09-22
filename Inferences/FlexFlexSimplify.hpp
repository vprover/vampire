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
 * @file CombinatorDemodISE.hpp
 * Defines class CombinatorDemodISE.
 */


#ifndef __FlexFlexSimplify__
#define __FlexFlexSimplify__

#if VHOL

#include "Forwards.hpp"
#include "InferenceEngine.hpp"
#include "Kernel/TermTransformer.hpp"

namespace Inferences {


class FlexFlexSimplify
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(FlexFlexSimplify);
  USE_ALLOCATOR(FlexFlexSimplify);

  Clause* simplify(Clause* cl);
};

};

#endif

#endif /* __BetaEtaSimplify__ */
