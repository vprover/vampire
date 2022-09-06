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


#ifndef __BetaSimplify__
#define __BetaSimplify__

#if VHOL

#include "Forwards.hpp"
#include "InferenceEngine.hpp"
#include "Kernel/TermTransformer.hpp"

namespace Inferences {


class BetaSimplify
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(BetaSimplify);
  USE_ALLOCATOR(BetaSimplify);

  Clause* simplify(Clause* cl);
};

};

#endif

#endif /* __CombinatorDemodISE__ */
