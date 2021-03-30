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
 * @file ExtensionalityResolution.hpp
 * Defines class ExtensionalityResolution
 *
 */

#ifndef __ExtensionalityResolution__
#define __ExtensionalityResolution__

#include "Forwards.hpp"

#include "Saturation/ExtensionalityClauseContainer.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;

/* NOTE / TODO:
 * the ExtensionalityResolution rule has not yet been updated
 *  to fully capitalize on vampire's support for polymorphism.
 *  In particular, opportunities to apply the rule are detected
 *  based on sort equality rather then sort unifyability.
 *  See, e.g. NegEqSortFn (for BackwardPairingFn),
 *  ExtensionalityClauseContainer::activeIterator (for ForwardPairingFn).
 **/

class ExtensionalityResolution
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(ExtensionalityResolution);
  USE_ALLOCATOR(ExtensionalityResolution);

  ExtensionalityResolution() {}
  
  ClauseIterator generateClauses(Clause* premise);

  static Clause* performExtensionalityResolution(
    Clause* extCl, Literal* extLit,
    Clause* otherCl, Literal* otherLit,
    RobSubstitution* subst,
    unsigned& counter,
    const Options& opts);
private:
  struct ForwardPairingFn;
  struct ForwardUnificationsFn;
  struct ForwardResultFn;

  struct NegEqSortFn;
  struct BackwardPairingFn;
  struct BackwardUnificationsFn;
  struct BackwardResultFn;
};

};

#endif /*__ExtensionalityResolution__*/
