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
 * @file PrimitiveInstantiation.hpp
 * Defines class PrimitiveInstantiation.
 */

#ifndef __PrimitiveInstantiation__
#define __PrimitiveInstantiation__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Shell/Options.hpp"

namespace Inferences {

using namespace Kernel;

class PrimitiveInstantiation
: public GeneratingInferenceEngine
{
public:
  PrimitiveInstantiation(SaturationAlgorithm& salg);
  ClauseIterator generateClauses(Clause* premise) override;
private:
  const Shell::Options::PISet _piSet;
  TermStack _heads;
};

};

#endif /* __PrimitiveInstantiation__ */
