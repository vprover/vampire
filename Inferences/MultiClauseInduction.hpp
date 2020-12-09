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
 * @file MultiClauseInduction.hpp
 * Defines class MultiClauseInduction
 *
 */

#ifndef __MultiClauseInduction__
#define __MultiClauseInduction__

#include "Forwards.hpp"

#include "Indexing/TermIndex.hpp"
#include "Shell/InductionSchemeGenerator.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Saturation;

class MultiClauseInduction
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(MultiClauseInduction);
  USE_ALLOCATOR(MultiClauseInduction);

  MultiClauseInduction() = default;
  ClauseIterator generateClauses(Clause* premise) override;
  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

private:
  struct InductionClauseIterator;

  TermIndex* _index;
};

};

#endif /*__Induction__*/
