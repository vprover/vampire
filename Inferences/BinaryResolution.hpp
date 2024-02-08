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
 * @file BinaryResolution.hpp
 * Defines class BinaryResolution
 *
 */

#ifndef __BinaryResolution__
#define __BinaryResolution__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class BinaryResolution
: public GeneratingInferenceEngine
{
public:
  USE_ALLOCATOR(BinaryResolution);

  BinaryResolution(bool hasEquality) 
    : _index(0),
    _unificationWithAbstraction(false),
    _hasEquality(hasEquality)
  {  }

  void attach(SaturationAlgorithm* salg);
  void detach();

  static Clause* generateClause(Clause* queryCl, Literal* queryLit, SLQueryResult res, const Options& opts, Ordering& ord, PassiveClauseContainer* passive=0, bool afterCheck=false, LiteralSelector* ls = 0, ReducibilityChecker* checker = 0, bool diamondBreaking = false);
  ClauseIterator generateClauses(Clause* premise);

private:
  struct UnificationsFn;
  struct ResultFn;

  BinaryResolutionIndex* _index;
  bool _unificationWithAbstraction;
  bool _hasEquality;
};

};

#endif /*__BinaryResolution__*/
