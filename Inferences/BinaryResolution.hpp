
/*
 * File BinaryResolution.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
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

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class BinaryResolution
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(BinaryResolution);
  USE_ALLOCATOR(BinaryResolution);

  BinaryResolution() : _index(0), _unificationWithAbstraction(false) {}

  void attach(SaturationAlgorithm* salg);
  void detach();

  static Clause* generateClause(Clause* queryCl, Literal* queryLit, SLQueryResult res, const Options& opts, PassiveClauseContainer* passive=0, Ordering* ord=0, LiteralSelector* ls = 0);
  ClauseIterator generateClauses(Clause* premise);

private:
  struct UnificationsFn;
  struct ResultFn;

  GeneratingLiteralIndex* _index;
  bool _unificationWithAbstraction;
};

};

#endif /*__BinaryResolution__*/
