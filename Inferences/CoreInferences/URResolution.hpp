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
 * @file URResolution.cpp
 * Defines class URResolution.
 */

#ifndef __URResolution__
#define __URResolution__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class URResolution
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(URResolution);
  USE_ALLOCATOR(URResolution);

  URResolution();
  URResolution(bool selectedOnly, UnitClauseLiteralIndex* unitIndex,
      NonUnitClauseLiteralIndex* nonUnitIndex);

  void attach(SaturationAlgorithm* salg);
  void detach();

  ClauseIterator generateClauses(Clause* premise);

private:
  struct Item;
  typedef List<Item*> ItemList;

  void processAndGetClauses(Item* itm, unsigned startIdx, ClauseList*& acc);

  void processLiteral(ItemList*& itms, unsigned idx);

  void doBackwardInferences(Clause* cl, ClauseList*& acc);


  bool _emptyClauseOnly;
  bool _selectedOnly;
  UnitClauseLiteralIndex* _unitIndex;
  NonUnitClauseLiteralIndex* _nonUnitIndex;
};

};

#endif // __URResolution__
