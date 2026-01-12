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

#include "Indexing/LiteralIndex.hpp"
#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

template<bool synthesis>
class URResolution
: public GeneratingInferenceEngine
{
public:
  URResolution(bool full);

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

  ClauseIterator generateClauses(Clause* premise) override;

private:
  struct Item;
  typedef List<Item*> ItemList;

  void processAndGetClauses(Item* itm, unsigned startIdx, ClauseList*& acc);

  void processLiteral(ItemList*& itms, unsigned idx);

  void doBackwardInferences(Clause* cl, ClauseList*& acc);

  bool _full;
  bool _emptyClauseOnly;
  bool _selectedOnly;
  using UnitIndexType = std::conditional_t<synthesis, UnitClauseWithALLiteralIndex, UnitClauseLiteralIndex>;
  using NonUnitIndexType = std::conditional_t<synthesis, NonUnitClauseWithALLiteralIndex, NonUnitClauseLiteralIndex>;
  std::shared_ptr<UnitIndexType> _unitIndex;
  std::shared_ptr<NonUnitIndexType> _nonUnitIndex;
};

};

#endif // __URResolution__
