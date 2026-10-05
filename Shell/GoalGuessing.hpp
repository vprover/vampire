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
 * @file GoalGuessing.hpp
 * Defines class GoalGuessing.
 */


#ifndef __GoalGuessing__
#define __GoalGuessing__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHSet.hpp"

namespace Shell {

using namespace Kernel;
using namespace Lib;

class GoalGuessing
{
public:
  void apply(Problem& prb);
private:
  bool apply(UnitList*& units);
  bool apply(Clause* cl);
  bool apply(FormulaUnit* fu);
  bool apply(Literal* lit);

  void countPerUnitUsage(UnitList* units);
  void collectFunctors(Unit* u);

  bool _lookInside;
  bool _checkTop;
  bool _checkSymbols;
  bool _checkPosition;

  /** value of the gtg_limit option, read once in apply(Problem&) */
  unsigned _limit;
  /** for each function symbol, the number of units it occurs in */
  DArray<unsigned> _perUnitUsageCount;
  /** the function symbols of the unit currently being counted */
  DHSet<unsigned, FnvHash, IdentityHash> _functorsInUnit;
};

};

#endif /* __GoalGuessing__ */
