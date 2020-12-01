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

namespace Shell {

using namespace Kernel;

class GoalGuessing
{
public:
  CLASS_NAME(GoalGuessing);
  USE_ALLOCATOR(GoalGuessing);

  void apply(Problem& prb);
private:
  bool apply(UnitList*& units);
  bool apply(Clause* cl);
  bool apply(FormulaUnit* fu);
  bool apply(Literal* lit);

  bool _lookInside;
  bool _checkTop;
  bool _checkSymbols;
  bool _checkPosition;
};

};

#endif /* __GoalGuessing__ */
