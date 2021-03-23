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
 * @file InequalitySplitting.hpp
 * Defines class InequalitySplitting.
 */


#ifndef __InequalitySplitting__
#define __InequalitySplitting__

#include "Forwards.hpp"
#include "Lib/Stack.hpp"
#include "Kernel/Inference.hpp"

namespace Shell {

using namespace std;
using namespace Lib;
using namespace Kernel;


class InequalitySplitting
{
public:
  InequalitySplitting(const Options& opt);

  void perform(Problem& prb);
  bool perform(UnitList*& units);

private:
  Clause* trySplitClause(Clause* cl);
  Literal* splitLiteral(Literal* lit, UnitInputType inpType, Clause*& premise);

  Literal* makeNameLiteral(unsigned predNum, TermList arg, bool polarity, TermStack vars);

  bool isSplittable(Literal* lit);
  bool isSplittableEqualitySide(TermList t);

  Stack<Clause*> _predDefs;
  unsigned _splittingTreshold;
  bool _appify; // do it the higher-order way
};

};

#endif /* __InequalitySplitting__ */
