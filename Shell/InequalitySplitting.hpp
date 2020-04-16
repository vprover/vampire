
/*
 * File InequalitySplitting.hpp.
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
  Literal* splitLiteral(Literal* lit, Inference::InputType inpType, Clause*& premise);

  Literal* makeNameLiteral(unsigned predNum, TermList arg, bool polarity);

  bool isSplittable(Literal* lit);
  bool isSplittableEqualitySide(TermList t);

  Stack<Clause*> _predDefs;
  unsigned _splittingTreshold;
};

};

#endif /* __InequalitySplitting__ */
