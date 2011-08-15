/**
 * @file InequalitySplitting.hpp
 * Defines class InequalitySplitting.
 */


#ifndef __InequalitySplitting__
#define __InequalitySplitting__

#include "Forwards.hpp"
#include "Lib/Stack.hpp"

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
  Literal* splitLiteral(Literal* lit, Unit::InputType inpType, Clause*& premise);

  Literal* makeNameLiteral(unsigned predNum, TermList arg, bool polarity);

  bool isSplittable(Literal* lit);
  bool isSplittableEqualitySide(TermList t);

  Stack<Clause*> _predDefs;
  unsigned _splittingTreshold;
};

};

#endif /* __InequalitySplitting__ */
