/**
 * @file TheoryFlattening.hpp
 * Defines class TheoryFlattening.
 */


#ifndef __TheoryFlattening__
#define __TheoryFlattening__

#include "Forwards.hpp"

namespace Shell {

using namespace Kernel;

/**
 * Class for flattening clauses to separate theory and non-theory parts
 */
class TheoryFlattening
{
public:
  void apply(Problem& prb);
  bool apply(UnitList*& units);
  bool apply(ClauseList*& units);
private:
  Clause* apply(Clause*& cl);
  Literal* replaceTopTerms(Literal* lit, Stack<Literal*>& newLits,unsigned& maxVar);

};

};

#endif /* __TheoryFlattening__ */
