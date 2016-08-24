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
  Clause* apply(Clause*& cl);
private:
  Literal* replaceTopTerms(Literal* lit, Stack<Literal*>& newLits,unsigned& maxVar);
  Term* replaceTopTermsInTerm(Term* term, Stack<Literal*>& newLits,
                              unsigned& maxVar,bool interpreted);


};

};

#endif /* __TheoryFlattening__ */
