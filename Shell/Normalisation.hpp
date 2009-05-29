/**
 * @file Normalisation.hpp
 * Defines class Normalisation implementing the normalisation inference rule.
 * @since 24/12/2003 Manchester
 */

#ifndef __Normalisation__
#define __Normalisation__


#include "../Lib/Comparison.hpp"
#include "../Kernel/Unit.hpp"

#include "SymCounter.hpp"

namespace Kernel {
  class Literal;
  class Term;
  class TermList;
  class Clause;
  class FormulaUnit;
}

using namespace Lib;
using namespace Kernel;

namespace Shell {

/**
 * Class implementing normalisation-related procedures.
 * @since 03/04/2004 Torrevieja, lots renumberSymbols removed
 */
class Normalisation
{
public:
  Normalisation();
  UnitList* normalise(UnitList*);
  bool lessThan(Literal*, Literal*);
  bool lessThan(Unit*, Unit*);
private:
  void normalise(Unit*);
  Comparison compare(Term*, Term*);
  Comparison compare(Formula*, Formula*);
  Comparison compare(Literal*, Literal*);
  bool lessThan(Formula*, Formula*);
  Comparison compare(TermList* ss, TermList* ts);

  /**
   * Return the result of comparison of two integers i1 and i2
   */
  inline static
  Comparison compare (int i1, int i2)
  {
    return i1 > i2
           ? GREATER
           : i1 == i2
             ? EQUAL
             : LESS;
  }

  /**
   * Return the result of comparison of two booleans b1 and b2.
   * @since 30/04/2005 Manchester
   */
  inline static
  Comparison compare (bool b1, bool b2)
  {
    return b1 ? (b2 ? EQUAL : LESS) : (b2 ? GREATER : EQUAL);
  }

  /** Counter of the number of symbols */
  SymCounter _counter;
}; // class Normalisation

}

#endif
