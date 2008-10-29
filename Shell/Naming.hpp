/**
 * @file Naming.hpp
 * Defines the naming technique
 * @since 05/05/2005 Manchester
 * @since 07/07/2007 Manchester, changed to new datastructures
 */

#ifndef __Naming__
#define __Naming__

#include "../Kernel/Formula.hpp"
#include "../Kernel/Unit.hpp"

using namespace Kernel;

namespace Shell {

/**
 * Class implementing the naming technique.
 * @since 05/05/2005 Manchester
 */
class Naming
{
public:
  Naming (int threshold);
  Unit* apply(Unit* unit,UnitList*& defs);
private:
  /** Encodes information about the position of the sub formula */
  enum Where {
    /** the subformula is only in the range of conjunctions */
    ON_TOP,
    /** the subformula is in the range of at least one equivalence */
    UNDER_IFF,
    /** the subformula has a positive polarity but has at least one
     * disjunction above */
    OTHER
  }; 
  /** Threshold for naming. If a non-unit clause is going to be used 
   *  the number of times greater than of equal to the threshold, 
   *  it will be named. 
   */
  int _threshold;
  /** The list of definitions produced by naming for this unit*/
  UnitList* _defs;

  Formula* apply(Formula* subformula,Where where,int& pos,int& neg);
  FormulaList* apply(FormulaList* subformulas,
		     Where where,
		     int* results,
		     int* resultsNeg);
  Formula* introduceDefinition(Formula* f,bool iff);
}; // class Naming

}

#endif
