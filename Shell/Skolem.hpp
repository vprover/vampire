/**
 * @file Skolem.hpp
 * Defines class Skolem implementing skolemisation.
 * @since 05/01/2004 Manchester
 * @since 08/07/2007 Manchester Airport, changed to new datastructures
 */

#ifndef __Skolem__
#define __Skolem__

#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Substitution.hpp"

namespace Kernel {
  class Unit;
}

using namespace Lib;
using namespace Kernel;

namespace Shell {

// class Formula;
// class FormulaList;

/**
 * Class implementing skolemisation-related procedures.
 * @since 23/01/2004 Manchester, changed to use non-static functions
 */
class Skolem
{
public:
  static Unit* skolemise(Unit*);
private:
  /** Initialise a Skolem object */
  Skolem ()
    : _vars(16), _beingSkolemised(0)
  {}
  FormulaUnit* skolemiseImpl(FormulaUnit*);
  Formula* skolemise(Formula*);
  FormulaList* skolemise(FormulaList*);

  void reset();
  Term* createSkolemTerm(unsigned var);

  typedef Stack<int> VarStack;

  /** collected substitution */
  Substitution _subst;
  /** Universally quantified variables collected */
  VarStack _vars;

  /** map var --> sort */
  DHMap<unsigned,unsigned> _varSorts;

  Unit* _beingSkolemised;
}; // class Skolem

}

#endif
