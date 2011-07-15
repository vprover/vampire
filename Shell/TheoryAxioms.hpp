/**
 * @file TheoryAxioms.hpp
 * Defines class TheoryAxioms.
 */

#ifndef __TheoryAxioms__
#define __TheoryAxioms__

#include "Forwards.hpp"

#include "Kernel/Theory.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class TheoryAxioms {
public:


  struct Arithmetic;

  void apply(UnitList*& units, Property* prop);

private:
  void addCommutativity(Interpretation op, UnitList*& units);
  void addAssociativity(Interpretation op, UnitList*& units);
  void addIdentity(Interpretation op, TermList idElement, UnitList*& units);
  void addCommutativeGroupAxioms(Interpretation op, Interpretation inverse, TermList idElement, UnitList*& units);

  void addTheoryUnit(Literal* lit, UnitList*& units);

  Unit* replaceFunctions(Unit* u);
  Formula* replaceFunctions(Formula* f);
  FormulaList* replaceFunctions(FormulaList* fs);
  Literal* replaceFunctions(Literal* l);
};

}

#endif // __TheoryAxioms__
