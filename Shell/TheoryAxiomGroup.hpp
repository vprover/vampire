/**
 * @file TheoryAxiomGroup.hpp
 * Defines class TheoryAxiomGroup.
 */

#ifndef __TheoryAxiomGroup__
#define __TheoryAxiomGroup__

#include "Forwards.hpp"

#include "Kernel/Theory.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class TheoryAxiomGroup {
public:
  void apply(Problem& prb,unsigned group);
  void apply(UnitList*& units, unsigned group, Property* prop);
  void apply(UnitList*& units, unsigned group, unsigned srt);

private:
  void addTheoryUnit(Unit* unit, UnitList*& units);
  void addTheoryUnitClause(Literal* lit, UnitList*& units);
  void addTheoryNonUnitClause(UnitList*& units, Literal* lit1, Literal* lit2, Literal* lit3=0);

  void addOne(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units);
  void addTwo(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units);
  void addThree(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units);
  void addFour(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units);
  void addFive(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units);
  void addSix(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units);
  void addSeven(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units);
  void addEight(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units);
  void addNine(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units);
  void addTen(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units);
  void addEleven(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units);
  void addTwelve(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units);
  void addThirteen(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units);
  void addFourteen(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units);
  void addFifteen(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units);
};

}

#endif // __TheoryAxiomGroup__
