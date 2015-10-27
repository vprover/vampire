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
  void apply(Problem& prb);
  bool apply(UnitList*& units, Property* prop);

  /**
   * There is a separate method for adding the FOOL domain axiom because unlike
   * for the other supported theories, reasoning in FOOL is complete, so we
   * want to be sure to always add the axiom when FOOL subexpressions are met,
   * which is a different condition that is used to apply axioms than the one,
   * used for the other theories.
   */
  void applyFOOL(Problem& prb);

private:
  void addCommutativity(Interpretation op, UnitList*& units);
  void addAssociativity(Interpretation op, UnitList*& units);
  void addIdentity(Interpretation op, UnitList*& units);
  void addRightIdentity(Interpretation op, TermList idElement, UnitList*& units);
  void addCommutativeGroupAxioms(Interpretation op,Interpretation inverse,
				 TermList idElement, UnitList*& units);

  void addReflexivity(Interpretation op, UnitList*& units);
  void addTransitivity(Interpretation op, UnitList*& units);
  void addOrderingTotality(Interpretation lessEqual, UnitList*& units);
  void addTotalOrderAxioms(Interpretation lessEqual, UnitList*& units);
  void addMonotonicity(Interpretation lessEqual, Interpretation addition, UnitList*& units);
  void addAdditionAndOrderingAxioms(Interpretation plus, Interpretation unaryMinus,
				    TermList zeroElement, TermList oneElement,
				    Interpretation lessEqual, UnitList*& units);
  void addAdditionOrderingAndMultiplicationAxioms(Interpretation plus, Interpretation unaryMinus,
						  TermList zeroElement, TermList oneElement,
						  Interpretation lessEqual, Interpretation multiply,
						  UnitList*& units);
  void addExtraIntegerOrderingAxiom(Interpretation plus, TermList oneElement, Interpretation lessEqual,
				    UnitList*& units);

  void addBooleanArrayExtensionalityAxioms(Interpretation select, Interpretation store, unsigned skolem, UnitList*& units);
  void addArrayExtensionalityAxioms(Interpretation select, Interpretation store, unsigned skolem, UnitList*& units);
  void addBooleanArrayWriteAxioms(Interpretation select, Interpretation store, UnitList*& units);
  void addFloorAxioms(Interpretation floor, Interpretation lessEqual, Interpretation unaryMinus,
                      Interpretation plus, TermList oneElement, UnitList*& units);
  void addCeilingAxioms(Interpretation ceiling, Interpretation lessEqual, Interpretation plus, 
                        TermList oneElement, UnitList*& units);
  void addRoundAxioms(Interpretation round, Interpretation floor, Interpretation ceiling, UnitList*& units); 
  void addTruncateAxioms(Interpretation truncate, Interpretation lessEqual, Interpretation unaryMinus,
                      Interpretation plus, TermList zeroElement, TermList oneElement, UnitList*& units);
  void addArrayWriteAxioms(Interpretation select, Interpretation store, UnitList*& units);
  void addTheoryUnitClause(Literal* lit, UnitList*& units);
  void addTheoryNonUnitClause(UnitList*& units, Literal* lit1, Literal* lit2, Literal* lit3=0);
  void addAndOutputTheoryUnit(Unit* unit,UnitList*& units);
};

}

#endif // __TheoryAxioms__
