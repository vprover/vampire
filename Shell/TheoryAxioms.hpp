/**
 * @file TheoryAxioms.hpp
 * Defines class TheoryAxioms.
 */

#ifndef __TheoryAxioms__
#define __TheoryAxioms__

#include "Forwards.hpp"

#include "Kernel/Theory.hpp"
#include "Options.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class TheoryAxioms {
public:
  TheoryAxioms(Options::TheoryAxiomLevel level) : _level(level) {}


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
  Options::TheoryAxiomLevel _level;

  void addCommutativity(Interpretation op, UnitList*& units);
  void addAssociativity(Interpretation op, UnitList*& units);
  void addRightIdentity(Interpretation op, TermList idElement, UnitList*& units);
  void addLeftIdentity(Interpretation op, TermList idElement, UnitList*& units);
  void addCommutativeGroupAxioms(Interpretation op,Interpretation inverse,
				 TermList idElement, UnitList*& units);

  void addRightInverse(Interpretation op, Interpretation inverse, UnitList*& units);

  void addNonReflexivity(Interpretation op, UnitList*& units);
  void addTransitivity(Interpretation op, UnitList*& units);
  void addOrderingTotality(Interpretation less, UnitList*& units);
  void addTotalOrderAxioms(Interpretation less, UnitList*& units);
  void addMonotonicity(Interpretation less, Interpretation addition, UnitList*& units);
  void addPlusOneGreater(Interpretation plus, TermList oneElement,
                                     Interpretation less, UnitList*& units);
  void addAdditionAndOrderingAxioms(Interpretation plus, Interpretation unaryMinus,
				    TermList zeroElement, TermList oneElement,
				    Interpretation less, UnitList*& units);
  void addAdditionOrderingAndMultiplicationAxioms(Interpretation plus, Interpretation unaryMinus,
						  TermList zeroElement, TermList oneElement,
						  Interpretation less, Interpretation multiply,
						  UnitList*& units);
  void addExtraIntegerOrderingAxiom(Interpretation plus, TermList oneElement, Interpretation less,
				    UnitList*& units);
  void addQuotientAxioms(Interpretation quotient, Interpretation multiply, TermList zeroElement, TermList oneElement,
                         Interpretation less,UnitList*& units);
  void addIntegerDivisionWithModuloAxioms(Interpretation plus, Interpretation unaryMinus, Interpretation less,
                                Interpretation multiply, Interpretation divide, Interpretation divides,
                                Interpretation modulo, Interpretation abs, TermList zeroElement,
                                TermList oneElement, UnitList*& units);
  void addIntegerAbsAxioms(Interpretation abs, Interpretation less,
                           Interpretation unaryMinus, TermList zeroElement, UnitList*& units);
  void addIntegerDividesAxioms(Interpretation divides, Interpretation multiply, TermList zero, TermList n, UnitList*& units);

  void addBooleanArrayExtensionalityAxioms(Interpretation select, Interpretation store, unsigned skolem, UnitList*& units);
  void addArrayExtensionalityAxioms(Interpretation select, Interpretation store, unsigned skolem, UnitList*& units);
  void addBooleanArrayWriteAxioms(Interpretation select, Interpretation store, UnitList*& units);
  void addTupleAxioms(unsigned tupleSort, UnitList*& units);
  void addFloorAxioms(Interpretation floor, Interpretation less, Interpretation unaryMinus,
                      Interpretation plus, TermList oneElement, UnitList*& units);
  void addCeilingAxioms(Interpretation ceiling, Interpretation less, Interpretation plus, 
                        TermList oneElement, UnitList*& units);
  void addRoundAxioms(Interpretation round, Interpretation floor, Interpretation ceiling, UnitList*& units); 
  void addTruncateAxioms(Interpretation truncate, Interpretation less, Interpretation unaryMinus,
                      Interpretation plus, TermList zeroElement, TermList oneElement, UnitList*& units);
  void addArrayWriteAxioms(Interpretation select, Interpretation store, UnitList*& units);
  void addTheoryUnitClause(Literal* lit, UnitList*& units);
  void addTheoryNonUnitClause(UnitList*& units, Literal* lit1, Literal* lit2, Literal* lit3=0);
  void addTheoryNonUnitClause(UnitList*& units, Literal* lit1, Literal* lit2, Literal* lit3, Literal* lit4);
  void addAndOutputTheoryUnit(Unit* unit,UnitList*& units);
};

}

#endif // __TheoryAxioms__
