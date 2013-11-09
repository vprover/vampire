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

  void apply(Problem& prb);
  bool apply(UnitList*& units, Property* prop);

private:
  void addCommutativity(Interpretation op, UnitList*& units);
  void addAssociativity(Interpretation op, UnitList*& units);
  void addIdentity(Interpretation op, TermList idElement, UnitList*& units);
  void addCommutativeGroupAxioms(Interpretation op, Interpretation inverse, TermList idElement, UnitList*& units);

  void addReflexivity(Interpretation op, UnitList*& units);
  void addTransitivity(Interpretation op, UnitList*& units);
  void addOrderingTotality(Interpretation lessEqual, UnitList*& units);
  void addTotalOrderAxioms(Interpretation lessEqual, UnitList*& units);

  void addMonotonicity(Interpretation lessEqual, Interpretation addition, UnitList*& units);

  void addAdditionAndOrderingAxioms(Interpretation plus, Interpretation unaryMinus,
      TermList zeroElement, TermList oneElement, Interpretation lessEqual, UnitList*& units);
  void addAdditionOrderingAndMultiplicationAxioms(Interpretation plus, Interpretation unaryMinus,
      TermList zeroElement, TermList oneElement, Interpretation lessEqual, Interpretation multiply,
      UnitList*& units);

  void addExtraIntegerOrderingAxiom(Interpretation plus, TermList oneElement, Interpretation lessEqual,
      UnitList*& units);

  void addArrayExtensionalityAxioms(Interpretation select, Interpretation store, UnitList*& units);
  void addArrayWriteAxioms(Interpretation select, Interpretation store, UnitList*& units);


  void addTheoryUnit(Literal* lit, UnitList*& units);
  void addTheoryClause(UnitList*& units, Literal* lit1, Literal* lit2, Literal* lit3=0);
};

}

#endif // __TheoryAxioms__
