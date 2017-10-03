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
  TheoryAxioms() {} 

static unsigned const CHEAP = 0;
static unsigned const EXPENSIVE = 1;

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
  void addBVUdivAxiom1(Interpretation bvudiv, TermList zeroElement, TermList oneElement,UnitList*& units);
  /*void addConcatAxiom(Interpretation concatInterpretation, unsigned sortArg1,unsigned sortArg2,unsigned resultSort, UnitList*& units);*/
  /*void addBVsdivAxiom(Interpretation bvsdivInterpretation, Interpretation extractInterpretation,Interpretation bvudivI, Interpretation bvnegI, unsigned n,UnitList*& units);
   */               
  void addCertainBitVectorAxioms(Interpretation plus, Interpretation unaryMinus,
  TermList zeroElement, TermList oneElement, Interpretation less, UnitList*& units);
  void addBVNandAxiom1(Interpretation bvnand, Interpretation bvnot, Interpretation bvand, UnitList*& units);
  void addBVNorAxiom1(Interpretation bvnor, Interpretation bvnot, Interpretation bvor, UnitList*& units);
  void addBVXORAxiom1(Interpretation bvxorInterpretation, Interpretation bvorInterpretation , Interpretation bvandInterpretation, Interpretation bvnotInterpretation, UnitList*& units);
  void addBVXNORAxiom1(Interpretation bvxnor, Interpretation bvor , Interpretation bvand, Interpretation bvnot, UnitList*& units);
  void addBVSUBAxiom1(Interpretation subInterpretation, Interpretation bvaddInterpretation , Interpretation bvnegInterpretation, UnitList*& units);
  void addBVUleAxiom1(Interpretation bvule, Interpretation bvult, UnitList*& units);
  void addBVReverseAxiom(Interpretation bvugt, Interpretation bvult, UnitList*& units);
  void addMulBitVectorAxioms(Interpretation plus, Interpretation unaryMinus,
    TermList zeroElement, TermList oneElement, Interpretation less, Interpretation multiply, UnitList*& units);
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

  // term algebra axioms
  void addExhaustivenessAxiom(TermAlgebra* ta, UnitList*& units);
  void addDistinctnessAxiom(TermAlgebra* ta, UnitList*& units);
  void addInjectivityAxiom(TermAlgebra* ta, UnitList*& units);
  void addAlternativeInjectivityAxiom(TermAlgebra* ta, UnitList*& units);
  void addDiscriminationAxiom(TermAlgebra* ta, UnitList*& units);
  void addAcyclicityAxiom(TermAlgebra* ta, UnitList*& units);

  /* Subterm definitions used by the acyclicity axiom. True iff some
     definition was actually added (i.e. if the constructor is
     recursive) */
  static bool addSubtermDefinitions(unsigned subtermPredicate, TermAlgebraConstructor* c, UnitList*& units);

  static void addTheoryUnitClause(Literal* lit, UnitList*& units,unsigned level);
  static void addTheoryUnitClause(Literal* lit, Inference* inf, UnitList*& units,unsigned level);
  static void addTheoryNonUnitClause(UnitList*& units, Literal* lit1, Literal* lit2,unsigned level);
  static void addTheoryNonUnitClause(UnitList*& units, Literal* lit1, Literal* lit2, Literal* lit3,unsigned level);
  static void addTheoryNonUnitClause(UnitList*& units, Literal* lit1, Literal* lit2, Literal* lit3, Literal* lit4,unsigned level);
  static void addAndOutputTheoryUnit(Unit* unit,UnitList*& units,unsigned level);
};

}

#endif // __TheoryAxioms__
