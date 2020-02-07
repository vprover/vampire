
/*
 * File TheoryAxioms.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
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
  TheoryAxioms(Problem& prb) :
    _prb(prb)
  {} 

static unsigned const CHEAP = 0;
static unsigned const EXPENSIVE = 1;

  void apply();

  /**
   * There is a separate method for adding the FOOL domain axiom because unlike
   * for the other supported theories, reasoning in FOOL is complete, so we
   * want to be sure to always add the axiom when FOOL subexpressions are met,
   * which is a different condition that is used to apply axioms than the one,
   * used for the other theories.
   */
  void applyFOOL();

private:

  Problem& _prb;

  void addCommutativity(Interpretation op);

  void addAssociativity(Interpretation op);
  void addRightIdentity(Interpretation op, TermList idElement);

  void addLeftIdentity(Interpretation op, TermList idElement);
  void addCommutativeGroupAxioms(Interpretation op, Interpretation inverse, TermList idElement);

  void addRightInverse(Interpretation op, Interpretation inverse);

  void addNonReflexivity(Interpretation op);

  void addTransitivity(Interpretation op);
  void addOrderingTotality(Interpretation less);
  void addTotalOrderAxioms(Interpretation less);
  void addMonotonicity(Interpretation less, Interpretation addition);
  void addPlusOneGreater(Interpretation plus, TermList oneElement, Interpretation less);
  void addAdditionAndOrderingAxioms(Interpretation plus, Interpretation unaryMinus,
				    TermList zeroElement, TermList oneElement,
				    Interpretation less);
  void addAdditionOrderingAndMultiplicationAxioms(Interpretation plus, Interpretation unaryMinus,
						  TermList zeroElement, TermList oneElement,
                                                  Interpretation less, Interpretation multiply);


  // Bitvector axioms
  //------------------------------------------------------------------------------------------------------------------------------------------
  void addBitVectorCommutativity(Interpretation op, unsigned size);
  void addBitVectorRightIdentity(Interpretation i, TermList idElement, unsigned size);
  void addPolyMorphicNonReflexivity(Interpretation op, OperatorType* type);

  void addPolyMorphicSpecialConstantAxiom(Interpretation op, TermList arg, TermList out, unsigned size);
  void addPolyMorphicSpecialConstantAxiomVariation(Interpretation op, TermList arg, TermList out, unsigned size);
  void addPolyMorphicBinaryFunctionEquivalentToUnaryFunctionAppliedToBinaryFunction(Interpretation f, Interpretation unary, Interpretation binary, unsigned size);
  void addPolyMorphicBinaryFunctionEquivalentToBinaryFunctionAppliedToUnaryFunction(Interpretation f, Interpretation binary, Interpretation unary, unsigned size);
  
  void addBVXORAxiom1(Interpretation bvxorInterpretation, Interpretation bvorInterpretation , Interpretation bvandInterpretation, Interpretation bvnotInterpretation, unsigned size);
  void addBVXNORAxiom1(Interpretation xnor, Interpretation bvor , Interpretation bvand, Interpretation bvnot, unsigned size);
  void addBVReverseAndMoreAxiom(Interpretation bvugt, Interpretation bvult,unsigned size);
  void addEqualsImpliesBinaryPredicate(Interpretation itp, unsigned srt);

  void addBVUREMwithPredicateAxiom(Interpretation f, Interpretation p, unsigned srt);
  void addFunctionWithSameArgumentEqualsConstant(Interpretation f, TermList constant, unsigned srt);
  void addFunctionWithSameArgumentEqualArgument(Interpretation f, unsigned srt);
  void addFunctionAppliedToConstantPredicateFirstArgVariation(Interpretation f, Interpretation p, TermList constant, unsigned srt);

  void addSomeAdditionAxiom(unsigned srt);
  void addAdditionByOneAxioms(unsigned srt);
  void addUnaryFunctionAppliedTwiceEqualsArgument(Interpretation f, unsigned srt);

  void isPredicateWithEqualRemovedOrEqualAxiom(Interpretation completePredicate, Interpretation predicateWithEqualRemoved, unsigned sort);
  void addMaxAxiom(Interpretation p, unsigned srt);

  void predicateTrueForArgumentsOfAFunction(unsigned srt, Interpretation func, Interpretation pred);

  void addPredicateOnConcatArgsImpliesPredicateConcatFirstArg(unsigned srt0, unsigned srt1, unsigned resultSrt, Interpretation predicate);
  void addConcatArgsPredicateImpliesWholePredicateVariation(Interpretation predicate, unsigned srt0, unsigned srt1, unsigned resultSort);
  void addConcatArgsPredicateImpliesWholePredicate(Interpretation predicate, unsigned srt0, unsigned srt1, unsigned resultSort);
  void addConcatArgumentsNotEqualEquivalentToConcatResultsNotEqual(unsigned srt0, unsigned srt1, unsigned resultSort);
  void addConcatAxiom1(unsigned srt0, unsigned srt1, unsigned resultSrt);
  void addConcatAxiom2(unsigned srt0, unsigned srt1, unsigned resultSrt);

  void addPolyMorphicClauseAxiom(unsigned srt, Interpretation pred1, bool swapArguments, bool polarity,Interpretation pred2, bool swapArguments2, bool polarity2);
  void addPolyMorphicLiteralWithConstantAxiom(unsigned srt, Interpretation pred1, TermList constant, bool swapArguments, bool polarity);

  void addXNEqualToConstantImpliesAxiom(unsigned srt, Interpretation predicate, TermList constant, bool swapArgs);
  void addTempOrAxiom2(unsigned srt, Interpretation pred1, Interpretation func);
  void addSimplePolyMorphicPredicateWithConstantAxiom(unsigned srt, Interpretation pred, TermList constant, bool swapArguments, bool reversePolarity, bool comm);


  void addOtherBVANDSignedPredicatesAxiom(unsigned srt, Interpretation pred, Interpretation func,
  		  TermList constant);

  void addSpecialEqualAndAxiom(unsigned srt, Interpretation func);
  void addShiftingAxiom(unsigned srt, Interpretation func1, Interpretation func2);

  void addORSignedOperatorWithConstantAxiom(unsigned srt0, Interpretation pred, Interpretation func,TermList constant);

  void addDivisionZeroAxiom(unsigned srt);
  void addDivisionOneAxiom(unsigned srt);
  void addAnotherDivisionAxiom(unsigned srt);
  void addDivisionSameArgAxiom(unsigned srt);
  void addDivAxiomGT(unsigned srt);
  void addDivONEAxiom(unsigned srt);
  void addDivAxiomGT2(unsigned srt);
  void addTempAxiom(unsigned srt);

  // Chaos Axioms
  void addChaosAxiom0(unsigned srt, unsigned size);
  void addChaosAxiom1(unsigned srt, unsigned size);
  void addChaosAxiom2(unsigned srt, unsigned size);
  void addChaosAxiom3(unsigned srt, unsigned size);
  void addChaosAxiom4(unsigned srt, unsigned size);
  void addChaosAxiom5(unsigned srt, unsigned size);
  void addChaosAxiom6(unsigned srt, unsigned size);
  void addSolverAxiom1(unsigned srt, unsigned size);
  // bvsgt_bvand

  void addChaosAxiom10(unsigned srt, unsigned size);


//------------------------------------------------------------------------------------------------------------------------------------------
  void addExtraIntegerOrderingAxiom(Interpretation plus, TermList oneElement, Interpretation less);

  void addQuotientAxioms(Interpretation quotient, Interpretation multiply, TermList zeroElement, TermList oneElement,
                         Interpretation less);
  void addIntegerDivisionWithModuloAxioms(Interpretation plus, Interpretation unaryMinus, Interpretation less,
                                Interpretation multiply, Interpretation divide, Interpretation divides,
                                Interpretation modulo, Interpretation abs, TermList zeroElement,
                                TermList oneElement);
  void addIntegerAbsAxioms(Interpretation abs, Interpretation less,
                           Interpretation unaryMinus, TermList zeroElement);
  void addIntegerDividesAxioms(Interpretation divides, Interpretation multiply, TermList zero, TermList n);

  void addBooleanArrayExtensionalityAxioms(unsigned arraySort, unsigned skolem);
  void addArrayExtensionalityAxioms(unsigned arraySort, unsigned skolem);
  void addBooleanArrayWriteAxioms(unsigned arraySort);
  void addArrayWriteAxioms(unsigned arraySort);

  void addTupleAxioms(unsigned tupleSort);
  void addFloorAxioms(Interpretation floor, Interpretation less, Interpretation unaryMinus,
                      Interpretation plus, TermList oneElement);
  void addCeilingAxioms(Interpretation ceiling, Interpretation less, Interpretation plus, 
                        TermList oneElement);
  void addRoundAxioms(Interpretation round, Interpretation floor, Interpretation ceiling); 
  void addTruncateAxioms(Interpretation truncate, Interpretation less, Interpretation unaryMinus,
                      Interpretation plus, TermList zeroElement, TermList oneElement);

  // term algebra axioms
  void addExhaustivenessAxiom(TermAlgebra* ta);
  void addDistinctnessAxiom(TermAlgebra* ta);
  void addInjectivityAxiom(TermAlgebra* ta);
  void addDiscriminationAxiom(TermAlgebra* ta);
  void addAcyclicityAxiom(TermAlgebra* ta);

  /* Subterm definitions used by the acyclicity axiom. True iff some
     definition was actually added (i.e. if the constructor is
     recursive) */
  bool addSubtermDefinitions(unsigned subtermPredicate, TermAlgebraConstructor* c);

  void addTheoryUnitClause(Literal* lit, unsigned level);
  void addTheoryUnitClause(Literal* lit, Inference* inf, unsigned level);
  void addTheoryNonUnitClause(Literal* lit1, Literal* lit2,unsigned level);
  void addTheoryNonUnitClause(Literal* lit1, Literal* lit2, Literal* lit3,unsigned level);
  void addTheoryNonUnitClause(Literal* lit1, Literal* lit2, Literal* lit3, Literal* lit4,unsigned level);
  void addAndOutputTheoryUnit(Unit* unit, unsigned level);
};

}

#endif // __TheoryAxioms__
