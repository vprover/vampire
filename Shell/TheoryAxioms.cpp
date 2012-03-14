/**
 * @file TheoryAxioms.cpp
 * Implements class TheoryAxioms.
 */

#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Theory.hpp"

#include "AxiomGenerator.hpp"
#include "Property.hpp"
#include "SymCounter.hpp"

#include "TheoryAxioms.hpp"


namespace Shell
{
using namespace Lib;
using namespace Kernel;

/**
 * Add unit clause with literal @c lit among @c units
 */
void TheoryAxioms::addTheoryUnit(Literal* lit, UnitList*& units)
{
  CALL("TheoryAxioms::addTheoryUnit");

  Clause* unit = Clause::fromIterator(getSingletonIterator(lit), Unit::AXIOM, new Inference(Inference::THEORY));
  UnitList::push(unit, units);
  LOG_UNIT("arith_axioms",unit);
}

/**
 * Add clause with literals @c lit1, @c lit2, @c lit3 among @c units
 *
 * @c lit3 can be zero, in that case only the first two literals are used.
 */
void TheoryAxioms::addTheoryClause(UnitList*& units, Literal* lit1, Literal* lit2, Literal* lit3)
{
  CALL("TheoryAxioms::addTheoryClause");

  static LiteralStack lits;
  lits.reset();
  ASS(lit1);
  lits.push(lit1);
  ASS(lit2);
  lits.push(lit2);
  if(lit3) {
    lits.push(lit3);
  }

  Clause* cl = Clause::fromStack(lits, Unit::AXIOM, new Inference(Inference::THEORY));
  UnitList::push(cl, units);
  LOG_UNIT("arith_axioms",cl);
}


/**
 * Add axiom op(X,Y)=op(Y,X)
 */
void TheoryAxioms::addCommutativity(Interpretation op, UnitList*& units)
{
  CALL("TheoryAxioms::addCommutativity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned func = env.signature->getInterpretingSymbol(op);
  unsigned srt = theory->getOperationSort(op);
  TermList v1(0,false);
  TermList v2(1,false);
  TermList f12(Term::create2(func, v1, v2));
  TermList f21(Term::create2(func, v2, v1));
  Literal* eq = Literal::createEquality(true, f12, f21, srt);

  addTheoryUnit(eq, units);
}

/**
 * Add axiom op(X,op(Y,Z))=op(op(X,Y),Z)
 */
void TheoryAxioms::addAssociativity(Interpretation op, UnitList*& units)
{
  CALL("TheoryAxioms::addCommutativity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned func = env.signature->getInterpretingSymbol(op);
  unsigned srt = theory->getOperationSort(op);
  TermList v1(0,false);
  TermList v2(1,false);
  TermList v3(2,false);
  TermList f12(Term::create2(func, v1, v2));
  TermList f23(Term::create2(func, v2, v3));
  TermList f1f23(Term::create2(func, v1, f23));
  TermList ff12_3(Term::create2(func, f12, v3));
  Literal* eq = Literal::createEquality(true, f1f23, ff12_3, srt);

  addTheoryUnit(eq, units);
}

/**
 * Add axiom op(X,id)=X
 */
void TheoryAxioms::addIdentity(Interpretation op, TermList idElement, UnitList*& units)
{
  CALL("TheoryAxioms::addIdentity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned func = env.signature->getInterpretingSymbol(op);
  unsigned srt = theory->getOperationSort(op);
  TermList v1(0,false);
  TermList f1I(Term::create2(func, v1, idElement));
  Literal* eq = Literal::createEquality(true, f1I, v1, srt);

  addTheoryUnit(eq, units);
}

/**
 * Add axioms for commutative group with @c op, @c inverse and @c idElement
 */
void TheoryAxioms::addCommutativeGroupAxioms(Interpretation op, Interpretation inverse, TermList idElement, UnitList*& units)
{
  CALL("TheoryAxioms::addCommutativeGroupAxioms");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);
  ASS(theory->isFunction(inverse));
  ASS_EQ(theory->getArity(inverse),1);

  addCommutativity(op, units);
  addAssociativity(op, units);
  addIdentity(op, idElement, units);

  //-(X0+X1)==(-X0)+(-X1)

  unsigned opFunc = env.signature->getInterpretingSymbol(op);
  unsigned invFunc = env.signature->getInterpretingSymbol(inverse);
  unsigned srt = theory->getOperationSort(op);
  ASS_EQ(srt, theory->getOperationSort(inverse));
  TermList v1(0,false);
  TermList v2(1,false);
  TermList f12(Term::create2(opFunc, v1, v2));
  TermList nv1(Term::create1(invFunc, v1));
  TermList nv2(Term::create1(invFunc, v2));
  TermList nf12(Term::create1(invFunc, f12));
  TermList fn1n2(Term::create2(opFunc, nv2, nv1));
  Literal* eq1 = Literal::createEquality(true, nf12, fn1n2, srt);
  addTheoryUnit(eq1, units);

  //X0+(-X0)==idElement
  TermList f1n1(Term::create2(opFunc, v1, nv1));
  Literal* eq2 = Literal::createEquality(true, f1n1, idElement, srt);
  addTheoryUnit(eq2, units);
}

/**
 * Add axiom op(X,X)
 */
void TheoryAxioms::addReflexivity(Interpretation op, UnitList*& units)
{
  CALL("TheoryAxioms::addReflexivity");

  ASS(!theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned opPred = env.signature->getInterpretingSymbol(op);
  TermList v1(0,false);
  Literal* l11 = Literal::create2(opPred, true, v1, v1);
  addTheoryUnit(l11, units);
}

/**
 * Add axiom ~op(X,Y) | ~op(Y,Z) | op(X,Z)
 */
void TheoryAxioms::addTransitivity(Interpretation op, UnitList*& units)
{
  CALL("TheoryAxioms::addTransitivity");
  ASS(!theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned opPred = env.signature->getInterpretingSymbol(op);
  TermList v1(0,false);
  TermList v2(1,false);
  TermList v3(2,false);

  Literal* nonL12 = Literal::create2(opPred, false, v1, v2);
  Literal* nonL23 = Literal::create2(opPred, false, v2, v3);
  Literal* l13 = Literal::create2(opPred, true, v1, v3);

  addTheoryClause(units, nonL12, nonL23, l13);
}

/**
 * Add axiom le(X,Y) | le(Y,X)
 */
void TheoryAxioms::addOrderingTotality(Interpretation lessEqual, UnitList*& units)
{
  CALL("TheoryAxioms::addOrderingTotality");
  ASS(!theory->isFunction(lessEqual));
  ASS_EQ(theory->getArity(lessEqual),2);

  unsigned opPred = env.signature->getInterpretingSymbol(lessEqual);
  TermList v1(0,false);
  TermList v2(1,false);

  Literal* l12 = Literal::create2(opPred, true, v1, v2);
  Literal* l21 = Literal::create2(opPred, true, v2, v1);

  addTheoryClause(units, l12, l21);
}

/**
 * Add axioms of reflexivity, transitivity and total ordering for predicate @c lessEqual
 */
void TheoryAxioms::addTotalOrderAxioms(Interpretation lessEqual, UnitList*& units)
{
  CALL("TheoryAxioms::addTotalOrderAxioms");

  addReflexivity(lessEqual, units);
  addTransitivity(lessEqual, units);
  addOrderingTotality(lessEqual, units);
}

/**
 * Add axiom ~le(X,Y) | le(X+Z,Y+Z)
 */
void TheoryAxioms::addMonotonicity(Interpretation lessEqual, Interpretation addition, UnitList*& units)
{
  CALL("TheoryAxioms::addMonotonicity");
  ASS(!theory->isFunction(lessEqual));
  ASS_EQ(theory->getArity(lessEqual),2);
  ASS(theory->isFunction(addition));
  ASS_EQ(theory->getArity(addition),2);

  unsigned lePred = env.signature->getInterpretingSymbol(lessEqual);
  unsigned addFun = env.signature->getInterpretingSymbol(addition);
  TermList v1(0,false);
  TermList v2(1,false);
  TermList v3(2,false);
  TermList v1Pv3(Term::create2(addFun, v1,v3));
  TermList v2Pv3(Term::create2(addFun, v2,v3));
  Literal* nonLe = Literal::create2(lePred, false, v1, v2);
  Literal* leAdded = Literal::create2(lePred, true, v1Pv3, v2Pv3);

  addTheoryClause(units, nonLe, leAdded);
}

/**
 * Add axioms for addition, unary minus and ordering
 */
void TheoryAxioms::addAdditionAndOrderingAxioms(Interpretation plus, Interpretation unaryMinus,
    TermList zeroElement, TermList oneElement, Interpretation lessEqual, UnitList*& units)
{
  CALL("TheoryAxioms::addAdditionAndOrderingAxioms");

  addCommutativeGroupAxioms(plus, unaryMinus, zeroElement, units);
  addTotalOrderAxioms(lessEqual, units);
  addMonotonicity(lessEqual, plus, units);

  //axiom( ile(zero,one) );
  unsigned lePred = env.signature->getInterpretingSymbol(lessEqual);
  Literal* nonLeOneZero = Literal::create2(lePred, false, oneElement, zeroElement);
  addTheoryUnit(nonLeOneZero, units);

  //axiom( (X0+one)<=X1 --> ~(X1<=X0) );
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  TermList v1(0,false);
  TermList v2(1,false);
  Literal* nonLe21 = Literal::create2(lePred, false, v2, v1);
  TermList v1POne(Term::create2(plusFun, v1, oneElement));
  Literal* nonLt1POne2 = Literal::create2(lePred, false, v1POne, v2);
  addTheoryClause(units, nonLe21, nonLt1POne2);

  //connect strict and non-strict inequality
  //axiom( (ile(X0,X1)) --> ((X0==X1) | ilt(X0,X1)) );

  unsigned varSort = theory->getOperationSort(lessEqual);
  Literal* v1EqV2 = Literal::createEquality(true, v1, v2, varSort);
  Literal* nonLe12 = Literal::create2(lePred, false, v1, v2);
  addTheoryClause(units, nonLe21, nonLe12, v1EqV2);
}

/**
 * Add axioms for addition, multiplication, unary minus and ordering
 */
void TheoryAxioms::addAdditionOrderingAndMultiplicationAxioms(Interpretation plus, Interpretation unaryMinus,
    TermList zeroElement, TermList oneElement, Interpretation lessEqual, Interpretation multiply,
    UnitList*& units)
{
  CALL("TheoryAxioms::addAdditionOrderingAndMultiplicationAxioms");

  unsigned srt = theory->getOperationSort(plus);
  ASS_EQ(srt, theory->getOperationSort(unaryMinus));
  ASS_EQ(srt, theory->getOperationSort(lessEqual));
  ASS_EQ(srt, theory->getOperationSort(multiply));

  addAdditionAndOrderingAxioms(plus, unaryMinus, zeroElement, oneElement, lessEqual, units);

  addCommutativity(multiply, units);
  addAssociativity(multiply, units);
  addIdentity(multiply, oneElement, units);

  //axiom( X0*zero==zero );
  unsigned mulFun = env.signature->getInterpretingSymbol(multiply);
  TermList v1(0,false);
  TermList v1MulZero(Term::create2(mulFun, v1, zeroElement));
  Literal* v1EqV1MulZero = Literal::createEquality(true, v1MulZero, zeroElement, srt);
  addTheoryUnit(v1EqV1MulZero, units);

  //axiom( X0*(X1++)==(X0*X1)+X0 );
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  TermList v2(1,false);
  TermList v2POne(Term::create2(plusFun, v2, oneElement));
  TermList v1MulV2POne(Term::create2(mulFun, v1, v2POne));
  TermList v1MulV2(Term::create2(mulFun, v1, v2));
  TermList v1MulV2PV1(Term::create2(plusFun, v1MulV2, v1));
  Literal* succDistrEq = Literal::createEquality(true, v1MulV2POne, v1MulV2PV1, srt);
  addTheoryUnit(succDistrEq, units);

  //axiom( (X0+X1)*(X2+X3) == (X0*X2 + X0*X3 + X1*X2 + X1*X3) );
  TermList v3(2,false);
  TermList v4(3,false);
  TermList v1Pv2(Term::create2(plusFun, v1, v2));
  TermList v3Pv4(Term::create2(plusFun, v3, v4));
  TermList distrLhs(Term::create2(mulFun, v1Pv2, v3Pv4));
  TermList v1Mv3(Term::create2(mulFun, v1, v3));
  TermList v1Mv4(Term::create2(mulFun, v1, v4));
  TermList v2Mv3(Term::create2(mulFun, v2, v3));
  TermList v2Mv4(Term::create2(mulFun, v2, v4));
  TermList add1(Term::create2(plusFun, v1Mv3, v1Mv4));
  TermList add2(Term::create2(plusFun, v2Mv3, v2Mv4));
  TermList distrRhs(Term::create2(plusFun, add1, add2));
  Literal* distrEq = Literal::createEquality(true, distrLhs, distrRhs, srt);
  addTheoryUnit(distrEq, units);
}

/**
 * Add axiom valid only for integer ordering: le(Y,X) | le(X+1,Y)
 */
void TheoryAxioms::addExtraIntegerOrderingAxiom(Interpretation plus, TermList oneElement, Interpretation lessEqual,
    UnitList*& units)
{
  CALL("TheoryAxioms::addExtraIntegerOrderingAxiom");

  //axiom( ~(X1<=X0) --> (X0+one)<=X1 );
  unsigned lePred = env.signature->getInterpretingSymbol(lessEqual);
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  TermList v1(0,false);
  TermList v2(1,false);
  Literal* le21 = Literal::create2(lePred, true, v2, v1);
  TermList v1POne(Term::create2(plusFun, v1, oneElement));
  Literal* lt1POne2 = Literal::create2(lePred, true, v1POne, v2);
  addTheoryClause(units, le21, lt1POne2);
}

//Axioms for integer division that hven't been implemented yet
//
//axiom( (ige(X0,zero) & igt(X1,zero)) --> ( ilt(X0-X1, idiv(X0,X1)*X1) & ile(idiv(X0,X1)*X1, X0) ) );
//axiom( (ilt(X0,zero) & ilt(X1,zero)) --> ( igt(X0-X1, idiv(X0,X1)*X1) & ige(idiv(X0,X1)*X1, X0) ) );
//axiom( (ige(X0,zero) & ilt(X1,zero)) --> ( ilt(X0+X1, idiv(X0,X1)*X1) & ile(idiv(X0,X1)*X1, X0) ) );
//axiom( (ilt(X0,zero) & igt(X1,zero)) --> ( igt(X0+X1, idiv(X0,X1)*X1) & ige(idiv(X0,X1)*X1, X0) ) );
//axiom( (ilt(X0,zero) & igt(X1,zero)) --> ( igt(X0+X1, idiv(X0,X1)*X1) & ige(idiv(X0,X1)*X1, X0) ) );
//axiom( (X1!=zero) --> (idiv(X0,X1)+X2==idiv(X0+(X1*X2),X1)) );

/**
 * Add theory axioms to the @b units list that are relevant to
 * units present in the list. The problem must have been processed
 * by the InterpretedNormalizer before using this rule.
 */
void TheoryAxioms::apply(Problem& prb)
{
  CALL("TheoryAxioms::apply(Problem&)");

  Property* prop = prb.getProperty();
  if(apply(prb.units(), prop)) {
    prb.invalidateProperty();
    prb.reportEqualityAdded(false);
  }
}

/**
 * Add theory axioms to the @b units list that are relevant to
 * units present in the list. The problem must have been processed
 * by the InterpretedNormalizer before using this rule.
 *
 * True is returned iff the list of units was modified.
 */
bool TheoryAxioms::apply(UnitList*& units, Property* prop)
{
  CALL("TheoryAxioms::apply");

  bool modified = false;
  {
    bool haveIntPlus =
	prop->hasInterpretedOperation(Theory::INT_PLUS) ||
	prop->hasInterpretedOperation(Theory::INT_UNARY_MINUS) ||
	prop->hasInterpretedOperation(Theory::INT_LESS_EQUAL) ||
	prop->hasInterpretedOperation(Theory::INT_MULTIPLY);
    bool haveIntMultiply =
	prop->hasInterpretedOperation(Theory::INT_MULTIPLY);
    if(haveIntPlus) {
      TermList zero(theory->representConstant(IntegerConstantType(0)));
      TermList one(theory->representConstant(IntegerConstantType(1)));
      if(haveIntMultiply) {
	addAdditionOrderingAndMultiplicationAxioms(Theory::INT_PLUS, Theory::INT_UNARY_MINUS, zero, one,
	    Theory::INT_LESS_EQUAL, Theory::INT_MULTIPLY, units);
      }
      else {
	addAdditionAndOrderingAxioms(Theory::INT_PLUS, Theory::INT_UNARY_MINUS, zero, one,
	    Theory::INT_LESS_EQUAL, units);
      }
      addExtraIntegerOrderingAxiom(Theory::INT_PLUS, one, Theory::INT_LESS_EQUAL, units);
      modified = true;
    }
  }

  {
    bool haveRatPlus =
	prop->hasInterpretedOperation(Theory::RAT_PLUS) ||
	prop->hasInterpretedOperation(Theory::RAT_UNARY_MINUS) ||
	prop->hasInterpretedOperation(Theory::RAT_LESS_EQUAL) ||
	prop->hasInterpretedOperation(Theory::RAT_MULTIPLY);
    bool haveRatMultiply =
	prop->hasInterpretedOperation(Theory::RAT_MULTIPLY);
    if(haveRatPlus) {
      TermList zero(theory->representConstant(RationalConstantType(0, 1)));
      TermList one(theory->representConstant(RationalConstantType(1, 1)));
      if(haveRatMultiply) {
	addAdditionOrderingAndMultiplicationAxioms(Theory::RAT_PLUS, Theory::RAT_UNARY_MINUS, zero, one,
	    Theory::RAT_LESS_EQUAL, Theory::RAT_MULTIPLY, units);
      }
      else {
	addAdditionAndOrderingAxioms(Theory::RAT_PLUS, Theory::RAT_UNARY_MINUS, zero, one,
	    Theory::RAT_LESS_EQUAL, units);
      }
      modified = true;
    }
  }

  {
    bool haveRealPlus =
	prop->hasInterpretedOperation(Theory::REAL_PLUS) ||
	prop->hasInterpretedOperation(Theory::REAL_UNARY_MINUS) ||
	prop->hasInterpretedOperation(Theory::REAL_LESS_EQUAL) ||
	prop->hasInterpretedOperation(Theory::REAL_MULTIPLY);
    bool haveRealMultiply =
	prop->hasInterpretedOperation(Theory::REAL_MULTIPLY);
    if(haveRealPlus) {
      TermList zero(theory->representConstant(RealConstantType(RationalConstantType(0, 1))));
      TermList one(theory->representConstant(RealConstantType(RationalConstantType(1, 1))));
      if(haveRealMultiply) {
	addAdditionOrderingAndMultiplicationAxioms(Theory::REAL_PLUS, Theory::REAL_UNARY_MINUS, zero, one,
	    Theory::REAL_LESS_EQUAL, Theory::REAL_MULTIPLY, units);
      }
      else {
	addAdditionAndOrderingAxioms(Theory::REAL_PLUS, Theory::REAL_UNARY_MINUS, zero, one,
	    Theory::REAL_LESS_EQUAL, units);
      }
      modified = true;
    }
  }
  return modified;
}

}
