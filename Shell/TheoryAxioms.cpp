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
#include "Kernel/Sorts.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Theory.hpp"

#include "AxiomGenerator.hpp"
#include "Property.hpp"
#include "SymCounter.hpp"
#include "TheoryAxioms.hpp"
#include "Options.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

/**
 * Add the unit @c to @c units and output it, if the option show_theory_axioms is on.
 * @since 11/11/2013 Manchester
 * @author Andrei Voronkov
 */
void TheoryAxioms::addAndOutputTheoryUnit(Unit* unit,UnitList*& units)
{
  CALL("TheoryAxioms::addAndOutputTheoryUnit");
  if (env.options->showTheoryAxioms()) {
    cout << "% Theory " << (unit->isClause() ? "clause" : "formula" ) << ": " << unit->toString() << "\n";
  }
  UnitList::push(unit,units);
} // addAndOutputTheoryUnit

/**
 * Add the theory unit clause with literal @c lit to @c units.
 * @since 11/11/2013, Manchester: output of the clause added
 * @author Andrei Voronkov
 */
void TheoryAxioms::addTheoryUnitClause(Literal* lit, UnitList*& units)
{
  CALL("TheoryAxioms::addTheoryUnitClause");
  Clause* unit = Clause::fromIterator(getSingletonIterator(lit), Unit::AXIOM, new Inference(Inference::THEORY));
  addAndOutputTheoryUnit(unit,units);
} // addTheoryUnitClause

/**
 * Add clause with literals @c lit1, @c lit2, @c lit3 to @c units.
 * @c lit3 can be null, in that case only the first two literals are used.
 *
 * @since 11/11/2013, Manchester: output of the clause added
 * @author Andrei Voronkov
 */
void TheoryAxioms::addTheoryNonUnitClause(UnitList*& units, Literal* lit1, Literal* lit2, Literal* lit3)
{
  CALL("TheoryAxioms::addTheoryNonUnitClause");
  LiteralStack lits;
  ASS(lit1);
  lits.push(lit1);
  ASS(lit2);
  lits.push(lit2);
  if (lit3) {
    lits.push(lit3);
  }
  Clause* cl = Clause::fromStack(lits, Unit::AXIOM, new Inference(Inference::THEORY));
  addAndOutputTheoryUnit(cl,units);
} // addTheoryNonUnitCLause

/**
 * Add the axiom f(X,Y)=f(Y,X).
 * @since 11/11/2013, Manchester: modified
 * @author Andrei Voronkov
 */
void TheoryAxioms::addCommutativity(Interpretation op,UnitList*& units)
{
  CALL("TheoryAxioms::addCommutativity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned f = env.signature->getInterpretingSymbol(op);
  unsigned srt = theory->getOperationSort(op);
  TermList x(0,false);
  TermList y(1,false);
  TermList fxy(Term::create2(f,x,y));
  TermList fyx(Term::create2(f,y,x));
  Literal* eq = Literal::createEquality(true,fxy,fyx,srt);
  addTheoryUnitClause(eq,units);
} // addCommutativity

/**
 * Add axiom f(X,f(Y,Z))=f(f(X,Y),Z).
 * @since 11/11/2013, Manchester: modified
 * @author Andrei Voronkov
 */
void TheoryAxioms::addAssociativity(Interpretation op, UnitList*& units)
{
  CALL("TheoryAxioms::addCommutativity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned f = env.signature->getInterpretingSymbol(op);
  unsigned srt = theory->getOperationSort(op);
  TermList x(0,false);
  TermList y(1,false);
  TermList z(2,false);
  TermList fxy(Term::create2(f,x,y));
  TermList fyz(Term::create2(f,y,z));
  TermList fx_fyz(Term::create2(f,x,fyz));
  TermList f_fxy_z(Term::create2(f,fxy,z));
  Literal* eq = Literal::createEquality(true, fx_fyz,f_fxy_z, srt);
  addTheoryUnitClause(eq, units);
} // addAsssociativity

/**
 * Add axiom f(X)=X
 * @author Giles
 */
void TheoryAxioms::addIdentity(Interpretation op, UnitList*& units)
{
  CALL("TheoryAxioms::addIdentity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),1);

  unsigned f = env.signature->getInterpretingSymbol(op);
  unsigned srt = theory->getOperationSort(op);
  TermList x(0,false);
  TermList fx(Term::create1(f,x));
  Literal* eq = Literal::createEquality(true,fx,x,srt);
  addTheoryUnitClause(eq,units);
} // addIdentity

/**
 * Add axiom f(X,e)=X.
 * @since 11/11/2013, Manchester: modified
 * @author Andrei Voronkov
 */
void TheoryAxioms::addRightIdentity(Interpretation op, TermList e, UnitList*& units)
{
  CALL("TheoryAxioms::addRightIdentity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned f = env.signature->getInterpretingSymbol(op);
  unsigned srt = theory->getOperationSort(op);
  TermList x(0,false);
  TermList fxe(Term::create2(f,x,e));
  Literal* eq = Literal::createEquality(true,fxe,x,srt);
  addTheoryUnitClause(eq, units);
} // addRightIdentity

/**
 * Add axioms for commutative group with addition @c op, inverse @c inverse and unit @c e:
 * <ol>
 * <li>f(X,Y)=f(Y,X) (commutativity)</li>
 * <li>f(X,f(Y,Z))=f(f(X,Y),Z) (associativity)</li>
 * <li>f(X,e)=X (right identity)</li>
 * <li>i(f(x,y)) = f(i(y),i(x))</li>
 * <li>f(x,i(x))=e (right inverse)</li>
 * </ol>
 * @since 11/11/2013, Manchester: modified
 * @author Andrei Voronkov
 */
void TheoryAxioms::addCommutativeGroupAxioms(Interpretation op, Interpretation inverse, TermList e, UnitList*& units)
{
  CALL("TheoryAxioms::addCommutativeGroupAxioms");

  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);
  ASS(theory->isFunction(inverse));
  ASS_EQ(theory->getArity(inverse),1);

  addCommutativity(op,units);
  addAssociativity(op,units);
  addRightIdentity(op,e,units);

  // i(f(x,y)) = f(i(y),i(x))
  unsigned f = env.signature->getInterpretingSymbol(op);
  unsigned i = env.signature->getInterpretingSymbol(inverse);
  unsigned srt = theory->getOperationSort(op);
  ASS_EQ(srt, theory->getOperationSort(inverse));

  TermList x(0,false);
  TermList y(1,false);
  TermList fxy(Term::create2(f,x,y));
  TermList ix(Term::create1(i,x));
  TermList iy(Term::create1(i,y));
  TermList i_fxy(Term::create1(i,fxy));
  TermList f_iy_ix(Term::create2(f,iy,ix));
  Literal* eq1 = Literal::createEquality(true,i_fxy,f_iy_ix,srt);
  addTheoryUnitClause(eq1, units);

  // f(x,i(x))=e
  TermList fx_ix(Term::create2(f,x,ix));
  Literal* eq2 = Literal::createEquality(true,fx_ix,e,srt);
  addTheoryUnitClause(eq2, units);
} // TheoryAxioms::addCommutativeGroupAxioms

/**
 * Add axiom op(X,X)
 */
void TheoryAxioms::addReflexivity(Interpretation op, UnitList*& units)
{
  CALL("TheoryAxioms::addReflexivity");

  ASS(!theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned opPred = env.signature->getInterpretingSymbol(op);
  TermList x(0,false);
  Literal* l11 = Literal::create2(opPred, true, x, x);
  addTheoryUnitClause(l11, units);
} // addReflexivity

/**
 * Add axiom ~op(X,Y) | ~op(Y,Z) | op(X,Z)
 */
void TheoryAxioms::addTransitivity(Interpretation op, UnitList*& units)
{
  CALL("TheoryAxioms::addTransitivity");
  ASS(!theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned opPred = env.signature->getInterpretingSymbol(op);
  TermList x(0,false);
  TermList y(1,false);
  TermList v3(2,false);

  Literal* nonL12 = Literal::create2(opPred, false, x, y);
  Literal* nonL23 = Literal::create2(opPred, false, y, v3);
  Literal* l13 = Literal::create2(opPred, true, x, v3);

  addTheoryNonUnitClause(units, nonL12, nonL23, l13);
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
  TermList x(0,false);
  TermList y(1,false);

  Literal* l12 = Literal::create2(opPred, true, x, y);
  Literal* l21 = Literal::create2(opPred, true, y, x);

  addTheoryNonUnitClause(units, l12, l21);
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
  TermList x(0,false);
  TermList y(1,false);
  TermList v3(2,false);
  TermList xPv3(Term::create2(addFun, x,v3));
  TermList yPv3(Term::create2(addFun, y,v3));
  Literal* nonLe = Literal::create2(lePred, false, x, y);
  Literal* leAdded = Literal::create2(lePred, true, xPv3, yPv3);

  addTheoryNonUnitClause(units, nonLe, leAdded);
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
  addTheoryUnitClause(nonLeOneZero, units);

  //axiom( (X0+one)<=X1 --> ~(X1<=X0) );
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  TermList x(0,false);
  TermList y(1,false);
  Literal* nonLe21 = Literal::create2(lePred, false, y, x);
  TermList xPOne(Term::create2(plusFun, x, oneElement));
  Literal* nonLt1POne2 = Literal::create2(lePred, false, xPOne, y);
  addTheoryNonUnitClause(units, nonLe21, nonLt1POne2);

  //connect strict and non-strict inequality
  //axiom( (ile(X0,X1)) --> ((X0==X1) | ilt(X0,X1)) );

  unsigned varSort = theory->getOperationSort(lessEqual);
  Literal* xEqY = Literal::createEquality(true, x, y, varSort);
  Literal* nonLe12 = Literal::create2(lePred, false, x, y);
  addTheoryNonUnitClause(units, nonLe21, nonLe12, xEqY);
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
  addRightIdentity(multiply, oneElement, units);

  //axiom( X0*zero==zero );
  unsigned mulFun = env.signature->getInterpretingSymbol(multiply);
  TermList x(0,false);
  TermList xMulZero(Term::create2(mulFun, x, zeroElement));
  Literal* xEqXMulZero = Literal::createEquality(true, xMulZero, zeroElement, srt);
  addTheoryUnitClause(xEqXMulZero, units);

  //axiom( X0*(X1++)==(X0*X1)+X0 );
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  TermList y(1,false);
  TermList yPOne(Term::create2(plusFun, y, oneElement));
  TermList xMulYPOne(Term::create2(mulFun, x, yPOne));
  TermList xMulY(Term::create2(mulFun, x, y));
  TermList xMulYPX(Term::create2(plusFun, xMulY, x));
  Literal* succDistrEq = Literal::createEquality(true, xMulYPOne, xMulYPX, srt);
  addTheoryUnitClause(succDistrEq, units);

  //axiom( (X0+X1)*(X2+X3) == (X0*X2 + X0*X3 + X1*X2 + X1*X3) );
  TermList v3(2,false);
  TermList v4(3,false);
  TermList xPy(Term::create2(plusFun, x, y));
  TermList v3Pv4(Term::create2(plusFun, v3, v4));
  TermList distrLhs(Term::create2(mulFun, xPy, v3Pv4));
  TermList xMv3(Term::create2(mulFun, x, v3));
  TermList xMv4(Term::create2(mulFun, x, v4));
  TermList yMv3(Term::create2(mulFun, y, v3));
  TermList yMv4(Term::create2(mulFun, y, v4));
  TermList add1(Term::create2(plusFun, xMv3, xMv4));
  TermList add2(Term::create2(plusFun, yMv3, yMv4));
  TermList distrRhs(Term::create2(plusFun, add1, add2));
  Literal* distrEq = Literal::createEquality(true, distrLhs, distrRhs, srt);
  addTheoryUnitClause(distrEq, units);
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
  TermList x(0,false);
  TermList y(1,false);
  Literal* le21 = Literal::create2(lePred, true, y, x);
  TermList xPOne(Term::create2(plusFun, x, oneElement));
  Literal* lt1POne2 = Literal::create2(lePred, true, xPOne, y);
  addTheoryNonUnitClause(units, le21, lt1POne2);
}
    
/**
 * Add axioms defining floor function
 * @author Giles
 */
void TheoryAxioms::addFloorAxioms(Interpretation floor, Interpretation lessEqual, Interpretation unaryMinus,
     Interpretation plus, TermList oneElement, UnitList*& units)
{
  CALL("TheoryAxioms::addFloorAxioms");

  unsigned lePred = env.signature->getInterpretingSymbol(lessEqual);
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  unsigned umFun = env.signature->getInterpretingSymbol(unaryMinus);
  unsigned floorFun = env.signature->getInterpretingSymbol(floor);
  TermList x(0,false);
  TermList floorX(Term::create1(floorFun,x));

  //axiom( floor(X) <= X )
  Literal* a1 = Literal::create2(lePred, true, floorX, x);
  addTheoryUnitClause(a1, units);

  //axiom( floor(X) > X-1 ) = axiom( ~ (X-1 <= floor(X)) ) as we eliminate all be le
  TermList m1(Term::create1(umFun,oneElement));
  TermList xm1(Term::create2(plusFun, x, m1));
  Literal* a2 = Literal::create2(lePred,false, xm1, floorX);
  addTheoryUnitClause(a2,units);
} //addFloorAxioms

/**
 * Add axioms defining ceiling function
 * @author Giles
 */ 
void TheoryAxioms::addCeilingAxioms(Interpretation ceiling, Interpretation lessEqual, 
     Interpretation plus, TermList oneElement, UnitList*& units)
{
  CALL("TheoryAxioms::addCeilingAxioms");

  unsigned lePred = env.signature->getInterpretingSymbol(lessEqual);
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  unsigned ceilingFun = env.signature->getInterpretingSymbol(ceiling);
  TermList x(0,false);
  TermList ceilingX(Term::create1(ceilingFun,x));

  //axiom( ceiling(X) >= X ) =  X <= ceiling(X)
  Literal* a1 = Literal::create2(lePred, true, x, ceilingX);
  addTheoryUnitClause(a1, units);

  //axiom( ceiling(X) < X+1 ) = X+1 > ceiling(X) = ~( X+1 <= ceiling(X)) 
  TermList xp1(Term::create2(plusFun, x, oneElement));
  Literal* a2 = Literal::create2(lePred,false, xp1, ceilingX);
  addTheoryUnitClause(a2,units);
} //addCeilingAxioms

/**
 * Add axioms defining round function
 * @author Giles
 */ 
void TheoryAxioms::addRoundAxioms(Interpretation round, Interpretation floor, Interpretation ceiling, UnitList*& units)
{
  CALL("TheoryAxioms::addRoundAxioms");
  
  //TODO... note that interesting as $round not in TPTP or translations
  // Suggested axioms:
  // round(x) = floor(x) | round(x) = ceiling(x)
  // x-0.5 > floor(x) => round(x) = ceiling(x)
  // x+0.5 < ceiling(x) => round(x) = floor(x)
  // x-0.5 = floor(x) => ?y : is_int(y) & 2*y = round(x)
  // x+0.5 = ceiling(x) => ?y : is_int(y) & 2*y = round(x)
  //NOT_IMPLEMENTED;

} //addRoundAxioms

/**
 * Add axioms defining truncate function
 * @author Giles
 */ 
void TheoryAxioms::addTruncateAxioms(Interpretation truncate, Interpretation lessEqual, Interpretation unaryMinus,
                      Interpretation plus, TermList zeroElement, TermList oneElement, UnitList*& units)
{
  CALL("TheoryAxioms::addTruncateAxioms");

  unsigned lePred = env.signature->getInterpretingSymbol(lessEqual);
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  unsigned umFun = env.signature->getInterpretingSymbol(unaryMinus);
  unsigned truncateFun = env.signature->getInterpretingSymbol(truncate);
  TermList x(0,false);
  TermList truncateX(Term::create1(truncateFun,x));

  TermList m1(Term::create1(umFun,oneElement));
  TermList xm1(Term::create2(plusFun,x,m1));
  TermList xp1(Term::create2(plusFun,x,oneElement));

  Literal* nzleX = Literal::create2(lePred,false,zeroElement,x);
  Literal* zleX = Literal::create2(lePred,true,zeroElement,x);

  //~(0<=x) |  truncate(x) <= x
  Literal* a1 = Literal::create2(lePred,true,truncateX,x);
  addTheoryNonUnitClause(units,nzleX,a1);

  //~(0<=x) | ~( truncate(x) <= x-1 )
  Literal* a2 = Literal::create2(lePred,false,truncateX,xm1);
  addTheoryNonUnitClause(units,nzleX,a2);

  //0<=x | x <= truncate(x)
  Literal* a3 = Literal::create2(lePred,true,x,truncateX);
  addTheoryNonUnitClause(units,zleX,a3);

  //0<=x | ~( x+1 <= truncate(x) )
  Literal* a4 = Literal::create2(lePred,false,xp1,truncateX);
  addTheoryNonUnitClause(units,zleX,a4);

} //addTruncateAxioms

/**
 * Adds the extensionality axiom of arrays (of type array1 or array2): 
 * select(X,sk(X,Y)) != select(Y,sk(X,Y)) | X = Y
 *
 * @author Laura Kovacs
 * @since 31/08/2012, Vienna
 * @since 11/11/2013 Manchester, updates
 * @author Andrei Voronkov
 * @since 05/01/2014 Vienna, add axiom in clause form (we need skolem function in other places)
 * @author Bernhard Kragl
*/
void TheoryAxioms::addArrayExtensionalityAxioms(
  Interpretation select,
  Interpretation store,
  unsigned skolemFn,
  UnitList*& units)
{
  CALL("TheoryAxioms::addArrayExtenstionalityAxioms");
        
  ASS(theory->isFunction(select));
  ASS(theory->isArrayOperation(select));
  ASS_EQ(theory->getArity(select),2);
              
  unsigned sel = env.signature->getInterpretingSymbol(select);
  unsigned rangeSort = theory->getArrayOperationSort(select);
  unsigned arraySort = theory->getArrayOperationSort(store);

  TermList x(0,false);
  TermList y(1,false);
  
  TermList sk(Term::create2(skolemFn, x, y)); //sk(x,y)
  TermList sel_x_sk(Term::create2(sel,x,sk)); //select(x,sk(x,y))
  TermList sel_y_sk(Term::create2(sel,y,sk)); //select(y,sk(x,y))
  Literal* eq = Literal::createEquality(true,x,y,arraySort); //x = y
  Literal* ineq = Literal::createEquality(false,sel_x_sk,sel_y_sk,rangeSort); //select(x,sk(x,y) != select(y,z)
  
  addTheoryNonUnitClause(units, eq, ineq);
} // addArrayExtensionalityAxiom    

/**
 * Adds the extensionality axiom of boolean arrays:
 * select(X, sk(X, Y)) <~> select(Y, sk(X, Y)) | X = Y
 *
 * @since 25/08/2015 Gothenburg
 * @author Evgeny Kotelnikov
 */
void TheoryAxioms::addBooleanArrayExtensionalityAxioms(
        Interpretation select,
        Interpretation store,
        unsigned skolemFn,
        UnitList*& units)
{
  CALL("TheoryAxioms::addBooleanArrayExtenstionalityAxioms");

  ASS(!theory->isFunction(select));
  ASS(theory->isArrayOperation(select));
  ASS_EQ(theory->getArity(select),2);

  unsigned sel = env.signature->getInterpretingSymbol(select);
  unsigned arraySort = theory->getArrayOperationSort(store);

  TermList x(0,false);
  TermList y(1,false);

  TermList sk(Term::create2(skolemFn, x, y)); //sk(x,y)
  Formula* x_neq_y = new AtomicFormula(Literal::createEquality(false,x,y,arraySort)); //x != y

  Formula* sel_x_sk = new AtomicFormula(Literal::create2(sel, true, x, sk)); //select(x,sk(x,y))
  Formula* sel_y_sk = new AtomicFormula(Literal::create2(sel, true, y, sk)); //select(y,sk(x,y))
  Formula* sx_neq_sy = new BinaryFormula(XOR, sel_x_sk, sel_y_sk); //select(x,sk(x,y)) <~> select(y,sk(x,y))

  Formula* axiom = new QuantifiedFormula(FORALL, new Formula::VarList(0, new Formula::VarList(1, 0)),
                                         new BinaryFormula(IMP, x_neq_y, sx_neq_sy));

  addAndOutputTheoryUnit(new FormulaUnit(axiom, new Inference(Inference::THEORY), Unit::AXIOM), units);
} // addBooleanArrayExtensionalityAxiom

/**
* Adds the write/select axiom of arrays (of type array1 or array2), 
 * @author Laura Kovacs
 * @since 31/08/2012, Vienna
*/
void TheoryAxioms::addArrayWriteAxioms(Interpretation select, Interpretation store, UnitList*& units)
{
  CALL("TheoryAxioms::addArrayWriteAxioms");
        
  ASS(theory->isFunction(select));
  ASS(theory->isArrayOperation(select));
  ASS_EQ(theory->getArity(select),2);
        
        
  unsigned func_select = env.signature->getInterpretingSymbol(select);
  unsigned func_store = env.signature->getInterpretingSymbol(store);

  unsigned rangeSort = theory->getArrayOperationSort(select);
  unsigned domainSort = theory->getArrayDomainSort(select);
  //unsigned arraySort = theory->getOperationSort(store);
        
  TermList i(0,false);
  TermList j(1,false);
  TermList v(2,false);
  TermList a(3,false);
  TermList args[] = {a, i, v};
        
  //axiom (!A: arraySort, !I:domainSort, !V:rangeSort: (select(store(A,I,V), I) = V
  TermList wAIV(Term::create(func_store, 3, args)); //store(A,I,V)
  TermList sWI(Term::create2(func_select, wAIV,i)); //select(wAIV,I)
  Literal* ax = Literal::createEquality(true, sWI, v, rangeSort);
  addTheoryUnitClause(ax, units);

  //axiom (!A: arraySort, !I,J:domainSort, !V:rangeSort: (I!=J)->(select(store(A,I,V), J) = select(A,J)
  TermList sWJ(Term::create2(func_select, wAIV,j)); //select(wAIV,J)
  TermList sAJ(Term::create2(func_select, a, j)); //select(A,J)
        
  Literal* indexEq = Literal::createEquality(true, i, j, domainSort);//!(!(I=J)) === I=J
  Literal* writeEq = Literal::createEquality(true, sWJ, sAJ, rangeSort);//(select(store(A,I,V), J) = select(A,J)
  addTheoryNonUnitClause(units, indexEq, writeEq);                      
} //

/**
* Adds the write/select axiom of arrays (of type array1 or array2),
 * @author Laura Kovacs
 * @since 31/08/2012, Vienna
*/
void TheoryAxioms::addBooleanArrayWriteAxioms(Interpretation select, Interpretation store, UnitList*& units)
{
  CALL("TheoryAxioms::addArrayWriteAxioms");

  ASS(!theory->isFunction(select));
  ASS(theory->isArrayOperation(select));
  ASS_EQ(theory->getArity(select),2);


  unsigned pred_select = env.signature->getInterpretingSymbol(select);
  unsigned func_store = env.signature->getInterpretingSymbol(store);

  unsigned rangeSort = theory->getArrayOperationSort(select);
  unsigned domainSort = theory->getArrayDomainSort(select);
  //unsigned arraySort = theory->getOperationSort(store);

  TermList i(0,false);
  TermList j(1,false);
  TermList v(2,false);
  TermList a(3,false);
  TermList args[] = {a, i, v};

  //axiom (!A: arraySort, !I:domainSort, !V:rangeSort: (select(store(A,I,V), I) <=> (V = $$true)
  TermList wAIV(Term::create(func_store, 3, args)); //store(A,I,V)
  Formula* sWI = new AtomicFormula(Literal::create2(pred_select, true, wAIV,i)); //select(wAIV,I)
  TermList true_(Term::createConstant(Signature::FOOL_TRUE));
  Formula* xeqt = new AtomicFormula(Literal::createEquality(true, true_, v, rangeSort));
  Formula* ax = new BinaryFormula(IFF, xeqt, sWI);
  addAndOutputTheoryUnit(new FormulaUnit(ax, new Inference(Inference::THEORY), Unit::AXIOM), units);

  //axiom (!A: arraySort, !I,J:domainSort, !V:rangeSort: (I!=J)->(select(store(A,I,V), J) <=> select(A,J)
  Formula* sWJ = new AtomicFormula(Literal::create2(pred_select, true, wAIV,j)); //select(wAIV,J)
  Formula* sAJ = new AtomicFormula(Literal::create2(pred_select, true, a, j)); //select(A,J)

  Formula* indexEq = new AtomicFormula(Literal::createEquality(false, i, j, domainSort));//I!=J
  Formula* writeEq = new BinaryFormula(IFF, sWJ, sAJ);//(select(store(A,I,V), J) <=> select(A,J)
  Formula* ax2 = new BinaryFormula(IMP, indexEq, writeEq);
  addAndOutputTheoryUnit(new FormulaUnit(ax2, new Inference(Inference::THEORY), Unit::AXIOM), units);
} //
    
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
 * by the InterpretedNormalizer before using this rule
 *
 * @return true iff the list of units was modified
 *
 * @since 11/11/2013, Manchester: bug fixes
 * @author Andrei Voronkov
 */
bool TheoryAxioms::apply(UnitList*& units, Property* prop)
{
  CALL("TheoryAxioms::apply");  
  bool modified = false;
  bool haveIntPlus =
    prop->hasInterpretedOperation(Theory::INT_PLUS) ||
    prop->hasInterpretedOperation(Theory::INT_UNARY_MINUS) ||
    prop->hasInterpretedOperation(Theory::INT_LESS_EQUAL) ||
    prop->hasInterpretedOperation(Theory::INT_MULTIPLY);
  bool haveIntMultiply =
    prop->hasInterpretedOperation(Theory::INT_MULTIPLY);

  bool haveIntFloor = prop->hasInterpretedOperation(Theory::INT_FLOOR);
  bool haveIntCeiling = prop->hasInterpretedOperation(Theory::INT_CEILING);
  bool haveIntRound = prop->hasInterpretedOperation(Theory::INT_ROUND);
  bool haveIntTruncate = prop->hasInterpretedOperation(Theory::INT_TRUNCATE);
  bool haveIntUnaryRoundingFunction = haveIntFloor || haveIntCeiling || haveIntRound || haveIntTruncate;

  if (haveIntPlus || haveIntUnaryRoundingFunction) {
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
    if(haveIntFloor){    addIdentity(Theory::INT_FLOOR,units); }
    if(haveIntCeiling){  addIdentity(Theory::INT_CEILING,units); }
    if(haveIntRound){    addIdentity(Theory::INT_ROUND,units); }
    if(haveIntTruncate){ addIdentity(Theory::INT_TRUNCATE,units); }
    modified = true;
  }
  bool haveRatPlus =
    prop->hasInterpretedOperation(Theory::RAT_PLUS) ||
    prop->hasInterpretedOperation(Theory::RAT_UNARY_MINUS) ||
    prop->hasInterpretedOperation(Theory::RAT_LESS_EQUAL) ||
    prop->hasInterpretedOperation(Theory::RAT_MULTIPLY);
  bool haveRatMultiply =
    prop->hasInterpretedOperation(Theory::RAT_MULTIPLY);

  bool haveRatFloor = prop->hasInterpretedOperation(Theory::RAT_FLOOR);
  bool haveRatCeiling = prop->hasInterpretedOperation(Theory::RAT_CEILING);
  bool haveRatRound = prop->hasInterpretedOperation(Theory::RAT_ROUND);
  bool haveRatTruncate = prop->hasInterpretedOperation(Theory::RAT_TRUNCATE);
  bool haveRatUnaryRoundingFunction = haveRatFloor || haveRatCeiling || haveRatRound || haveRatTruncate;

  if (haveRatPlus || haveRatUnaryRoundingFunction) {
    TermList zero(theory->representConstant(RationalConstantType(0, 1)));
    TermList one(theory->representConstant(RationalConstantType(1, 1)));
    if(haveRatMultiply || haveRatRound) {
      addAdditionOrderingAndMultiplicationAxioms(Theory::RAT_PLUS, Theory::RAT_UNARY_MINUS, zero, one,
						 Theory::RAT_LESS_EQUAL, Theory::RAT_MULTIPLY, units);
    }
    else {
      addAdditionAndOrderingAxioms(Theory::RAT_PLUS, Theory::RAT_UNARY_MINUS, zero, one,
				   Theory::RAT_LESS_EQUAL, units);
    }
    if(haveRatFloor || haveRatRound){
      addFloorAxioms(Theory::RAT_FLOOR,Theory::RAT_LESS_EQUAL,Theory::RAT_UNARY_MINUS,Theory::RAT_PLUS,one,units);
    }
    if(haveRatCeiling || haveRatRound){
      addCeilingAxioms(Theory::RAT_CEILING,Theory::RAT_LESS_EQUAL,Theory::RAT_PLUS,one,units);
    }
    if(haveRatRound){
      //addRoundAxioms(Theory::INT_TRUNCATE,Theory::INT_FLOOR,Theory::INT_CEILING,units);
    }
    if(haveRatTruncate){
      addTruncateAxioms(Theory::RAT_TRUNCATE,Theory::RAT_LESS_EQUAL,Theory::RAT_UNARY_MINUS,
                        Theory::RAT_PLUS,zero,one,units);
    }
    modified = true;
  }
  bool haveRealPlus =
    prop->hasInterpretedOperation(Theory::REAL_PLUS) ||
    prop->hasInterpretedOperation(Theory::REAL_UNARY_MINUS) ||
    prop->hasInterpretedOperation(Theory::REAL_LESS_EQUAL) ||
    prop->hasInterpretedOperation(Theory::REAL_MULTIPLY);
  bool haveRealMultiply =
    prop->hasInterpretedOperation(Theory::REAL_MULTIPLY);

  bool haveRealFloor = prop->hasInterpretedOperation(Theory::REAL_FLOOR);
  bool haveRealCeiling = prop->hasInterpretedOperation(Theory::REAL_CEILING);
  bool haveRealRound = prop->hasInterpretedOperation(Theory::REAL_ROUND);
  bool haveRealTruncate = prop->hasInterpretedOperation(Theory::REAL_TRUNCATE);
  bool haveRealUnaryRoundingFunction = haveRealFloor || haveRealCeiling || haveRealRound || haveRealTruncate;

  if (haveRealPlus || haveRealUnaryRoundingFunction) {
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
    if(haveRealFloor || haveRealRound){
      addFloorAxioms(Theory::REAL_FLOOR,Theory::REAL_LESS_EQUAL,Theory::REAL_UNARY_MINUS,Theory::REAL_PLUS,one,units);
    }
    if(haveRealCeiling || haveRealRound){
      addCeilingAxioms(Theory::REAL_CEILING,Theory::REAL_LESS_EQUAL,Theory::REAL_PLUS,one,units);
    }
    if(haveRealRound){
      //addRoundAxioms(Theory::INT_TRUNCATE,Theory::INT_FLOOR,Theory::INT_CEILING,units);
    }
    if(haveRealTruncate){
      addTruncateAxioms(Theory::REAL_TRUNCATE,Theory::REAL_LESS_EQUAL,Theory::REAL_UNARY_MINUS,
                        Theory::REAL_PLUS,zero,one,units);
    }

    modified = true;
  }


  VirtualIterator<unsigned> arraySorts = env.sorts->getArraySorts();
  while(arraySorts.hasNext()){
    unsigned arraySort = arraySorts.next();

    //cout << "Consider arraySort " << arraySort << endl;

    bool isBool = (env.sorts->getArraySort(arraySort)->getInnerSort() == Sorts::SRT_BOOL);

    // Get Interpretation objects for functions 
    Interpretation arraySelect = theory->getInterpretation(arraySort, isBool ? Theory::StructuredSortInterpretation::ARRAY_BOOL_SELECT
                                                                             : Theory::StructuredSortInterpretation::ARRAY_SELECT);
    Interpretation arrayStore  = theory->getInterpretation(arraySort,Theory::StructuredSortInterpretation::ARRAY_STORE);

    // Check if they are used
    bool haveSelect = prop->hasInterpretedOperation(arraySelect);
    bool haveStore = prop->hasInterpretedOperation(arrayStore);

    if (haveSelect || haveStore) {
      unsigned sk = theory->getArrayExtSkolemFunction(arraySort);
      if (isBool) {
        addBooleanArrayExtensionalityAxioms(arraySelect, arrayStore, sk, units);
      } else {
        addArrayExtensionalityAxioms(arraySelect, arrayStore, sk, units);
      }
      if (haveStore) {
        if (isBool) {
          addBooleanArrayWriteAxioms(arraySelect, arrayStore, units);
        } else {
          addArrayWriteAxioms(arraySelect, arrayStore, units);
        }
      }
      modified = true;
    }
  }

  return modified;
} // TheoryAxioms::apply

void TheoryAxioms::applyFOOL(Problem& prb) {
  CALL("TheoryAxioms::applyFOOL");

  static TermList t(Term::createConstant(Signature::FOOL_TRUE));
  static TermList f(Term::createConstant(Signature::FOOL_FALSE));

  // Add "$$true != $$false"
  Formula* inequality = new AtomicFormula(Literal::createEquality(false, t, f, Sorts::SRT_BOOL));
  Unit* disjointConstants = new FormulaUnit(inequality, new Inference(Inference::FOOL_AXIOM), Unit::AXIOM);
  addAndOutputTheoryUnit(disjointConstants, prb.units());

  // Do not add the finite domain axiom if --fool_paradomulation on
  if (env.options->FOOLParamodulation()) {
    return;
  }

  // Add "![X : $bool]: ((X = $$true) | (X = $$false))"
  Formula* xist = new AtomicFormula(Literal::createEquality(true, TermList(0, false), t, Sorts::SRT_BOOL));
  Formula* xisf = new AtomicFormula(Literal::createEquality(true, TermList(0, false), f, Sorts::SRT_BOOL));

  FormulaList* fs = new FormulaList(xist, new FormulaList(xisf, 0));
  Formula* disjunction = new QuantifiedFormula(FORALL, new Formula::VarList(0, 0), new JunctionFormula(OR, fs));
  Unit* finiteDomain = new FormulaUnit(disjunction, new Inference(Inference::FOOL_AXIOM), Unit::AXIOM);
  addAndOutputTheoryUnit(finiteDomain, prb.units());
} // TheoryAxioms::addBooleanDomainAxiom