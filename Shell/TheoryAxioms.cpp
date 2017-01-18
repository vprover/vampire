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
  addTheoryUnitClause(lit, new Inference(Inference::THEORY), units);
} // addTheoryUnitClause

void TheoryAxioms::addTheoryUnitClause(Literal* lit, Inference* inf, UnitList*& units)
{
  CALL("TheoryAxioms::addTheoryUnitClause");
  Clause* unit = Clause::fromIterator(getSingletonIterator(lit), Unit::AXIOM, inf);
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

void TheoryAxioms::addTheoryNonUnitClause(UnitList*& units, Literal* lit1, Literal* lit2, Literal* lit3,Literal* lit4)
{
  CALL("TheoryAxioms::addTheoryNonUnitClause");
  LiteralStack lits;
  ASS(lit1);
  lits.push(lit1);
  ASS(lit2);
  lits.push(lit2);
  ASS(lit3);
  lits.push(lit3);
  ASS(lit4);
  lits.push(lit4);
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
 * Add axiom f(e,X)=X.
 */
void TheoryAxioms::addLeftIdentity(Interpretation op, TermList e, UnitList*& units)
{
  CALL("TheoryAxioms::addLeftIdentity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned f = env.signature->getInterpretingSymbol(op);
  unsigned srt = theory->getOperationSort(op);
  TermList x(0,false);
  TermList fex(Term::create2(f,e,x));
  Literal* eq = Literal::createEquality(true,fex,x,srt);
  addTheoryUnitClause(eq, units);
} // addLeftIdentity

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
 * Add axiom op(op(x,i(y)),y) = x
 * e.g. (x+(-y))+y = x
 */
void TheoryAxioms::addRightInverse(Interpretation op, Interpretation inverse, UnitList*& units)
{
  TermList x(0,false);
  TermList y(0,false);
  unsigned f = env.signature->getInterpretingSymbol(op);
  unsigned i = env.signature->getInterpretingSymbol(inverse);
  unsigned srt = theory->getOperationSort(op);
  ASS_EQ(srt, theory->getOperationSort(inverse));

  TermList iy(Term::create1(i,y));
  TermList xiy(Term::create2(f,x,iy));
  TermList xiyy(Term::create2(f,xiy,y));
  Literal* eq = Literal::createEquality(true,xiyy,x,srt);
  addTheoryUnitClause(eq,units);
}

/**
 * Add axiom ~op(X,X)
 */
void TheoryAxioms::addNonReflexivity(Interpretation op, UnitList*& units)
{
  CALL("TheoryAxioms::addNonReflexivity");

  ASS(!theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned opPred = env.signature->getInterpretingSymbol(op);
  TermList x(0,false);
  Literal* l11 = Literal::create2(opPred, false, x, x);
  addTheoryUnitClause(l11, units);
} // addNonReflexivity

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
 * Add axiom less(X,Y) | less(Y,X) | X=Y
 */
void TheoryAxioms::addOrderingTotality(Interpretation less, UnitList*& units)
{
  CALL("TheoryAxioms::addOrderingTotality");
  ASS(!theory->isFunction(less));
  ASS_EQ(theory->getArity(less),2);

  unsigned opPred = env.signature->getInterpretingSymbol(less);
  TermList x(0,false);
  TermList y(1,false);

  Literal* l12 = Literal::create2(opPred, true, x, y);
  Literal* l21 = Literal::create2(opPred, true, y, x);

  unsigned srt = theory->getOperationSort(less);
  Literal* eq = Literal::createEquality(true,x,y,srt);

  addTheoryNonUnitClause(units, l12, l21,eq);
}

/**
 * Add axioms of reflexivity, transitivity and total ordering for predicate @c less
 */
void TheoryAxioms::addTotalOrderAxioms(Interpretation less, UnitList*& units)
{
  CALL("TheoryAxioms::addTotalOrderAxioms");

  addNonReflexivity(less, units);
  addTransitivity(less, units);
  addOrderingTotality(less, units);
}

/**
 * Add axiom ~less(X,Y) | less(X+Z,Y+Z)
 */
void TheoryAxioms::addMonotonicity(Interpretation less, Interpretation addition, UnitList*& units)
{
  CALL("TheoryAxioms::addMonotonicity");
  ASS(!theory->isFunction(less));
  ASS_EQ(theory->getArity(less),2);
  ASS(theory->isFunction(addition));
  ASS_EQ(theory->getArity(addition),2);

  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  unsigned addFun = env.signature->getInterpretingSymbol(addition);
  TermList x(0,false);
  TermList y(1,false);
  TermList v3(2,false);
  TermList xPv3(Term::create2(addFun, x,v3));
  TermList yPv3(Term::create2(addFun, y,v3));
  Literal* nonLe = Literal::create2(lessPred, false, x, y);
  Literal* leAdded = Literal::create2(lessPred, true, xPv3, yPv3);

  addTheoryNonUnitClause(units, nonLe, leAdded);
}

/**
 * Add the axiom $less(X,$sum(X,1))
 *
 * Taken from SPASS+T work
 */
void TheoryAxioms::addPlusOneGreater(Interpretation plus, TermList oneElement,
                                     Interpretation less, UnitList*& units)
{
  CALL("TheoryAxioms::addPlusOneGreater");
  ASS(!theory->isFunction(less));
  ASS_EQ(theory->getArity(less),2);
  ASS(theory->isFunction(plus));
  ASS_EQ(theory->getArity(plus),2);

  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  unsigned addFun = env.signature->getInterpretingSymbol(plus);
  TermList x(0,false);

  TermList xPo(Term::create2(addFun,x,oneElement));
  Literal* xPo_g_x = Literal::create2(lessPred,true,x,xPo);
  addTheoryUnitClause(xPo_g_x,units);
}

/**
 * Add axioms for addition, unary minus and ordering
 */
void TheoryAxioms::addAdditionAndOrderingAxioms(Interpretation plus, Interpretation unaryMinus,
    TermList zeroElement, TermList oneElement, Interpretation less, UnitList*& units)
{
  CALL("TheoryAxioms::addAdditionAndOrderingAxioms");

  addCommutativeGroupAxioms(plus, unaryMinus, zeroElement, units);
  addTotalOrderAxioms(less, units);
  addMonotonicity(less, plus, units);

  // y < x+one | x<y
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  TermList x(0,false);
  TermList y(1,false);
  Literal* xLy = Literal::create2(lessPred,true,x,y);
  TermList xP(Term::create2(plusFun,x,oneElement));
  Literal* yLxP = Literal::create2(lessPred,true,y,xP);
  addTheoryNonUnitClause(units,xLy,yLxP);

  // add that --x = x
  unsigned varSort = theory->getOperationSort(unaryMinus);
  unsigned unaryMinusFun = env.signature->getInterpretingSymbol(unaryMinus);
  TermList mx(Term::create1(unaryMinusFun,x));
  TermList mmx(Term::create1(unaryMinusFun,mx));
  Literal* mmxEqx = Literal::createEquality(true,mmx,x,varSort);
  addTheoryUnitClause(mmxEqx,units);

}

/**
 * Add axioms for addition, multiplication, unary minus and ordering
 */
void TheoryAxioms::addAdditionOrderingAndMultiplicationAxioms(Interpretation plus, Interpretation unaryMinus,
    TermList zeroElement, TermList oneElement, Interpretation less, Interpretation multiply,
    UnitList*& units)
{
  CALL("TheoryAxioms::addAdditionOrderingAndMultiplicationAxioms");

  unsigned srt = theory->getOperationSort(plus);
  ASS_EQ(srt, theory->getOperationSort(unaryMinus));
  ASS_EQ(srt, theory->getOperationSort(less));
  ASS_EQ(srt, theory->getOperationSort(multiply));

  addAdditionAndOrderingAxioms(plus, unaryMinus, zeroElement, oneElement, less, units);

  addCommutativity(multiply, units);
  addAssociativity(multiply, units);
  addRightIdentity(multiply, oneElement, units);

  //axiom( X0*zero==zero );
  unsigned mulFun = env.signature->getInterpretingSymbol(multiply);
  TermList x(0,false);
  TermList xMulZero(Term::create2(mulFun, x, zeroElement));
  Literal* xEqXMulZero = Literal::createEquality(true, xMulZero, zeroElement, srt);
  addTheoryUnitClause(xEqXMulZero, units);

  // Distributivity
  //axiom x*(y+z) = (x*y)+(x*z)

  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  TermList y(1,false);
  TermList z(2,false);

  TermList yPz(Term::create2(plusFun,y,z));
  TermList xTyPz(Term::create2(mulFun,x,yPz));

  TermList xTy(Term::create2(mulFun,x,y));
  TermList xTz(Term::create2(mulFun,x,z));
  TermList xTyPxTz(Term::create2(plusFun,xTy,xTz));
  
  Literal* distrib = Literal::createEquality(true, xTyPz, xTyPxTz,srt);
  addTheoryUnitClause(distrib,units);

  // Divisibility
  // (x != 0 & x times z = y & x times w = y) -> z = w
  // x=0 | x*z != y | x*w != y | z=w
  TermList w(3,false);
  Literal* xEz = Literal::createEquality(true,x,zeroElement,srt);
  TermList xTw(Term::create2(mulFun,x,w));
  Literal* xTznEy = Literal::createEquality(false,xTz,y,srt); 
  Literal* xTwnEy = Literal::createEquality(false,xTw,y,srt); 
  Literal* zEw = Literal::createEquality(true,z,w,srt);

  addTheoryNonUnitClause(units,xEz,xTznEy,xTwnEy,zEw);
  
}

/**
 * Add axioms for integer division
 * Also modulo and abs functions
 */
void TheoryAxioms::addIntegerDivisionWithModuloAxioms(Interpretation plus, Interpretation unaryMinus, Interpretation less,
                                Interpretation multiply, Interpretation divide, Interpretation divides,
                                Interpretation modulo, Interpretation abs, TermList zeroElement,
                                TermList oneElement, UnitList*& units)
{
  CALL("TheoryAxioms::addIntegerDivisionWithModuloAxioms");


  unsigned srt = theory->getOperationSort(plus);
  ASS_EQ(srt, theory->getOperationSort(unaryMinus));
  ASS_EQ(srt, theory->getOperationSort(less));
  ASS_EQ(srt, theory->getOperationSort(multiply));
  ASS_EQ(srt, theory->getOperationSort(divide));
  ASS_EQ(srt, theory->getOperationSort(divides));
  ASS_EQ(srt, theory->getOperationSort(modulo));
  ASS_EQ(srt, theory->getOperationSort(abs));

  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  unsigned umFun = env.signature->getInterpretingSymbol(unaryMinus);
  unsigned mulFun = env.signature->getInterpretingSymbol(multiply);
  unsigned divFun = env.signature->getInterpretingSymbol(divide);
  unsigned modFun = env.signature->getInterpretingSymbol(modulo);
  unsigned absFun = env.signature->getInterpretingSymbol(abs);
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);

  addIntegerAbsAxioms(abs,less,unaryMinus,zeroElement,units);

  TermList x(1,false);
  TermList y(2,false);

  // divides
  //TODO

  Literal* yis0 = Literal::createEquality(true,y,zeroElement,srt);
  TermList modxy(Term::create2(modFun,x,y));

  //y!=0 => x = modulo(x,y) +  multiply(y,div(x,y))

  TermList divxy(Term::create2(divFun,x,y));
  TermList mulydivxy(Term::create2(mulFun,y,divxy));
  TermList sum(Term::create2(plusFun,modxy,mulydivxy));
  Literal* xeqsum = Literal::createEquality(true,x,sum,srt);
  addTheoryNonUnitClause(units,yis0,xeqsum);

  // y!=0 => (0 <= mod(x,y))
  // y=0 | ~(mod(x,y) < 0)
  Literal* modxyge0 = Literal::create2(lessPred,false,modxy,zeroElement);
  addTheoryNonUnitClause(units,yis0,modxyge0);

  // y!=0 => (mod(x,y) <= abs(y)-1)
  // y=0 | ~( abs(y)-1 < mod(x,y) )
  TermList absy(Term::create1(absFun,y));
  TermList m1(Term::create1(umFun,oneElement));
  TermList absym1(Term::create2(plusFun,absy,m1));
  Literal* modxyleabsym1 = Literal::create2(lessPred,false,absym1,modxy);
  addTheoryNonUnitClause(units,yis0,modxyleabsym1);

}

void TheoryAxioms::addIntegerDividesAxioms(Interpretation divides, Interpretation multiply, TermList zero, TermList n, UnitList*& units)
{
  CALL("TheoryAxioms::addIntegerDividesAxioms");

#if VDEBUG
  // ASSERT n>0
  ASS(theory->isInterpretedConstant(n)); 
  IntegerConstantType nc;
  ALWAYS(theory->tryInterpretConstant(n,nc));
  ASS(nc.toInner()>0);
#endif

// ![Y] : (divides(n,Y) <=> ?[Z] : multiply(Z,n) = Y)

  unsigned srt = theory->getOperationSort(divides);
  ASS_EQ(srt, theory->getOperationSort(multiply));

  unsigned divsPred = env.signature->getInterpretingSymbol(divides);
  unsigned mulFun   = env.signature->getInterpretingSymbol(multiply);

  TermList y(1,false);
  TermList z(2,false);

// divides(n,Y) | multiply(Z,n) != Y 
  Literal* divsXY = Literal::create2(divsPred,true,n,y);
  TermList mZX(Term::create2(mulFun,z,n));
  Literal* mZXneY = Literal::createEquality(false,mZX,y,srt);
  addTheoryNonUnitClause(units,divsXY,mZXneY);

// ~divides(n,Y) | multiply(skolem(n,Y),n)=Y
  Literal* ndivsXY = Literal::create2(divsPred,false,n,y);
  
  // create a skolem function with signature srt*srt>srt
  unsigned skolem = env.signature->addSkolemFunction(2);
  Signature::Symbol* sym = env.signature->getFunction(skolem);
  sym->setType(new FunctionType({srt,srt},srt));
  TermList skXY(Term::create2(skolem,n,y));
  TermList msxX(Term::create2(mulFun,skXY,n));
  Literal* msxXeqY = Literal::createEquality(true,msxX,y,srt);

  addTheoryNonUnitClause(units,ndivsXY,msxXeqY);

}

void TheoryAxioms::addIntegerAbsAxioms(Interpretation abs, Interpretation less, 
                                       Interpretation unaryMinus, TermList zeroElement, UnitList*& units)
{
  CALL("TheoryAxioms::addIntegerAbsAxioms");

  unsigned srt = theory->getOperationSort(abs);
  ASS_EQ(srt, theory->getOperationSort(less));
  ASS_EQ(srt, theory->getOperationSort(unaryMinus));

  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  unsigned absFun = env.signature->getInterpretingSymbol(abs);
  unsigned umFun = env.signature->getInterpretingSymbol(unaryMinus);

  TermList x(1,false);
  TermList absX(Term::create1(absFun,x));
  TermList mx(Term::create1(umFun,x));
  TermList absmX(Term::create1(absFun,mx));

  // If x is positive then abs(x)=x 
  // If x is negative then abs(x)=-x 

  Literal* xNeg = Literal::create2(lessPred,false,zeroElement,x); // not 0<x
  Literal* xPos = Literal::create2(lessPred,false,x,zeroElement); // not x<0

  Literal* absXeqX = Literal::createEquality(true,absX,x,srt);
  Literal* absXeqmX = Literal::createEquality(true,absX,mx,srt);

  addTheoryNonUnitClause(units,xNeg,absXeqX);
  addTheoryNonUnitClause(units,xPos,absXeqmX);

}


/**
 * Add axioms for quotient i.e. rat or real division 
 */
void TheoryAxioms::addQuotientAxioms(Interpretation quotient, Interpretation multiply,
    TermList zeroElement, TermList oneElement, Interpretation less, 
    UnitList*& units)
{
  CALL("TheoryAxioms::addQuotientAxioms");

  unsigned srt = theory->getOperationSort(quotient);
  ASS_EQ(srt, theory->getOperationSort(multiply));
  ASS_EQ(srt, theory->getOperationSort(less));

  TermList x(1,false);
  TermList y(2,false);

  unsigned mulFun = env.signature->getInterpretingSymbol(multiply);
  unsigned divFun = env.signature->getInterpretingSymbol(quotient);

  Literal* guardx = Literal::createEquality(true,x,zeroElement,srt); 

  // x=0 | quotient(x,x)=1, easily derivable!
  //TermList qXX(Term::create2(quotient,x,x));
  //Literal* xQxis1 = Literal::createEquality(true,qXX,oneElement,srt);
  //addTheoryNonUnitClause(units,guardx,xQxis1);

  // x=0 | quotient(1,x)!=0
  TermList q1X(Term::create2(divFun,oneElement,x));
  Literal* oQxnot0 = Literal::createEquality(false,q1X,zeroElement,srt);
  addTheoryNonUnitClause(units,guardx,oQxnot0);

  // quotient(x,1)=x, easily derivable!
  //TermList qX1(Term::create2(quotient,x,oneElement));
  //Literal* qx1isx = Literal::createEquality(true,qX1,x,srt);
  //addTheoryUnitClause(qx1isx,units);

  // x=0 | quotient(multiply(y,x),x)=y
  TermList myx(Term::create2(mulFun,y,x));
  TermList qmx(Term::create2(divFun,myx,x));
  Literal* qmxisy = Literal::createEquality(true,qmx,y,srt);
  addTheoryNonUnitClause(units,guardx,qmxisy);


}

/**
 * Add axiom valid only for integer ordering: Y>X ->  Y => X+1 
 *
 * ~(x<y) | ~(y,x+1)
 */
void TheoryAxioms::addExtraIntegerOrderingAxiom(Interpretation plus, TermList oneElement, Interpretation less,
    UnitList*& units)
{
  CALL("TheoryAxioms::addExtraIntegerOrderingAxiom");

  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  TermList x(0,false);
  TermList y(1,false);
  Literal* nxLy = Literal::create2(lessPred, false, x, y);
  TermList xPOne(Term::create2(plusFun, x, oneElement));
  Literal* nyLxPOne = Literal::create2(lessPred, false, y,xPOne);
  addTheoryNonUnitClause(units, nxLy, nyLxPOne);
}
    
/**
 * Add axioms defining floor function
 * @author Giles
 */
void TheoryAxioms::addFloorAxioms(Interpretation floor, Interpretation less, Interpretation unaryMinus,
     Interpretation plus, TermList oneElement, UnitList*& units)
{
  CALL("TheoryAxioms::addFloorAxioms");

  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  unsigned umFun = env.signature->getInterpretingSymbol(unaryMinus);
  unsigned floorFun = env.signature->getInterpretingSymbol(floor);
  TermList x(0,false);
  TermList floorX(Term::create1(floorFun,x));

  //axiom( floor(X) <= X )
  // is ~(X < floor(X))
  Literal* a1 = Literal::create2(lessPred, false, x, floorX);
  addTheoryUnitClause(a1, units);

  //axiom( X-1 < floor(X) ) 
  TermList m1(Term::create1(umFun,oneElement));
  TermList xm1(Term::create2(plusFun, x, m1));
  Literal* a2 = Literal::create2(lessPred,true, xm1, floorX);
  addTheoryUnitClause(a2,units);
} //addFloorAxioms

/**
 * Add axioms defining ceiling function
 * @author Giles
 */ 
void TheoryAxioms::addCeilingAxioms(Interpretation ceiling, Interpretation less, 
     Interpretation plus, TermList oneElement, UnitList*& units)
{
  CALL("TheoryAxioms::addCeilingAxioms");

  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  unsigned ceilingFun = env.signature->getInterpretingSymbol(ceiling);
  TermList x(0,false);
  TermList ceilingX(Term::create1(ceilingFun,x));

  //axiom( ceiling(X) >= X ) 
  // is ~( ceiling(X) < X )
  Literal* a1 = Literal::create2(lessPred, false, ceilingX, x);
  addTheoryUnitClause(a1, units);

  //axiom( ceiling(X) < X+1 ) 
  TermList xp1(Term::create2(plusFun, x, oneElement));
  Literal* a2 = Literal::create2(lessPred,true, ceilingX, xp1);
  addTheoryUnitClause(a2,units);
} //addCeilingAxioms

/**
 * Add axioms defining round function
 * @author Giles
 */ 
void TheoryAxioms::addRoundAxioms(Interpretation round, Interpretation floor, Interpretation ceiling, UnitList*& units)
{
  CALL("TheoryAxioms::addRoundAxioms");
  
  //TODO... not that interesting as $round not in TPTP or translations
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
 * truncate is 'towards zero'
 *
 * >> x positive
 * x<0 | ~( x < tr(x) )		// x-1 < tr(x) <= x 
 * x<0 | x-1 < tr(x) 
 *
 * >> x negative
 * ~(x<0) | ~( tr(x) < x )	// x <= tr(x) < x+1 
 * ~(x<0) | tr(x) < x+1
 *
 * @author Giles
 */ 
void TheoryAxioms::addTruncateAxioms(Interpretation truncate, Interpretation less, Interpretation unaryMinus,
                      Interpretation plus, TermList zeroElement, TermList oneElement, UnitList*& units)
{
  CALL("TheoryAxioms::addTruncateAxioms");

  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  unsigned umFun = env.signature->getInterpretingSymbol(unaryMinus);
  unsigned truncateFun = env.signature->getInterpretingSymbol(truncate);
  TermList x(0,false);
  TermList truncateX(Term::create1(truncateFun,x));

  TermList m1(Term::create1(umFun,oneElement));
  TermList xm1(Term::create2(plusFun,x,m1));
  TermList xp1(Term::create2(plusFun,x,oneElement));

  Literal* xLz = Literal::create2(lessPred,true,x,zeroElement);
  Literal* nxLz= Literal::create2(lessPred,false,x,zeroElement);

  //x<0 | ~( x < tr(x) )
  Literal* a1 = Literal::create2(lessPred,false,x,truncateX);
  addTheoryNonUnitClause(units,xLz,a1);

  //x<0 | x-1 < tr(x)
  Literal* a2 = Literal::create2(lessPred,true,xm1,truncateX);
  addTheoryNonUnitClause(units,xLz,a2);

  // ~(x<0) | ~( tr(x) < x )
  Literal* a3 = Literal::create2(lessPred,false,truncateX,x);
  addTheoryNonUnitClause(units,nxLz,a3);

  // ~(x<0) | tr(x) < x+1
  Literal* a4 = Literal::create2(lessPred,true,truncateX,xp1);
  addTheoryNonUnitClause(units,nxLz,a4);

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
                                         new Formula::SortList(arraySort, new Formula::SortList(arraySort,0)),
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
  TermList true_(Term::foolTrue());
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
    prop->hasInterpretedOperation(Theory::INT_LESS) ||
    prop->hasInterpretedOperation(Theory::INT_MULTIPLY);
  bool haveIntMultiply =
    prop->hasInterpretedOperation(Theory::INT_MULTIPLY);

  bool haveIntDivision =
    prop->hasInterpretedOperation(Theory::INT_QUOTIENT_E) || // let's ignore the weird _F and _T for now!
    prop->hasInterpretedOperation(Theory::INT_REMAINDER_E) ||
    prop->hasInterpretedOperation(Theory::INT_ABS);

  bool haveIntDivides = prop->hasInterpretedOperation(Theory::INT_DIVIDES);

  bool haveIntFloor = prop->hasInterpretedOperation(Theory::INT_FLOOR);
  bool haveIntCeiling = prop->hasInterpretedOperation(Theory::INT_CEILING);
  bool haveIntRound = prop->hasInterpretedOperation(Theory::INT_ROUND);
  bool haveIntTruncate = prop->hasInterpretedOperation(Theory::INT_TRUNCATE);
  bool haveIntUnaryRoundingFunction = haveIntFloor || haveIntCeiling || haveIntRound || haveIntTruncate;

  if (haveIntPlus || haveIntUnaryRoundingFunction || haveIntDivision || haveIntDivides) {
    TermList zero(theory->representConstant(IntegerConstantType(0)));
    TermList one(theory->representConstant(IntegerConstantType(1)));
    if(haveIntMultiply || haveIntDivision || haveIntDivides) {
      addAdditionOrderingAndMultiplicationAxioms(Theory::INT_PLUS, Theory::INT_UNARY_MINUS, zero, one,
						 Theory::INT_LESS, Theory::INT_MULTIPLY, units);
      if(haveIntDivision){
        addIntegerDivisionWithModuloAxioms(Theory::INT_PLUS, Theory::INT_UNARY_MINUS, Theory::INT_LESS,
                                 Theory::INT_MULTIPLY, Theory::INT_QUOTIENT_E, Theory::INT_DIVIDES,
                                 Theory::INT_REMAINDER_E, Theory::INT_ABS, zero,one, units);
      }
      else if(haveIntDivides){ 
        Stack<TermList>& ns = env.signature->getDividesNvalues(); 
        Stack<TermList>::Iterator nsit(ns);
        while(nsit.hasNext()){
          TermList n = nsit.next();
          addIntegerDividesAxioms(Theory::INT_DIVIDES,Theory::INT_MULTIPLY,zero,n,units); 
        }
      }
    }
    else {
      addAdditionAndOrderingAxioms(Theory::INT_PLUS, Theory::INT_UNARY_MINUS, zero, one,
				   Theory::INT_LESS, units);
    }
    addExtraIntegerOrderingAxiom(Theory::INT_PLUS, one, Theory::INT_LESS, units);
    modified = true;
  }
  bool haveRatPlus =
    prop->hasInterpretedOperation(Theory::RAT_PLUS) ||
    prop->hasInterpretedOperation(Theory::RAT_UNARY_MINUS) ||
    prop->hasInterpretedOperation(Theory::RAT_LESS) ||
    prop->hasInterpretedOperation(Theory::RAT_QUOTIENT) ||
    prop->hasInterpretedOperation(Theory::RAT_MULTIPLY);
  bool haveRatMultiply =
    prop->hasInterpretedOperation(Theory::RAT_MULTIPLY);
  bool haveRatQuotient =
    prop->hasInterpretedOperation(Theory::RAT_QUOTIENT);

  bool haveRatFloor = prop->hasInterpretedOperation(Theory::RAT_FLOOR);
  bool haveRatCeiling = prop->hasInterpretedOperation(Theory::RAT_CEILING);
  bool haveRatRound = prop->hasInterpretedOperation(Theory::RAT_ROUND);
  bool haveRatTruncate = prop->hasInterpretedOperation(Theory::RAT_TRUNCATE);
  bool haveRatUnaryRoundingFunction = haveRatFloor || haveRatCeiling || haveRatRound || haveRatTruncate;

  if (haveRatPlus || haveRatUnaryRoundingFunction) {
    TermList zero(theory->representConstant(RationalConstantType(0, 1)));
    TermList one(theory->representConstant(RationalConstantType(1, 1)));
    if(haveRatMultiply || haveRatRound || haveRatQuotient) {
      addAdditionOrderingAndMultiplicationAxioms(Theory::RAT_PLUS, Theory::RAT_UNARY_MINUS, zero, one,
						 Theory::RAT_LESS, Theory::RAT_MULTIPLY, units);

      if(haveRatQuotient){
        addQuotientAxioms(Theory::RAT_QUOTIENT,Theory::RAT_MULTIPLY,zero,one,Theory::RAT_LESS,units);
      }
    }
    else {
      addAdditionAndOrderingAxioms(Theory::RAT_PLUS, Theory::RAT_UNARY_MINUS, zero, one,
				   Theory::RAT_LESS, units);
    }
    if(haveRatFloor || haveRatRound){
      addFloorAxioms(Theory::RAT_FLOOR,Theory::RAT_LESS,Theory::RAT_UNARY_MINUS,Theory::RAT_PLUS,one,units);
    }
    if(haveRatCeiling || haveRatRound){
      addCeilingAxioms(Theory::RAT_CEILING,Theory::RAT_LESS,Theory::RAT_PLUS,one,units);
    }
    if(haveRatRound){
      //addRoundAxioms(Theory::INT_TRUNCATE,Theory::INT_FLOOR,Theory::INT_CEILING,units);
    }
    if(haveRatTruncate){
      addTruncateAxioms(Theory::RAT_TRUNCATE,Theory::RAT_LESS,Theory::RAT_UNARY_MINUS,
                        Theory::RAT_PLUS,zero,one,units);
    }
    modified = true;
  }
  bool haveRealPlus =
    prop->hasInterpretedOperation(Theory::REAL_PLUS) ||
    prop->hasInterpretedOperation(Theory::REAL_UNARY_MINUS) ||
    prop->hasInterpretedOperation(Theory::REAL_LESS) ||
    prop->hasInterpretedOperation(Theory::REAL_QUOTIENT) ||
    prop->hasInterpretedOperation(Theory::REAL_MULTIPLY);
  bool haveRealMultiply =
    prop->hasInterpretedOperation(Theory::REAL_MULTIPLY);
  bool haveRealQuotient =
    prop->hasInterpretedOperation(Theory::REAL_QUOTIENT);

  bool haveRealFloor = prop->hasInterpretedOperation(Theory::REAL_FLOOR);
  bool haveRealCeiling = prop->hasInterpretedOperation(Theory::REAL_CEILING);
  bool haveRealRound = prop->hasInterpretedOperation(Theory::REAL_ROUND);
  bool haveRealTruncate = prop->hasInterpretedOperation(Theory::REAL_TRUNCATE);
  bool haveRealUnaryRoundingFunction = haveRealFloor || haveRealCeiling || haveRealRound || haveRealTruncate;

  if (haveRealPlus || haveRealUnaryRoundingFunction) {
    TermList zero(theory->representConstant(RealConstantType(RationalConstantType(0, 1))));
    TermList one(theory->representConstant(RealConstantType(RationalConstantType(1, 1))));
    if(haveRealMultiply || haveRealQuotient) {
      addAdditionOrderingAndMultiplicationAxioms(Theory::REAL_PLUS, Theory::REAL_UNARY_MINUS, zero, one,
						 Theory::REAL_LESS, Theory::REAL_MULTIPLY, units);

      if(haveRealQuotient){
        addQuotientAxioms(Theory::REAL_QUOTIENT,Theory::REAL_MULTIPLY,zero,one,Theory::REAL_LESS,units);
      }
    }
    else {
      addAdditionAndOrderingAxioms(Theory::REAL_PLUS, Theory::REAL_UNARY_MINUS, zero, one,
				   Theory::REAL_LESS, units);
    }
    if(haveRealFloor || haveRealRound){
      addFloorAxioms(Theory::REAL_FLOOR,Theory::REAL_LESS,Theory::REAL_UNARY_MINUS,Theory::REAL_PLUS,one,units);
    }
    if(haveRealCeiling || haveRealRound){
      addCeilingAxioms(Theory::REAL_CEILING,Theory::REAL_LESS,Theory::REAL_PLUS,one,units);
    }
    if(haveRealRound){
      //addRoundAxioms(Theory::INT_TRUNCATE,Theory::INT_FLOOR,Theory::INT_CEILING,units);
    }
    if(haveRealTruncate){
      addTruncateAxioms(Theory::REAL_TRUNCATE,Theory::REAL_LESS,Theory::REAL_UNARY_MINUS,
                        Theory::REAL_PLUS,zero,one,units);
    }

    modified = true;
  }

  VirtualIterator<unsigned> arraySorts = env.sorts->getStructuredSorts(Sorts::StructuredSort::ARRAY);
  while(arraySorts.hasNext()){
    unsigned arraySort = arraySorts.next();

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

  VirtualIterator<TermAlgebra*> tas = env.signature->termAlgebrasIterator();
  while (tas.hasNext()) {
    TermAlgebra* ta = tas.next();

    TermAlgebras::addExhaustivenessAxiom(ta, units);
//    TermAlgebras::addAlternativeExhaustivenessAxiom(ta, units);
    TermAlgebras::addDistinctnessAxiom(ta, units);
    TermAlgebras::addInjectivityAxiom(ta, units);
//    TermAlgebras::addAlternativeInjectivityAxiom(ta, units);
    TermAlgebras::addDiscriminationAxiom(ta, units);

    if (env.options->termAlgebraCyclicityCheck() == Options::TACyclicityCheck::AXIOM) {
      TermAlgebras::addAcyclicityAxiom(ta, units);
    }

    modified = true;
  }

  return modified;
} // TheoryAxioms::apply

void TheoryAxioms::applyFOOL(Problem& prb) {
  CALL("TheoryAxioms::applyFOOL");

  TermList t(Term::foolTrue());
  TermList f(Term::foolFalse());

  Inference* foolAxiom = new Inference(Inference::FOOL_AXIOM);

  // Add "$$true != $$false"
  Clause* tneqfClause = new(1) Clause(1, Unit::AXIOM, foolAxiom);
  (*tneqfClause)[0] = Literal::createEquality(false, t, f, Sorts::SRT_BOOL);
  addAndOutputTheoryUnit(tneqfClause, prb.units());

  // Do not add the finite domain axiom if --fool_paradomulation on
  if (env.options->FOOLParamodulation()) {
    return;
  }

  // Add "![X : $bool]: ((X = $$true) | (X = $$false))"
  Clause* boolVarClause = new(2) Clause(2, Unit::AXIOM, foolAxiom);
  (*boolVarClause)[0] = Literal::createEquality(true, TermList(0, false), t, Sorts::SRT_BOOL);
  (*boolVarClause)[1] = Literal::createEquality(true, TermList(0, false), f, Sorts::SRT_BOOL);
  addAndOutputTheoryUnit(boolVarClause, prb.units());
} // TheoryAxioms::addBooleanDomainAxiom

void TheoryAxioms::TermAlgebras::addExhaustivenessAxiom(TermAlgebra* ta, UnitList*& units) {
  CALL("TheoryAxioms::TermAlgebras::addExhaustivenessAxiom");

  TermList x(0, false);
  Stack<TermList> argTerms;

  FormulaList* l = FormulaList::empty();

  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor *c = ta->constructor(i);
    argTerms.reset();

    for (unsigned j = 0; j < c->arity(); j++) {
      if (c->argSort(j) == Sorts::SRT_BOOL) {
        Literal* lit = Literal::create1(c->destructorFunctor(j), true, x);
        Term* t = Term::createFormula(new AtomicFormula(lit));
        argTerms.push(TermList(t));
      } else {
        Term* t = Term::create1(c->destructorFunctor(j), x);
        argTerms.push(TermList(t));
      }
    }

    TermList rhs(Term::create(c->functor(), (unsigned)argTerms.size(), argTerms.begin()));
    FormulaList::push(new AtomicFormula(Literal::createEquality(true, x, rhs, ta->sort())), l);
  }

  Formula::VarList* vars = Formula::VarList::empty()->cons(x.var());
  Formula::SortList* sorts = Formula::SortList::empty()->cons(ta->sort());

  Formula *axiom;
  switch (l->length()) {
    case 0:
      // the algebra cannot have 0 constructors
      ASSERTION_VIOLATION;
    case 1:
      axiom = new QuantifiedFormula(Connective::FORALL, vars, sorts, l->head());
      break;
    default:
      axiom = new QuantifiedFormula(Connective::FORALL, vars, sorts, new JunctionFormula(Connective::OR, l));
  }

  Unit* unit = new FormulaUnit(axiom, new Inference(Inference::TERM_ALGEBRA_EXHAUSTIVENESS), Unit::AXIOM);
  addAndOutputTheoryUnit(unit, units);
}

void TheoryAxioms::TermAlgebras::addAlternativeExhaustivenessAxiom(TermAlgebra* ta, UnitList*& units) {
  CALL("TheoryAxioms::TermAlgebras::addAlternativeExhaustivenessAxiom");

  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor* c = ta->constructor(i);

    Stack<TermList> variables;
    for (unsigned var = 0; var < c->arity(); var++) {
      variables.push(TermList(var, false));
    }

    TermList constructedTerm(Term::create(c->functor(), c->arity(), variables.begin()));

    for (unsigned j = 0; j < c->arity(); j++) {
      Term* rhs = Term::create1(c->destructorFunctor(j), constructedTerm);
      Literal* eq = Literal::createEquality(true, TermList(j, false), TermList(rhs), c->argSort(j));
      addTheoryUnitClause(eq, new Inference(Inference::TERM_ALGEBRA_EXHAUSTIVENESS), units);
    }
  }
}

void TheoryAxioms::TermAlgebras::addDistinctnessAxiom(TermAlgebra* ta, UnitList*& units) {
  CALL("TermAlgebra::addDistinctnessAxiom");

  Array<TermList> terms(ta->nConstructors());

  unsigned var = 0;
  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor* c = ta->constructor(i);

    Stack<TermList> args;
    for (unsigned j = 0; j < c->arity(); j++) {
      args.push(TermList(var++, false));
    }
    TermList term(Term::create(c->functor(), (unsigned)args.size(), args.begin()));
    terms[i] = term;
  }

  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    for (unsigned j = i + 1; j < ta->nConstructors(); j++) {
      Literal* ineq = Literal::createEquality(false, terms[i], terms[j], ta->sort());
      addTheoryUnitClause(ineq, new Inference(Inference::TERM_ALGEBRA_DISTINCTNESS), units);
    }
  }
}

void TheoryAxioms::TermAlgebras::addInjectivityAxiom(TermAlgebra* ta, UnitList*& units)
{
  CALL("TheoryAxioms::TermAlgebras::addInjectivityAxiom");

  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor* c = ta->constructor(i);

    Stack<TermList> lhsArgs(c->arity());
    Stack<TermList> rhsArgs(c->arity());

    for (unsigned j = 0; j < c->arity(); j++) {
      lhsArgs.push(TermList(j * 2, false));
      rhsArgs.push(TermList(j * 2 + 1, false));
    }

    TermList lhs(Term::create(c->functor(), (unsigned)lhsArgs.size(), lhsArgs.begin()));
    TermList rhs(Term::create(c->functor(), (unsigned)rhsArgs.size(), rhsArgs.begin()));
    Literal* eql = Literal::createEquality(false, lhs, rhs, ta->sort());

    for (unsigned j = 0; j < c->arity(); j++) {
      Literal* eqr = Literal::createEquality(true, TermList(j * 2, false), TermList(j * 2 + 1, false), c->argSort(j));

      Clause* injectivity = new(2) Clause(2, Unit::AXIOM, new Inference(Inference::TERM_ALGEBRA_INJECTIVITY));
      (*injectivity)[0] = eql;
      (*injectivity)[1] = eqr;
      addAndOutputTheoryUnit(injectivity, units);
    }
  }
}

void TheoryAxioms::TermAlgebras::addAlternativeInjectivityAxiom(TermAlgebra* ta, UnitList*& units)
{
  CALL("TheoryAxioms::TermAlgebras::addAlternativeInjectivityAxiom");

  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor* c = ta->constructor(i);

    static TermList t1(0, false);
    static TermList t2(1, false);

    Clause* clause = new(c->arity() + 1) Clause(c->arity() + 1, Unit::AXIOM, new Inference(Inference::TERM_ALGEBRA_INJECTIVITY));
    for (unsigned j = 0; j < c->arity(); j++) {
      TermList proj1 = TermList(Term::create1(c->destructorFunctor(j), t1));
      TermList proj2 = TermList(Term::create1(c->destructorFunctor(j), t2));
      (*clause)[j] = Literal::createEquality(false, proj1, proj2, c->argSort(j));
    }
    (*clause)[c->arity()] = Literal::createEquality(true, t1, t2, ta->sort());
    addAndOutputTheoryUnit(clause, units);
  }
}

void TheoryAxioms::TermAlgebras::addDiscriminationAxiom(TermAlgebra* ta, UnitList*& units) {
  CALL("TermAlgebras::addDiscriminationAxiom");

  Array<TermList> cases(ta->nConstructors());
  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor* c = ta->constructor(i);

    Stack<TermList> variables;
    for (unsigned var = 0; var < c->arity(); var++) {
      variables.push(TermList(var, false));
    }

    TermList term(Term::create(c->functor(), (unsigned)variables.size(), variables.begin()));
    cases[i] = term;
  }

  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor* constructor = ta->constructor(i);

    if (!constructor->hasDiscriminator()) continue;

    for (unsigned c = 0; c < cases.size(); c++) {
      Literal* lit = Literal::create1(constructor->discriminator(), c == i, cases[c]);
      addTheoryUnitClause(lit, new Inference(Inference::TERM_ALGEBRA_DISCRIMINATION), units);
    }
  }
}

void TheoryAxioms::TermAlgebras::addAcyclicityAxiom(TermAlgebra* ta, UnitList*& units)
{
  CALL("TheoryAxioms::TermAlgebras::addAcyclicityAxiom");

  unsigned pred = ta->getSubtermPredicate();

  if (ta->allowsCyclicTerms()) {
    return;
  }

  bool rec = false;

  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    if (addSubtermDefinitions(pred, ta->constructor(i), units)) {
      rec = true;
    }
  }

  // rec <=> the subterm relation is non-empty
  if (!rec) {
    return;
  }

  static TermList x(0, false);

  Literal* sub = Literal::create2(pred, false, x, x);
  addTheoryUnitClause(sub, new Inference(Inference::TERM_ALGEBRA_ACYCLICITY), units);
}

bool TheoryAxioms::TermAlgebras::addSubtermDefinitions(unsigned subtermPredicate, TermAlgebraConstructor* c, UnitList*& units)
{
  CALL("TheoryAxioms::TermAlgebras::addSubtermDefinitions");

  TermList z(c->arity(), false);

  Stack<TermList> args;
  for (unsigned i = 0; i < c->arity(); i++) {
    args.push(TermList(i, false));
  }
  TermList right(Term::create(c->functor(), (unsigned)args.size(), args.begin()));

  bool added = false;
  for (unsigned i = 0; i < c->arity(); i++) {
    if (c->argSort(i) != c->rangeSort()) continue;

    TermList y(i, false);

    // Direct subterms are subterms: Sub(y, c(x1, ... y ..., xn))
    Literal* sub = Literal::create2(subtermPredicate, true, y, right);
    addTheoryUnitClause(sub, new Inference(Inference::TERM_ALGEBRA_ACYCLICITY), units);

    // Transitivity of the subterm relation: Sub(z, y) -> Sub(z, c(x1, ... y , xn))
    Clause* transitivity = new(2) Clause(2, Unit::AXIOM, new Inference(Inference::TERM_ALGEBRA_ACYCLICITY));
    (*transitivity)[0] = Literal::create2(subtermPredicate, false, z, y);
    (*transitivity)[1] = Literal::create2(subtermPredicate, true,  z, right);
    addAndOutputTheoryUnit(transitivity, units);

    added = true;
  }
  return added;
}
