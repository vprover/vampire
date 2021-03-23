/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file TheoryAxioms.cpp
 * Implements class TheoryAxioms.
 */

#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"
#include "Lib/DHSet.hpp"

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
#include "Kernel/SortHelper.hpp"

#include "Indexing/TermSharing.hpp"

#include "Property.hpp"
#include "SymCounter.hpp"
#include "TheoryAxioms.hpp"
#include "Options.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;


/**
 * Add the unit @c to @c problem and output it, if the option show_theory_axioms is on.
 * @since 11/11/2013 Manchester
 * @author Andrei Voronkov
 */
void TheoryAxioms::addAndOutputTheoryUnit(Unit* unit, unsigned level)
{
  CALL("TheoryAxioms::addAndOutputTheoryUnit");

  static Options::TheoryAxiomLevel opt_level = env.options->theoryAxioms();
  // if the theory axioms are some or off (want this case for some things like fool) and the axiom is not
  // a cheap one then don't add it
  if(opt_level != Options::TheoryAxiomLevel::ON && level != CHEAP){ return; }

  if (env.options->showTheoryAxioms()) {
    Unit* qunit = unit;
    Formula* f = 0;
    if(unit->isClause()){
      f = Formula::fromClause(static_cast<Clause*>(unit));
      qunit = new FormulaUnit(f,unit->inference());
    }
    cout << "% Theory " << (unit->isClause() ? "clause" : "formula" ) << ": " << qunit->toString() << "\n";
    if(f){ f->destroy(); } 
  }
  if(!unit->isClause()){
    _prb.reportFormulasAdded();
  }
  UnitList::push(unit, _prb.units());
} // addAndOutputTheoryUnit

/**
 * Add the theory clause with literals @c lits to @c problem.
 * @since 11/11/2013, Manchester: output of the clause added
 * @author Andrei Voronkov
 */
void TheoryAxioms::addTheoryClauseFromLits(std::initializer_list<Literal*> lits, InferenceRule rule, unsigned level)
{
  CALL("TheoryAxioms::addTheoryClauseFromLits");
  LiteralStack lit_stack;
  for (Literal* lit : lits) {
    ASS(lit);
    lit_stack.push(lit);
  }
  Clause* cl = Clause::fromStack(lit_stack, TheoryAxiom(rule));
  addAndOutputTheoryUnit(cl, level);
} // addTheoryClauseFromLits

/**
 * Add the axiom f(X,Y)=f(Y,X).
 * @since 11/11/2013, Manchester: modified
 * @author Andrei Voronkov
 */
void TheoryAxioms::addCommutativity(Interpretation op)
{
  CALL("TheoryAxioms::addCommutativity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned f = env.signature->getInterpretingSymbol(op);
  TermList srt = theory->getOperationSort(op);
  TermList x(0,false);
  TermList y(1,false);
  TermList fxy(Term::create2(f,x,y));
  TermList fyx(Term::create2(f,y,x));
  Literal* eq = Literal::createEquality(true,fxy,fyx,srt);
  addTheoryClauseFromLits({eq}, InferenceRule::THA_COMMUTATIVITY, EXPENSIVE);
} // addCommutativity

/**
 * Add axiom f(X,f(Y,Z))=f(f(X,Y),Z).
 * @since 11/11/2013, Manchester: modified
 * @author Andrei Voronkov
 */
void TheoryAxioms::addAssociativity(Interpretation op)
{
  CALL("TheoryAxioms::addCommutativity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned f = env.signature->getInterpretingSymbol(op);
  TermList srt = theory->getOperationSort(op);
  TermList x(0,false);
  TermList y(1,false);
  TermList z(2,false);
  TermList fxy(Term::create2(f,x,y));
  TermList fyz(Term::create2(f,y,z));
  TermList fx_fyz(Term::create2(f,x,fyz));
  TermList f_fxy_z(Term::create2(f,fxy,z));
  Literal* eq = Literal::createEquality(true, fx_fyz,f_fxy_z, srt);
  addTheoryClauseFromLits({eq}, InferenceRule::THA_ASSOCIATIVITY, EXPENSIVE);
} // addAsssociativity


/**
 * Add axiom f(X,e)=X.
 * @since 11/11/2013, Manchester: modified
 * @author Andrei Voronkov
 */
void TheoryAxioms::addRightIdentity(Interpretation op, TermList e)
{
  CALL("TheoryAxioms::addRightIdentity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned f = env.signature->getInterpretingSymbol(op);
  TermList srt = theory->getOperationSort(op);
  TermList x(0,false);
  TermList fxe(Term::create2(f,x,e));
  Literal* eq = Literal::createEquality(true,fxe,x,srt);
  addTheoryClauseFromLits({eq}, InferenceRule::THA_RIGHT_IDENTINTY, EXPENSIVE);
} // addRightIdentity

/**
 * Add axiom f(e,X)=X.
 */
void TheoryAxioms::addLeftIdentity(Interpretation op, TermList e)
{
  CALL("TheoryAxioms::addLeftIdentity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned f = env.signature->getInterpretingSymbol(op);
  TermList srt = theory->getOperationSort(op);
  TermList x(0,false);
  TermList fex(Term::create2(f,e,x));
  Literal* eq = Literal::createEquality(true,fex,x,srt);
  addTheoryClauseFromLits({eq}, InferenceRule::THA_LEFT_IDENTINTY, EXPENSIVE);
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
void TheoryAxioms::addCommutativeGroupAxioms(Interpretation op, Interpretation inverse, TermList e)
{
  CALL("TheoryAxioms::addCommutativeGroupAxioms");

  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);
  ASS(theory->isFunction(inverse));
  ASS_EQ(theory->getArity(inverse),1);

  addCommutativity(op);
  addAssociativity(op);
  addRightIdentity(op,e);

  // i(f(x,y)) = f(i(y),i(x))
  unsigned f = env.signature->getInterpretingSymbol(op);
  unsigned i = env.signature->getInterpretingSymbol(inverse);
  TermList srt = theory->getOperationSort(op);
  ASS_EQ(srt, theory->getOperationSort(inverse));

  TermList x(0,false);
  TermList y(1,false);
  TermList fxy(Term::create2(f,x,y));
  TermList ix(Term::create1(i,x));
  TermList iy(Term::create1(i,y));
  TermList i_fxy(Term::create1(i,fxy));
  TermList f_iy_ix(Term::create2(f,iy,ix));
  Literal* eq1 = Literal::createEquality(true,i_fxy,f_iy_ix,srt);
  addTheoryClauseFromLits({eq1}, InferenceRule::THA_INVERSE_OP_OP_INVERSES, EXPENSIVE);

  // f(x,i(x))=e
  TermList fx_ix(Term::create2(f,x,ix));
  Literal* eq2 = Literal::createEquality(true,fx_ix,e,srt);
  addTheoryClauseFromLits({eq2}, InferenceRule::THA_INVERSE_OP_UNIT, EXPENSIVE);
} // TheoryAxioms::addCommutativeGroupAxioms

/**
 * Add axiom op(op(x,i(y)),y) = x
 * e.g. (x+(-y))+y = x
 */
void TheoryAxioms::addRightInverse(Interpretation op, Interpretation inverse)
{
  TermList x(0,false);
  TermList y(0,false);
  unsigned f = env.signature->getInterpretingSymbol(op);
  unsigned i = env.signature->getInterpretingSymbol(inverse);
  TermList srt = theory->getOperationSort(op);
  ASS_EQ(srt, theory->getOperationSort(inverse));

  TermList iy(Term::create1(i,y));
  TermList xiy(Term::create2(f,x,iy));
  TermList xiyy(Term::create2(f,xiy,y));
  Literal* eq = Literal::createEquality(true,xiyy,x,srt);
  addTheoryClauseFromLits({eq}, InferenceRule::THA_INVERSE_ASSOC, EXPENSIVE);
}

/**
 * Add axiom ~op(X,X)
 */
void TheoryAxioms::addNonReflexivity(Interpretation op)
{
  CALL("TheoryAxioms::addNonReflexivity");

  ASS(!theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned opPred = env.signature->getInterpretingSymbol(op);
  TermList x(0,false);
  Literal* l11 = Literal::create2(opPred, false, x, x);
  addTheoryClauseFromLits({l11}, InferenceRule::THA_NONREFLEX, CHEAP);
} // addNonReflexivity

/**
 * Add axiom ~op(X,Y) | ~op(Y,Z) | op(X,Z)
 */
void TheoryAxioms::addTransitivity(Interpretation op)
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

  addTheoryClauseFromLits({nonL12,nonL23,l13}, InferenceRule::THA_TRANSITIVITY, CHEAP);
}

/**
 * Add axiom less(X,Y) | less(Y,X) | X=Y
 */
void TheoryAxioms::addOrderingTotality(Interpretation less)
{
  CALL("TheoryAxioms::addOrderingTotality");
  ASS(!theory->isFunction(less));
  ASS_EQ(theory->getArity(less),2);

  unsigned opPred = env.signature->getInterpretingSymbol(less);
  TermList x(0,false);
  TermList y(1,false);

  Literal* l12 = Literal::create2(opPred, true, x, y);
  Literal* l21 = Literal::create2(opPred, true, y, x);

  TermList srt = theory->getOperationSort(less);
  Literal* eq = Literal::createEquality(true,x,y,srt);

  addTheoryClauseFromLits({l12,l21,eq}, InferenceRule::THA_ORDER_TOTALALITY, CHEAP);
}

/**
 * Add axioms of reflexivity, transitivity and total ordering for predicate @c less
 */
void TheoryAxioms::addTotalOrderAxioms(Interpretation less)
{
  CALL("TheoryAxioms::addTotalOrderAxioms");

  addNonReflexivity(less);
  addTransitivity(less);
  addOrderingTotality(less);
}

/**
 * Add axiom ~less(X,Y) | less(X+Z,Y+Z)
 */
void TheoryAxioms::addMonotonicity(Interpretation less, Interpretation addition)
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

  addTheoryClauseFromLits({nonLe,leAdded}, InferenceRule::THA_ORDER_MONOTONICITY, EXPENSIVE);
}

/**
 * Add the axiom $less(X,$sum(X,1))
 *
 * Taken from SPASS+T work
 */
void TheoryAxioms::addPlusOneGreater(Interpretation plus, TermList oneElement,
                                     Interpretation less)
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
  addTheoryClauseFromLits({xPo_g_x}, InferenceRule::THA_PLUS_ONE_GREATER, CHEAP);
}

/**
 * Add axioms for addition, unary minus and ordering
 */
void TheoryAxioms::addAdditionAndOrderingAxioms(Interpretation plus, Interpretation unaryMinus,
    TermList zeroElement, TermList oneElement, Interpretation less)
{
  CALL("TheoryAxioms::addAdditionAndOrderingAxioms");

  addCommutativeGroupAxioms(plus, unaryMinus, zeroElement);
  addTotalOrderAxioms(less);
  addMonotonicity(less, plus);

  // y < x+one | x<y
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  TermList x(0,false);
  TermList y(1,false);
  Literal* xLy = Literal::create2(lessPred,true,x,y);
  TermList xP(Term::create2(plusFun,x,oneElement));
  Literal* yLxP = Literal::create2(lessPred,true,y,xP);

  addTheoryClauseFromLits({xLy,yLxP}, InferenceRule::THA_ORDER_PLUS_ONE_DICHOTOMY, EXPENSIVE);

  // add that --x = x
  TermList varSort = theory->getOperationSort(unaryMinus);
  unsigned unaryMinusFun = env.signature->getInterpretingSymbol(unaryMinus);
  TermList mx(Term::create1(unaryMinusFun,x));
  TermList mmx(Term::create1(unaryMinusFun,mx));
  Literal* mmxEqx = Literal::createEquality(true,mmx,x,varSort);
  addTheoryClauseFromLits({mmxEqx}, InferenceRule::THA_MINUS_MINUS_X, EXPENSIVE);
}

/**
 * Add axioms for addition, multiplication, unary minus and ordering
 */
void TheoryAxioms::addAdditionOrderingAndMultiplicationAxioms(Interpretation plus, Interpretation unaryMinus,
    TermList zeroElement, TermList oneElement, Interpretation less, Interpretation multiply)
{
  CALL("TheoryAxioms::addAdditionOrderingAndMultiplicationAxioms");

  TermList srt = theory->getOperationSort(plus);
  ASS_EQ(srt, theory->getOperationSort(unaryMinus));
  ASS_EQ(srt, theory->getOperationSort(less));
  ASS_EQ(srt, theory->getOperationSort(multiply));

  addAdditionAndOrderingAxioms(plus, unaryMinus, zeroElement, oneElement, less);

  addCommutativity(multiply);
  addAssociativity(multiply);
  addRightIdentity(multiply, oneElement);

  //axiom( X0*zero==zero );
  unsigned mulFun = env.signature->getInterpretingSymbol(multiply);
  TermList x(0,false);
  TermList xMulZero(Term::create2(mulFun, x, zeroElement));
  Literal* xEqXMulZero = Literal::createEquality(true, xMulZero, zeroElement, srt);
  addTheoryClauseFromLits({xEqXMulZero}, InferenceRule::THA_TIMES_ZERO, EXPENSIVE);

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
  addTheoryClauseFromLits({distrib}, InferenceRule::THA_DISTRIBUTIVITY, EXPENSIVE);

  // Divisibility
  // (x != 0 & x times z = y & x times w = y) -> z = w
  // x=0 | x*z != y | x*w != y | z=w
  TermList w(3,false);
  Literal* xEz = Literal::createEquality(true,x,zeroElement,srt);
  TermList xTw(Term::create2(mulFun,x,w));
  Literal* xTznEy = Literal::createEquality(false,xTz,y,srt); 
  Literal* xTwnEy = Literal::createEquality(false,xTw,y,srt); 
  Literal* zEw = Literal::createEquality(true,z,w,srt);

  addTheoryClauseFromLits({xEz,xTznEy,xTwnEy,zEw}, InferenceRule::THA_DIVISIBILITY, EXPENSIVE);
}

/**
 * Add axioms for integer division
 * Also modulo and abs functions
 */
void TheoryAxioms::addIntegerDivisionWithModuloAxioms(Interpretation plus, Interpretation unaryMinus, Interpretation less,
                                Interpretation multiply, Interpretation divide, Interpretation divides,
                                Interpretation modulo, Interpretation abs, TermList zeroElement,
                                TermList oneElement)
{
  CALL("TheoryAxioms::addIntegerDivisionWithModuloAxioms");


  TermList srt = theory->getOperationSort(plus);
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

  addIntegerAbsAxioms(abs,less,unaryMinus,zeroElement);

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
  addTheoryClauseFromLits({yis0,xeqsum}, InferenceRule::THA_MODULO_MULTIPLY, EXPENSIVE);

  // y!=0 => (0 <= mod(x,y))
  // y=0 | ~(mod(x,y) < 0)
  Literal* modxyge0 = Literal::create2(lessPred,false,modxy,zeroElement);
  addTheoryClauseFromLits({yis0,modxyge0}, InferenceRule::THA_MODULO_POSITIVE, EXPENSIVE);

  // y!=0 => (mod(x,y) <= abs(y)-1)
  // y=0 | ~( abs(y)-1 < mod(x,y) )
  TermList absy(Term::create1(absFun,y));
  TermList m1(Term::create1(umFun,oneElement));
  TermList absym1(Term::create2(plusFun,absy,m1));
  Literal* modxyleabsym1 = Literal::create2(lessPred,false,absym1,modxy);
  addTheoryClauseFromLits({yis0,modxyleabsym1}, InferenceRule::THA_MODULO_SMALL, EXPENSIVE);
}

void TheoryAxioms::addIntegerDividesAxioms(Interpretation divides, Interpretation multiply, TermList zero, TermList n)
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

  TermList srt = theory->getOperationSort(divides);
  ASS_EQ(srt, theory->getOperationSort(multiply));

  unsigned divsPred = env.signature->getInterpretingSymbol(divides);
  unsigned mulFun   = env.signature->getInterpretingSymbol(multiply);

  TermList y(1,false);
  TermList z(2,false);

// divides(n,Y) | multiply(Z,n) != Y 
  Literal* divsXY = Literal::create2(divsPred,true,n,y);
  TermList mZX(Term::create2(mulFun,z,n));
  Literal* mZXneY = Literal::createEquality(false,mZX,y,srt);
  addTheoryClauseFromLits({divsXY,mZXneY}, InferenceRule::THA_DIVIDES_MULTIPLY, EXPENSIVE);

// ~divides(n,Y) | multiply(skolem(n,Y),n)=Y
  Literal* ndivsXY = Literal::create2(divsPred,false,n,y);
  
  // create a skolem function with signature srt*srt>srt
  unsigned skolem = env.signature->addSkolemFunction(2);
  Signature::Symbol* sym = env.signature->getFunction(skolem);
  sym->setType(OperatorType::getFunctionType({srt,srt},srt));
  TermList skXY(Term::create2(skolem,n,y));
  TermList msxX(Term::create2(mulFun,skXY,n));
  Literal* msxXeqY = Literal::createEquality(true,msxX,y,srt);

  addTheoryClauseFromLits({ndivsXY,msxXeqY}, InferenceRule::THA_NONDIVIDES_SKOLEM, EXPENSIVE);
}

void TheoryAxioms::addIntegerAbsAxioms(Interpretation abs, Interpretation less, 
                                       Interpretation unaryMinus, TermList zeroElement)
{
  CALL("TheoryAxioms::addIntegerAbsAxioms");

  TermList srt = theory->getOperationSort(abs);
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

  addTheoryClauseFromLits({xNeg,absXeqX}, InferenceRule::THA_ABS_EQUALS, EXPENSIVE);
  addTheoryClauseFromLits({xPos,absXeqmX}, InferenceRule::THA_ABS_MINUS_EQUALS, EXPENSIVE);
}


/**
 * Add axioms for quotient i.e. rat or real division 
 */
void TheoryAxioms::addQuotientAxioms(Interpretation quotient, Interpretation multiply,
    TermList zeroElement, TermList oneElement, Interpretation less)
{
  CALL("TheoryAxioms::addQuotientAxioms");

  TermList srt = theory->getOperationSort(quotient);
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
  //addTheoryNonUnitClause(guardx,xQxis1);

  // x=0 | quotient(1,x)!=0
  TermList q1X(Term::create2(divFun,oneElement,x));
  Literal* oQxnot0 = Literal::createEquality(false,q1X,zeroElement,srt);
  addTheoryClauseFromLits({guardx,oQxnot0}, InferenceRule::THA_QUOTIENT_NON_ZERO, EXPENSIVE);

  // quotient(x,1)=x, easily derivable!
  //TermList qX1(Term::create2(quotient,x,oneElement));
  //Literal* qx1isx = Literal::createEquality(true,qX1,x,srt);
  //addTheoryUnitClause(qx1isx);

  // x=0 | quotient(multiply(y,x),x)=y
  TermList myx(Term::create2(mulFun,y,x));
  TermList qmx(Term::create2(divFun,myx,x));
  Literal* qmxisy = Literal::createEquality(true,qmx,y,srt);

  addTheoryClauseFromLits({guardx,qmxisy}, InferenceRule::THA_QUOTIENT_MULTIPLY, EXPENSIVE);
}

/**
 * Add axiom valid only for integer ordering: Y>X ->  Y => X+1 
 *
 * ~(x<y) | ~(y,x+1)
 */
void TheoryAxioms::addExtraIntegerOrderingAxiom(Interpretation plus, TermList oneElement,
                                                Interpretation less)
{
  CALL("TheoryAxioms::addExtraIntegerOrderingAxiom");

  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  TermList x(0,false);
  TermList y(1,false);
  Literal* nxLy = Literal::create2(lessPred, false, x, y);
  TermList xPOne(Term::create2(plusFun, x, oneElement));
  Literal* nyLxPOne = Literal::create2(lessPred, false, y,xPOne);

  addTheoryClauseFromLits({nxLy,nyLxPOne}, InferenceRule::THA_EXTRA_INTEGER_ORDERING, EXPENSIVE);
}
    
/**
 * Add axioms defining floor function
 * @author Giles
 */
void TheoryAxioms::addFloorAxioms(Interpretation floor, Interpretation less, Interpretation unaryMinus,
     Interpretation plus, TermList oneElement)
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
  addTheoryClauseFromLits({a1}, InferenceRule::THA_FLOOR_SMALL, EXPENSIVE);

  //axiom( X-1 < floor(X) ) 
  TermList m1(Term::create1(umFun,oneElement));
  TermList xm1(Term::create2(plusFun, x, m1));
  Literal* a2 = Literal::create2(lessPred,true, xm1, floorX);

  addTheoryClauseFromLits({a2}, InferenceRule::THA_FLOOR_BIG, EXPENSIVE);
} //addFloorAxioms

/**
 * Add axioms defining ceiling function
 * @author Giles
 */ 
void TheoryAxioms::addCeilingAxioms(Interpretation ceiling, Interpretation less, 
     Interpretation plus, TermList oneElement)
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
  addTheoryClauseFromLits({a1}, InferenceRule::THA_CEILING_BIG, EXPENSIVE);

  //axiom( ceiling(X) < X+1 ) 
  TermList xp1(Term::create2(plusFun, x, oneElement));
  Literal* a2 = Literal::create2(lessPred,true, ceilingX, xp1);
  addTheoryClauseFromLits({a2}, InferenceRule::THA_CEILING_SMALL, EXPENSIVE);
} //addCeilingAxioms

/**
 * Add axioms defining round function
 * @author Giles
 */ 
void TheoryAxioms::addRoundAxioms(Interpretation round, Interpretation floor, Interpretation ceiling)
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
                      Interpretation plus, TermList zeroElement, TermList oneElement)
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
  addTheoryClauseFromLits({xLz,a1}, InferenceRule::THA_TRUNC1, EXPENSIVE);

  //x<0 | x-1 < tr(x)
  Literal* a2 = Literal::create2(lessPred,true,xm1,truncateX);
  addTheoryClauseFromLits({xLz,a2}, InferenceRule::THA_TRUNC2, EXPENSIVE);

  // ~(x<0) | ~( tr(x) < x )
  Literal* a3 = Literal::create2(lessPred,false,truncateX,x);
  addTheoryClauseFromLits({nxLz,a3}, InferenceRule::THA_TRUNC3, EXPENSIVE);

  // ~(x<0) | tr(x) < x+1
  Literal* a4 = Literal::create2(lessPred,true,truncateX,xp1);
  addTheoryClauseFromLits({nxLz,a4}, InferenceRule::THA_TRUNC4, EXPENSIVE);
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
void TheoryAxioms::addArrayExtensionalityAxioms(TermList arraySort, unsigned skolemFn)
{
  CALL("TheoryAxioms::addArrayExtenstionalityAxioms");

  unsigned sel = env.signature->getInterpretingSymbol(Theory::ARRAY_SELECT,Theory::getArrayOperatorType(arraySort,Theory::ARRAY_SELECT));

  TermList rangeSort = SortHelper::getInnerSort(arraySort);

  TermList x(0,false);
  TermList y(1,false);
  
  TermList sk(Term::create2(skolemFn, x, y)); //sk(x,y)
  TermList sel_x_sk(Term::create2(sel,x,sk)); //select(x,sk(x,y))
  TermList sel_y_sk(Term::create2(sel,y,sk)); //select(y,sk(x,y))
  Literal* eq = Literal::createEquality(true,x,y,arraySort); //x = y
  Literal* ineq = Literal::createEquality(false,sel_x_sk,sel_y_sk,rangeSort); //select(x,sk(x,y) != select(y,z)

  addTheoryClauseFromLits({eq,ineq}, InferenceRule::THA_ARRAY_EXTENSIONALITY, CHEAP);
} // addArrayExtensionalityAxiom    

/**
 * Adds the extensionality axiom of boolean arrays:
 * select(X, sk(X, Y)) <~> select(Y, sk(X, Y)) | X = Y
 *
 * @since 25/08/2015 Gothenburg
 * @author Evgeny Kotelnikov
 */
void TheoryAxioms::addBooleanArrayExtensionalityAxioms(TermList arraySort, unsigned skolemFn)
{
  CALL("TheoryAxioms::addBooleanArrayExtenstionalityAxioms");

  OperatorType* selectType = Theory::getArrayOperatorType(arraySort,Theory::ARRAY_BOOL_SELECT);

  unsigned sel = env.signature->getInterpretingSymbol(Theory::ARRAY_BOOL_SELECT,selectType);

  TermList x(0,false);
  TermList y(1,false);

  TermList sk(Term::create2(skolemFn, x, y)); //sk(x,y)
  Formula* x_neq_y = new AtomicFormula(Literal::createEquality(false,x,y,arraySort)); //x != y

  Formula* sel_x_sk = new AtomicFormula(Literal::create2(sel, true, x, sk)); //select(x,sk(x,y))
  Formula* sel_y_sk = new AtomicFormula(Literal::create2(sel, true, y, sk)); //select(y,sk(x,y))
  Formula* sx_neq_sy = new BinaryFormula(XOR, sel_x_sk, sel_y_sk); //select(x,sk(x,y)) <~> select(y,sk(x,y))

  Formula* axiom = new QuantifiedFormula(FORALL, VList::cons(0, VList::cons(1, VList::empty())),
                                         SList::cons(arraySort, SList::cons(arraySort,SList::empty())),
                                         new BinaryFormula(IMP, x_neq_y, sx_neq_sy));

  addAndOutputTheoryUnit(new FormulaUnit(axiom, TheoryAxiom(InferenceRule::THA_BOOLEAN_ARRAY_EXTENSIONALITY)),CHEAP);
} // addBooleanArrayExtensionalityAxiom

/**
* Adds the write/select axiom of arrays (of type array1 or array2), 
 * @author Laura Kovacs
 * @since 31/08/2012, Vienna
*/
void TheoryAxioms::addArrayWriteAxioms(TermList arraySort)
{
  CALL("TheoryAxioms::addArrayWriteAxioms");
        
  unsigned func_select = env.signature->getInterpretingSymbol(Theory::ARRAY_SELECT,Theory::getArrayOperatorType(arraySort,Theory::ARRAY_SELECT));
  unsigned func_store = env.signature->getInterpretingSymbol(Theory::ARRAY_STORE,Theory::getArrayOperatorType(arraySort,Theory::ARRAY_STORE));

  TermList rangeSort = SortHelper::getInnerSort(arraySort);
  TermList domainSort = SortHelper::getIndexSort(arraySort);

  TermList i(0,false);
  TermList j(1,false);
  TermList v(2,false);
  TermList a(3,false);
  TermList args[] = {a, i, v};
        
  //axiom (!A: arraySort, !I:domainSort, !V:rangeSort: (select(store(A,I,V), I) = V
  TermList wAIV(Term::create(func_store, 3, args)); //store(A,I,V)
  TermList sWI(Term::create2(func_select, wAIV,i)); //select(wAIV,I)
  Literal* ax = Literal::createEquality(true, sWI, v, rangeSort);
  addTheoryClauseFromLits({ax}, InferenceRule::THA_ARRAY_WRITE1, CHEAP);

  //axiom (!A: arraySort, !I,J:domainSort, !V:rangeSort: (I!=J)->(select(store(A,I,V), J) = select(A,J)
  TermList sWJ(Term::create2(func_select, wAIV,j)); //select(wAIV,J)
  TermList sAJ(Term::create2(func_select, a, j)); //select(A,J)
        
  Literal* indexEq = Literal::createEquality(true, i, j, domainSort);//!(!(I=J)) === I=J
  Literal* writeEq = Literal::createEquality(true, sWJ, sAJ, rangeSort);//(select(store(A,I,V), J) = select(A,J)
  addTheoryClauseFromLits({indexEq,writeEq}, InferenceRule::THA_ARRAY_WRITE2, CHEAP);
} //

/**
* Adds the write/select axiom of arrays (of type array1 or array2),
 * @author Laura Kovacs
 * @since 31/08/2012, Vienna
*/
void TheoryAxioms::addBooleanArrayWriteAxioms(TermList arraySort)
{
  CALL("TheoryAxioms::addArrayWriteAxioms");

  unsigned pred_select = env.signature->getInterpretingSymbol(Theory::ARRAY_BOOL_SELECT,Theory::getArrayOperatorType(arraySort,Theory::ARRAY_BOOL_SELECT));
  unsigned func_store = env.signature->getInterpretingSymbol(Theory::ARRAY_STORE,Theory::getArrayOperatorType(arraySort,Theory::ARRAY_STORE));

  TermList domainSort = SortHelper::getIndexSort(arraySort);

  TermList a(0,false);
  TermList i(1,false);

  TermList false_(Term::foolFalse());
  TermList true_(Term::foolTrue());

  // select(store(A,I,$$true), I)
  //~select(store(A,I,$$false), I)

  for (TermList bval : {false_,true_}) {
    TermList args[] = {a, i, bval};
    TermList wAIV(Term::create(func_store, 3, args)); //store(A,I,bval)
    Literal* lit = Literal::create2(pred_select, true, wAIV,i);
    if (bval == false_) {
      lit = Literal::complementaryLiteral(lit);
    }
    Formula* ax = new AtomicFormula(lit);
    addAndOutputTheoryUnit(new FormulaUnit(ax, TheoryAxiom(InferenceRule::THA_BOOLEAN_ARRAY_WRITE1)),CHEAP);
  }

  TermList v(2,false);
  TermList j(3,false);

  TermList args[] = {a, i, v};

  //axiom (!A: arraySort, !I,J:domainSort, !V:rangeSort: (I!=J)->(select(store(A,I,V), J) <=> select(A,J)
  TermList wAIV(Term::create(func_store, 3, args)); //store(A,I,V)
  Formula* sWJ = new AtomicFormula(Literal::create2(pred_select, true, wAIV,j)); //select(wAIV,J)
  Formula* sAJ = new AtomicFormula(Literal::create2(pred_select, true, a, j)); //select(A,J)

  Formula* indexEq = new AtomicFormula(Literal::createEquality(false, i, j, domainSort));//I!=J
  Formula* writeEq = new BinaryFormula(IFF, sWJ, sAJ);//(select(store(A,I,V), J) <=> select(A,J)
  Formula* ax2 = new BinaryFormula(IMP, indexEq, writeEq);
  addAndOutputTheoryUnit(new FormulaUnit(ax2, TheoryAxiom(InferenceRule::THA_BOOLEAN_ARRAY_WRITE2)),CHEAP);
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
 * Add theory axioms to the @b problem that are relevant to
 * units present in the problem. The problem must have been processed
 * by the InterpretedNormalizer before using this rule
 *
 * @since 11/11/2013, Manchester: bug fixes
 * @author Andrei Voronkov
 */
void TheoryAxioms::apply()
{
  CALL("TheoryAxioms::applyProperty");
  Property* prop = _prb.getProperty();
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
						 Theory::INT_LESS, Theory::INT_MULTIPLY);
      if(haveIntDivision){
        addIntegerDivisionWithModuloAxioms(Theory::INT_PLUS, Theory::INT_UNARY_MINUS, Theory::INT_LESS,
                                 Theory::INT_MULTIPLY, Theory::INT_QUOTIENT_E, Theory::INT_DIVIDES,
                                 Theory::INT_REMAINDER_E, Theory::INT_ABS, zero,one);
      }
      else if(haveIntDivides){ 
        Stack<TermList>& ns = env.signature->getDividesNvalues(); 
        Stack<TermList>::Iterator nsit(ns);
        while(nsit.hasNext()){
          TermList n = nsit.next();
          addIntegerDividesAxioms(Theory::INT_DIVIDES,Theory::INT_MULTIPLY,zero,n); 
        }
      }
    }
    else {
      addAdditionAndOrderingAxioms(Theory::INT_PLUS, Theory::INT_UNARY_MINUS, zero, one,
				   Theory::INT_LESS);
    }
    addExtraIntegerOrderingAxiom(Theory::INT_PLUS, one, Theory::INT_LESS);
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
						 Theory::RAT_LESS, Theory::RAT_MULTIPLY);

      if(haveRatQuotient){
        addQuotientAxioms(Theory::RAT_QUOTIENT,Theory::RAT_MULTIPLY,zero,one,Theory::RAT_LESS);
      }
    }
    else {
      addAdditionAndOrderingAxioms(Theory::RAT_PLUS, Theory::RAT_UNARY_MINUS, zero, one,
				   Theory::RAT_LESS);
    }
    if(haveRatFloor || haveRatRound){
      addFloorAxioms(Theory::RAT_FLOOR,Theory::RAT_LESS,Theory::RAT_UNARY_MINUS,Theory::RAT_PLUS,one);
    }
    if(haveRatCeiling || haveRatRound){
      addCeilingAxioms(Theory::RAT_CEILING,Theory::RAT_LESS,Theory::RAT_PLUS,one);
    }
    if(haveRatRound){
      //addRoundAxioms(Theory::INT_TRUNCATE,Theory::INT_FLOOR,Theory::INT_CEILING);
    }
    if(haveRatTruncate){
      addTruncateAxioms(Theory::RAT_TRUNCATE,Theory::RAT_LESS,Theory::RAT_UNARY_MINUS,
                        Theory::RAT_PLUS,zero,one);
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
						 Theory::REAL_LESS, Theory::REAL_MULTIPLY);

      if(haveRealQuotient){
        addQuotientAxioms(Theory::REAL_QUOTIENT,Theory::REAL_MULTIPLY,zero,one,Theory::REAL_LESS);
      }
    }
    else {
      addAdditionAndOrderingAxioms(Theory::REAL_PLUS, Theory::REAL_UNARY_MINUS, zero, one,
				   Theory::REAL_LESS);
    }
    if(haveRealFloor || haveRealRound){
      addFloorAxioms(Theory::REAL_FLOOR,Theory::REAL_LESS,Theory::REAL_UNARY_MINUS,Theory::REAL_PLUS,one);
    }
    if(haveRealCeiling || haveRealRound){
      addCeilingAxioms(Theory::REAL_CEILING,Theory::REAL_LESS,Theory::REAL_PLUS,one);
    }
    if(haveRealRound){
      //addRoundAxioms(Theory::INT_TRUNCATE,Theory::INT_FLOOR,Theory::INT_CEILING);
    }
    if(haveRealTruncate){
      addTruncateAxioms(Theory::REAL_TRUNCATE,Theory::REAL_LESS,Theory::REAL_UNARY_MINUS,
                        Theory::REAL_PLUS,zero,one);
    }

    modified = true;
  }

  DHSet<TermList>* arraySorts = env.sharing->getArraySorts();
  DHSet<TermList>::Iterator it(*arraySorts);
  while(it.hasNext()){
    TermList arraySort = it.next();

    bool isBool = SortHelper::getInnerSort(arraySort) == AtomicSort::boolSort();
    
    // Check if they are used
    Interpretation arraySelect = isBool ? Theory::ARRAY_BOOL_SELECT : Theory::ARRAY_SELECT;
    bool haveSelect = prop->hasInterpretedOperation(arraySelect,Theory::getArrayOperatorType(arraySort,arraySelect));
    bool haveStore = prop->hasInterpretedOperation(Theory::ARRAY_STORE,Theory::getArrayOperatorType(arraySort,Theory::ARRAY_STORE));

    if (haveSelect || haveStore) {
      unsigned sk = theory->getArrayExtSkolemFunction(arraySort);
      if (isBool) {
        addBooleanArrayExtensionalityAxioms(arraySort, sk);
      } else {
        addArrayExtensionalityAxioms(arraySort, sk);
      }
      if (haveStore) {
        if (isBool) {
          addBooleanArrayWriteAxioms(arraySort);
        } else {
          addArrayWriteAxioms(arraySort);
        }
      }
      modified = true;
    }
  }

  VirtualIterator<TermAlgebra*> tas = env.signature->termAlgebrasIterator();
  while (tas.hasNext()) {
    TermAlgebra* ta = tas.next();

    addExhaustivenessAxiom(ta);
    addDistinctnessAxiom(ta);
    addInjectivityAxiom(ta);
    addDiscriminationAxiom(ta);

    if (env.options->termAlgebraCyclicityCheck() == Options::TACyclicityCheck::AXIOM) {
      addAcyclicityAxiom(ta);
    }

    modified = true;
  }

  if(modified) {
    _prb.reportEqualityAdded(false);
  }
} // TheoryAxioms::apply

void TheoryAxioms::applyFOOL() {
  CALL("TheoryAxioms::applyFOOL");

  TermList t(Term::foolTrue());
  TermList f(Term::foolFalse());

  // Add "$$true != $$false"
  Literal* tneqf = Literal::createEquality(false, t, f, AtomicSort::boolSort());

  addTheoryClauseFromLits({tneqf},InferenceRule::FOOL_AXIOM_TRUE_NEQ_FALSE,CHEAP);

  // Do not add the finite domain axiom if --fool_paradomulation on
  if (env.options->FOOLParamodulation() || env.options->cases() ||
      env.options->casesSimp()) {
    return;
  }

  // Add "![X : $bool]: ((X = $$true) | (X = $$false))"
  Literal* boolVar1 = Literal::createEquality(true, TermList(0, false), t, AtomicSort::boolSort());
  Literal* boolVar2 = Literal::createEquality(true, TermList(0, false), f, AtomicSort::boolSort());

  addTheoryClauseFromLits({boolVar1,boolVar2},InferenceRule::FOOL_AXIOM_ALL_IS_TRUE_OR_FALSE,CHEAP);
} // TheoryAxioms::addBooleanDomainAxiom

/*
 * Note: In contrast to all other internally added theory axioms, the exhaustiveness axiom is
 * added in some cases as Formula and not as a clause. We would like to enforce the invariant that all internally
 * added theory axioms are added as clauses, in order to allow for an easy check whether a clause is
 * a theory axiom or not (without going up the preprocessing derivation until we derive at the axiom formula).
 * We currently already use this easy check, and miss the exhaustiveness axiom in some cases.
 *
 * Adding the exhaustiveness axiom as clause is difficult in the case where some destructor 
 * has boolean sort: The currently implemented clausification-algorithms (default and newcnf) differ
 * in how they clausify the axiom formula, and newcnf as far as I know generates different clausifications
 * of the exhaustiveness axiom formula depending on the value of some magic constants.
 */
void TheoryAxioms::addExhaustivenessAxiom(TermAlgebra* ta) {
  CALL("TheoryAxioms::addExhaustivenessAxiom");

  TermList x(0, false);

  // Part 1: compute list of literals and set flag if a FOOL-destructor occurs
  Stack<Literal*> lits;
  bool addsFOOL = false;

  Stack<TermList> argTerms;
  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor *c = ta->constructor(i);
    argTerms.reset();

    for (unsigned j = 0; j < c->arity(); j++) {
      if (c->argSort(j) == AtomicSort::boolSort()) {
        addsFOOL = true;
        Literal* lit = Literal::create1(c->destructorFunctor(j), true, x);
        Term* t = Term::createFormula(new AtomicFormula(lit));
        argTerms.push(TermList(t));
      } else {
        Term* t = Term::create1(c->destructorFunctor(j), x);
        argTerms.push(TermList(t));
      }
    }

    TermList rhs(Term::create(c->functor(), argTerms.size(), argTerms.begin()));
    lits.push(Literal::createEquality(true, x, rhs, ta->sort()));
  }
  ASS(!lits.isEmpty());

  // Part 2: add axiom
  // - if no FOOL-destructors occur, add the axiom as clause
  // - otherwise, add the axiom as formula (cf. comments at the beginning of this method)
  Unit* axiom;
  if (!addsFOOL) {
    axiom = Clause::fromStack(lits, TheoryAxiom(InferenceRule::TERM_ALGEBRA_EXHAUSTIVENESS_AXIOM));
  } else {
    Formula* disjunction;
    if(lits.size() == 1) {
        disjunction = new AtomicFormula(lits[0]);
    } else {
      FormulaList* fl = FormulaList::empty();
      for (unsigned i = 0; i < lits.size(); i++)
      {
        FormulaList::push(new AtomicFormula(lits[i]), fl);
      }
      disjunction = new JunctionFormula(Connective::OR, fl);
    }
    VList* vars = VList::singleton(x.var());
    SList* sorts = SList::singleton(ta->sort());
    auto universal = new QuantifiedFormula(Connective::FORALL, vars, sorts, disjunction);

    axiom = new FormulaUnit(universal, TheoryAxiom(InferenceRule::TERM_ALGEBRA_EXHAUSTIVENESS_AXIOM));

    _prb.reportFOOLAdded();
  }

  addAndOutputTheoryUnit(axiom, CHEAP);
}

void TheoryAxioms::addDistinctnessAxiom(TermAlgebra* ta) {
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
      addTheoryClauseFromLits({ineq}, InferenceRule::TERM_ALGEBRA_DISTINCTNESS_AXIOM,CHEAP);
    }
  }
}

void TheoryAxioms::addInjectivityAxiom(TermAlgebra* ta)
{
  CALL("TheoryAxioms::addInjectivityAxiom");

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

      addTheoryClauseFromLits({eql,eqr},InferenceRule::TERM_ALGEBRA_INJECTIVITY_AXIOM,CHEAP);
    }
  }
}

void TheoryAxioms::addDiscriminationAxiom(TermAlgebra* ta) {
  CALL("addDiscriminationAxiom");

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
      addTheoryClauseFromLits({lit}, InferenceRule::TERM_ALGEBRA_DISCRIMINATION_AXIOM,CHEAP);
    }
  }
}

void TheoryAxioms::addAcyclicityAxiom(TermAlgebra* ta)
{
  CALL("TheoryAxioms::addAcyclicityAxiom");

  unsigned pred = ta->getSubtermPredicate();

  if (ta->allowsCyclicTerms()) {
    return;
  }

  bool rec = false;

  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    if (addSubtermDefinitions(pred, ta->constructor(i))) {
      rec = true;
    }
  }

  // rec <=> the subterm relation is non-empty
  if (!rec) {
    return;
  }

  static TermList x(0, false);

  Literal* sub = Literal::create2(pred, false, x, x);
  addTheoryClauseFromLits({sub}, InferenceRule::TERM_ALGEBRA_ACYCLICITY_AXIOM,CHEAP);
}

bool TheoryAxioms::addSubtermDefinitions(unsigned subtermPredicate, TermAlgebraConstructor* c)
{
  CALL("TheoryAxioms::addSubtermDefinitions");

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
    addTheoryClauseFromLits({sub}, InferenceRule::TERM_ALGEBRA_DIRECT_SUBTERMS_AXIOM,CHEAP);

    // Transitivity of the subterm relation: Sub(z, y) -> Sub(z, c(x1, ... y , xn))
    Literal* trans1 = Literal::create2(subtermPredicate, false, z, y);
    Literal* trans2 = Literal::create2(subtermPredicate, true,  z, right);
    addTheoryClauseFromLits({trans1,trans2}, InferenceRule::TERM_ALGEBRA_SUBTERMS_TRANSITIVE_AXIOM,CHEAP);

    added = true;
  }
  return added;
}
