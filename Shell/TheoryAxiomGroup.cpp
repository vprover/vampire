/**
 * @file TheoryAxiomGroup.cpp
 * Implements class TheoryAxiomGroup.
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
#include "TheoryAxiomGroup.hpp"
#include "Options.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

/**
 * Copied form TheoryAxioms
 */
void TheoryAxiomGroup::addTheoryUnit(Unit* unit,UnitList*& units)
{
  CALL("TheoryAxiomGroup::addTheoryUnit");
  UnitList::push(unit,units);
} // addTheoryUnit

/**
 * Copied form TheoryAxioms
 */
void TheoryAxiomGroup::addTheoryUnitClause(Literal* lit, UnitList*& units)
{
  CALL("TheoryAxiomGroup::addTheoryUnitClause");
  Clause* unit = Clause::fromIterator(getSingletonIterator(lit), Unit::AXIOM, 
                     new Inference(Inference::THEORY));
  addTheoryUnit(unit,units);
} // addTheoryUnitClause

/**
 * Copied form TheoryAxioms
 */
void TheoryAxiomGroup::addTheoryNonUnitClause(UnitList*& units, Literal* lit1, Literal* lit2, Literal* lit3)
{
  CALL("TheoryAxiomGroup::addTheoryNonUnitClause");
  LiteralStack lits;
  ASS(lit1);
  lits.push(lit1);
  ASS(lit2);
  lits.push(lit2);
  if (lit3) {
    lits.push(lit3);
  }
  Clause* cl = Clause::fromStack(lits, Unit::AXIOM, new Inference(Inference::THEORY));
  addTheoryUnit(cl,units);
} // addTheoryNonUnitCLause


// $sum(X0,0) = X0
void TheoryAxiomGroup::addOne(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units)
{
  CALL("TheoryAxiomGroup::addOne");

  unsigned f = env.signature->getInterpretingSymbol(plus);
  unsigned srt = theory->getOperationSort(plus);
  TermList x(0,false);
  TermList fxe(Term::create2(f,x,zero));
  Literal* eq = Literal::createEquality(true,fxe,x,srt);
  addTheoryUnitClause(eq, units);

}

// $sum(0,X) = X
void TheoryAxiomGroup::addTwo(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units)
{
  CALL("TheoryAxiomGroup::addTwo");

  unsigned f = env.signature->getInterpretingSymbol(plus);
  unsigned srt = theory->getOperationSort(plus);
  TermList x(0,false);
  TermList fex(Term::create2(f,zero,x));
  Literal* eq = Literal::createEquality(true,fex,x,srt);
  addTheoryUnitClause(eq, units);

}

// $sum(X0,X1) = $sum(X1,X0)
void TheoryAxiomGroup::addThree(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units)
{
  CALL("TheoryAxiomGroup::addThree");

  unsigned f = env.signature->getInterpretingSymbol(plus);
  unsigned srt = theory->getOperationSort(plus);
  TermList x(0,false);
  TermList y(1,false);
  TermList fxy(Term::create2(f,x,y));
  TermList fyx(Term::create2(f,y,x));
  Literal* eq = Literal::createEquality(true,fxy,fyx,srt);
  addTheoryUnitClause(eq,units);

}

// $sum(X0,$sum(X1,X2)) = $sum($sum(X0,X1),X2)
void TheoryAxiomGroup::addFour(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units)
{
  CALL("TheoryAxiomGroup::addFour");

  unsigned f = env.signature->getInterpretingSymbol(plus);
  unsigned srt = theory->getOperationSort(plus);
  TermList x(0,false);
  TermList y(1,false);
  TermList z(2,false);
  TermList fxy(Term::create2(f,x,y));
  TermList fyz(Term::create2(f,y,z));
  TermList fx_fyz(Term::create2(f,x,fyz));
  TermList f_fxy_z(Term::create2(f,fxy,z));
  Literal* eq = Literal::createEquality(true, fx_fyz,f_fxy_z, srt);
  addTheoryUnitClause(eq, units);

}

// 0 = $sum(X0,$uminus(X0))
void TheoryAxiomGroup::addFive(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units)
{
  CALL("TheoryAxiomGroup::addFive");

  unsigned f = env.signature->getInterpretingSymbol(plus);
  unsigned i = env.signature->getInterpretingSymbol(uminus);
  unsigned srt = theory->getOperationSort(plus);
  TermList x(0,false);
  TermList ix(Term::create1(i,x));
  TermList fx_ix(Term::create2(f,x,ix));
  Literal* eq2 = Literal::createEquality(true,fx_ix,zero,srt);
  addTheoryUnitClause(eq2, units);

}

// $sum($uminus(X1),$uminus(X0)) = $uminus($sum(X0,X1))
void TheoryAxiomGroup::addSix(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units)
{
  CALL("TheoryAxiomGroup::addSix");

  unsigned f = env.signature->getInterpretingSymbol(plus);
  unsigned i = env.signature->getInterpretingSymbol(uminus);
  unsigned srt = theory->getOperationSort(plus);
  TermList x(0,false);
  TermList y(1,false);
  TermList fxy(Term::create2(f,x,y));
  TermList ix(Term::create1(i,x));
  TermList iy(Term::create1(i,y));
  TermList i_fxy(Term::create1(i,fxy));
  TermList f_iy_ix(Term::create2(f,iy,ix));
  Literal* eq1 = Literal::createEquality(true,i_fxy,f_iy_ix,srt);
  addTheoryUnitClause(eq1, units);


}

// $sum($sum(X,$uminus(Y)),Y) = X
void TheoryAxiomGroup::addSeven(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units)
{
  CALL("TheoryAxiomGroup::addSeven");

  unsigned f = env.signature->getInterpretingSymbol(plus);
  unsigned i = env.signature->getInterpretingSymbol(uminus);
  unsigned srt = theory->getOperationSort(plus);
  TermList x(0,false);
  TermList y(1,false);
  TermList iy(Term::create1(i,y));
  TermList fx_iy(Term::create2(f,x,iy));
  TermList fx_iy_y(Term::create2(f,fx_iy,y));
  Literal* eq2 = Literal::createEquality(true,fx_iy_y,x,srt);
  addTheoryUnitClause(eq2, units);

}

// $lesseq(X0,X0)
void TheoryAxiomGroup::addEight(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units)
{
  CALL("TheoryAxiomGroup::addEight");

  unsigned opPred = env.signature->getInterpretingSymbol(lessEq);
  TermList x(0,false);
  Literal* l11 = Literal::create2(opPred, true, x, x);
  addTheoryUnitClause(l11, units);

}

// $lesseq(X0,X1) | $lesseq(X1,X0)
void TheoryAxiomGroup::addNine(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units)
{
  CALL("TheoryAxiomGroup::addNine");

  unsigned opPred = env.signature->getInterpretingSymbol(lessEq);
  TermList x(0,false);
  TermList y(1,false);

  Literal* l12 = Literal::create2(opPred, true, x, y);
  Literal* l21 = Literal::create2(opPred, true, y, x);

  addTheoryNonUnitClause(units, l12, l21);

}

// ~$lesseq(X1,X0) | ~$lesseq(X0,X1) | X0 = X1
void TheoryAxiomGroup::addTen(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units)
{
  CALL("TheoryAxiomGroup::addTen");

  unsigned lePred = env.signature->getInterpretingSymbol(lessEq);
  unsigned varSort = theory->getOperationSort(lessEq);
  TermList x(0,false);
  TermList y(1,false);
  Literal* nonLe21 = Literal::create2(lePred, false, y, x);
  Literal* nonLe12 = Literal::create2(lePred, false, x, y);
  Literal* xEqY = Literal::createEquality(true, x, y, varSort);
  addTheoryNonUnitClause(units, nonLe21, nonLe12, xEqY);

}

// ~$lesseq(X0,X1) | ~$lesseq(X1,X2) | $lesseq(X0,X2)
void TheoryAxiomGroup::addEleven(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units)
{
  CALL("TheoryAxiomGroup::addEleven");

  unsigned opPred = env.signature->getInterpretingSymbol(lessEq);
  TermList x(0,false);
  TermList y(1,false);
  TermList v3(2,false);

  Literal* nonL12 = Literal::create2(opPred, false, x, y);
  Literal* nonL23 = Literal::create2(opPred, false, y, v3);
  Literal* l13 = Literal::create2(opPred, true, x, v3);

  addTheoryNonUnitClause(units, nonL12, nonL23, l13);

}

// $lesseq(X1,X0) | $lesseq($sum(X0,1),X1)
void TheoryAxiomGroup::addTwelve(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units)
{
  CALL("TheoryAxiomGroup::addTwelve");

  unsigned srt = theory->getOperationSort(plus);
  if(srt != Sorts::SRT_INTEGER) return; // This axiom is for Integers only 

  unsigned lePred = env.signature->getInterpretingSymbol(lessEq);
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  TermList x(0,false);
  TermList y(1,false);
  Literal* le21 = Literal::create2(lePred, true, y, x);
  TermList xPOne(Term::create2(plusFun, x, one));
  Literal* lt1POne2 = Literal::create2(lePred, true, xPOne, y);
  addTheoryNonUnitClause(units, le21, lt1POne2);

}

// ~$lesseq(X1,X0) | ~$lesseq($sum(X0,1),X1)
void TheoryAxiomGroup::addThirteen(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units)
{
  CALL("TheoryAxiomGroup::addThirteen");

  unsigned lePred = env.signature->getInterpretingSymbol(lessEq);
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  TermList x(0,false);
  TermList y(1,false);
  Literal* nonLe21 = Literal::create2(lePred, false, y, x);
  TermList xPOne(Term::create2(plusFun, x, one));
  Literal* nonLt1POne2 = Literal::create2(lePred, false, xPOne, y);  
  addTheoryNonUnitClause(units, nonLe21, nonLt1POne2);

}

// ~$lesseq($sum(X,1),X)
void TheoryAxiomGroup::addFourteen(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units)
{
  CALL("TheoryAxiomGroup::addFourteen");

  unsigned lePred = env.signature->getInterpretingSymbol(lessEq);
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  TermList x(0,false);
  TermList xPOne(Term::create2(plusFun, x, one));
  Literal* nonLt1POne2 = Literal::create2(lePred, false, xPOne, x);  

  addTheoryUnitClause(nonLt1POne2,units);
}

// ~$lesseq(X0,X1) | $lesseq($sum(X0,X2),$sum(X1,X2))
void TheoryAxiomGroup::addFifteen(Interpretation plus, Interpretation uminus, Interpretation lessEq, TermList zero, TermList one, UnitList* units)
{
  CALL("TheoryAxiomGroup::addFifteen");

  unsigned lePred = env.signature->getInterpretingSymbol(lessEq);
  unsigned addFun = env.signature->getInterpretingSymbol(plus);
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
 * Entry point
 */
void TheoryAxiomGroup::apply(Problem& prb, unsigned group)
{
  CALL("TheoryAxiomGroup::apply(Problem&)");

  Property* prop = prb.getProperty();
  apply(prb.units(), group, prop);
  prb.invalidateProperty();
  prb.reportEqualityAdded(false);
}

/**
 *
 * @return true iff the list of units was modified
 *
 * @author Giles 
 */
void TheoryAxiomGroup::apply(UnitList*& units, unsigned group, Property* prop)
{
  CALL("TheoryAxiomGroup::apply(units,group)");  

  if(prop->usesSort(Sorts::SRT_INTEGER)){ apply(units,group, Sorts::SRT_INTEGER); }
  if(prop->usesSort(Sorts::SRT_RATIONAL)){ apply(units,group, Sorts::SRT_RATIONAL); }
  if(prop->usesSort(Sorts::SRT_REAL)){ apply(units,group, Sorts::SRT_REAL); }
}

void TheoryAxiomGroup::apply(UnitList*& units, unsigned group, unsigned srt)
{
  CALL("TheoryAxiomGroup::apply(units,group,srt)");

  ASS(srt == Sorts::SRT_INTEGER || srt == Sorts::SRT_RATIONAL || srt == Sorts::SRT_REAL);

  Interpretation plus;
  Interpretation uminus;
  Interpretation lessEq;
  TermList zero;
  TermList one;

  if(srt == Sorts::SRT_INTEGER){
    plus = Theory::INT_PLUS;
    uminus = Theory::INT_UNARY_MINUS;
    lessEq = Theory::INT_LESS_EQUAL;
    zero = TermList(theory->representConstant(IntegerConstantType(0)));
    one = TermList(theory->representConstant(IntegerConstantType(1)));
  }
  if(srt == Sorts::SRT_RATIONAL){
    plus = Theory::RAT_PLUS;
    uminus = Theory::RAT_UNARY_MINUS;
    lessEq = Theory::RAT_LESS_EQUAL;
    zero = TermList(theory->representConstant(RationalConstantType(0)));
    one = TermList(theory->representConstant(RationalConstantType(1)));
  }
  if(srt == Sorts::SRT_REAL){
    plus = Theory::REAL_PLUS;
    uminus = Theory::REAL_UNARY_MINUS;
    lessEq = Theory::REAL_LESS_EQUAL;
    zero = TermList(theory->representConstant(RealConstantType(RationalConstantType(0))));
    one = TermList(theory->representConstant(RealConstantType(RationalConstantType(1))));
  }

  // 2^0 = 1u
  if(group & 1u) addOne(plus,uminus,lessEq,zero,one,units);
  // 2^1 = 2u
  if(group & 2u) addTwo(plus,uminus,lessEq,zero,one,units);
  // 2^2 = 4u
  if(group & 4u) addThree(plus,uminus,lessEq,zero,one,units);
  // 2^3 = 8u
  if(group & 8u) addFour(plus,uminus,lessEq,zero,one,units);
  // 2^4 = 16u
  if(group & 16u) addFive(plus,uminus,lessEq,zero,one,units); 
  // 2^5 = 32u
  if(group & 32u) addSix(plus,uminus,lessEq,zero,one,units);
  // 2^6 = 64u
  if(group & 64u) addSeven(plus,uminus,lessEq,zero,one,units);
  // 2^7 = 128u
  if(group & 128u) addEight(plus,uminus,lessEq,zero,one,units);
  // 2^8 = 256u
  if(group & 256u) addNine(plus,uminus,lessEq,zero,one,units);
  // 2^9 = 512u
  if(group & 512u) addTen(plus,uminus,lessEq,zero,one,units);
  // 2^10 = 1024u
  if(group & 1024u) addEleven(plus,uminus,lessEq,zero,one,units);
  // 2^11 = 2048u
  if(group & 2048u) addTwelve(plus,uminus,lessEq,zero,one,units);
  // 2^12 = 4096u
  if(group & 4096u) addThirteen(plus,uminus,lessEq,zero,one,units);
  // 2^13 = 8192u
  if(group & 8192u) addFourteen(plus,uminus,lessEq,zero,one,units);
  // 2^14 = 16384u
  if(group & 16384u) addFifteen(plus,uminus,lessEq,zero,one,units);
  // 2^15 = 32768u

} // TheoryAxiomGroup::apply

