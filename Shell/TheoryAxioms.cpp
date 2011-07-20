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

void TheoryAxioms::addTheoryUnit(Literal* lit, UnitList*& units)
{
  CALL("TheoryAxioms::addTheoryUnit");

  Clause* unit = Clause::fromIterator(getSingletonIterator(lit), Unit::AXIOM, new Inference(Inference::THEORY));
  UnitList::push(unit, units);
}

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
}


void TheoryAxioms::addCommutativity(Interpretation op, UnitList*& units)
{
  CALL("TheoryAxioms::addCommutativity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned func = env.signature->getInterpretingSymbol(op);
  TermList v1(0,false);
  TermList v2(1,false);
  TermList f12(Term::create2(func, v1, v2));
  TermList f21(Term::create2(func, v2, v1));
  Literal* eq = Literal::createEquality(true, f12, f21);

  addTheoryUnit(eq, units);
}

void TheoryAxioms::addAssociativity(Interpretation op, UnitList*& units)
{
  CALL("TheoryAxioms::addCommutativity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned func = env.signature->getInterpretingSymbol(op);
  TermList v1(0,false);
  TermList v2(1,false);
  TermList v3(2,false);
  TermList f12(Term::create2(func, v1, v2));
  TermList f23(Term::create2(func, v2, v3));
  TermList f1f23(Term::create2(func, v1, f23));
  TermList ff12_3(Term::create2(func, f12, v3));
  Literal* eq = Literal::createEquality(true, f1f23, ff12_3);

  addTheoryUnit(eq, units);
}

void TheoryAxioms::addIdentity(Interpretation op, TermList idElement, UnitList*& units)
{
  CALL("TheoryAxioms::addIdentity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned func = env.signature->getInterpretingSymbol(op);
  TermList v1(0,false);
  TermList f1I(Term::create2(func, v1, idElement));
  Literal* eq = Literal::createEquality(true, f1I, idElement);

  addTheoryUnit(eq, units);
}

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
  TermList v1(0,false);
  TermList v2(1,false);
  TermList f12(Term::create2(opFunc, v1, v2));
  TermList nv1(Term::create1(invFunc, v1));
  TermList nv2(Term::create1(invFunc, v2));
  TermList nf12(Term::create1(invFunc, f12));
  TermList fn1n2(Term::create2(opFunc, nv2, nv1));
  Literal* eq1 = Literal::createEquality(true, nf12, fn1n2);
  addTheoryUnit(eq1, units);

  //X0+(-X0)==idElement
  TermList f1n1(Term::create2(opFunc, v1, nv1));
  Literal* eq2 = Literal::createEquality(true, f1n1, idElement);
  addTheoryUnit(eq2, units);
}

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

void TheoryAxioms::addTotalOrderAxioms(Interpretation lessEqual, UnitList*& units)
{
  CALL("TheoryAxioms::addTotalOrderAxioms");

  addReflexivity(lessEqual, units);
  addTransitivity(lessEqual, units);
  addOrderingTotality(lessEqual, units);
}

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
  Literal* v1EqV2 = Literal::createVariableEquality(true, v1, v2, varSort);
  Literal* nonLe12 = Literal::create2(lePred, false, v1, v2);
  addTheoryClause(units, nonLe21, nonLe12, v1EqV2);
}

void TheoryAxioms::addAdditionOrderingAndMultiplicationAxioms(Interpretation plus, Interpretation unaryMinus,
    TermList zeroElement, TermList oneElement, Interpretation lessEqual, Interpretation multiply,
    UnitList*& units)
{
  CALL("TheoryAxioms::addAdditionOrderingAndMultiplicationAxioms");

  addAdditionAndOrderingAxioms(plus, unaryMinus, zeroElement, oneElement, lessEqual, units);

  addCommutativity(multiply, units);
  addAssociativity(multiply, units);
  addIdentity(multiply, oneElement, units);

  //axiom( X0*zero==zero );
  unsigned mulFun = env.signature->getInterpretingSymbol(multiply);
  TermList v1(0,false);
  TermList v1MulZero(0,false);
  Literal* v1EqV1MulZero = Literal::createEquality(true, v1MulZero, zeroElement);
  addTheoryUnit(v1EqV1MulZero, units);

  //axiom( X0*(X1++)==(X0*X1)+X0 );
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  TermList v2(1,false);
  TermList v2POne(Term::create2(plusFun, v2, oneElement));
  TermList v1MulV2POne(Term::create2(mulFun, v1, v2POne));
  TermList v1MulV2(Term::create2(mulFun, v1, v2));
  TermList v1MulV2PV1(Term::create2(plusFun, v1MulV2, v1));
  Literal* succDistrEq = Literal::createEquality(true, v1MulV2POne, v1MulV2PV1);
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
  Literal* distrEq = Literal::createEquality(true, distrLhs, distrRhs);
  addTheoryUnit(distrEq, units);
}

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


#if 0

struct TheoryAxioms::Arithmetic
: public AxiomGenerator
{
  void inclusionImplications()
  {
    if(has(Theory::INT_GREATER_EQUAL) || has(Theory::INT_LESS) || has(Theory::INT_GREATER)) {
      include(Theory::INT_LESS_EQUAL);
    }
    if(has(Theory::INT_LESS_EQUAL)) {
      include(Theory::PLUS);
    }

    if(has(Theory::MINUS)) {
      include(Theory::PLUS);
    }
    if(has(Theory::UNARY_MINUS)) {
       include(Theory::PLUS);
    }
    if(has(Theory::PLUS)) {
      include(Theory::UNARY_MINUS);
      include(Theory::INT_GREATER);
    }


    if(has(Theory::INT_DIVIDE)) {
      include(Theory::MINUS);
      include(Theory::PLUS);
      include(Theory::MULTIPLY);

      include(Theory::INT_GREATER);
      include(Theory::INT_GREATER_EQUAL);
      include(Theory::INT_LESS);
      include(Theory::INT_LESS_EQUAL);
    }
//    if(has(Theory::DIVIDE)) {
//      include(Theory::MULTIPLY);
//    }
  }
  void enumerate()
  {
    if(has(Theory::PLUS)) {
      ASS(has(Theory::INT_GREATER));

      //group axioms
      axiom( (X0+X1)+X2==X0+(X1+X2) );
      axiom( X0+zero==X0 );
      axiom( -(X0+X1)==(-X0)+(-X1) );
      axiom( X0+(-X0)==zero );

      //commutativity
      axiom( X0+X1==X1+X0 );


      //order axioms
      axiom( ile(X0,X0) );
      axiom( (ile(X0,X1) & ile(X1,X2)) --> ile(X0,X2) );

      //total order
      axiom( (ile(X0,X1)) | ile(X1,X0) );

      //connects groups and order
      axiom( ile(X1,X2) --> ile(X1+X0,X2+X0) );

      //specific for arithmetic
      axiom( ile(zero,one) );
      axiom( ilt(X0,X1) --> ile(X0+one,X1) );

      //connect strict and non-strict inequality
      axiom( (ile(X0,X1)) --> ((X0==X1) | ilt(X0,X1)) );

    }
#if VDEBUG
    else {
      ASS(!has(Theory::INT_GREATER));
    }
#endif

//    if(has(Theory::GREATER)) {
//      axiom( !(X0>X0) );
//      axiom( ((X0>X1) & (X1>X2)) --> (X0>X2) );
//
//      //total order
//      axiom( (!(X0>X1)) | !(X1>X0) );
//
//      //specific for arithmetic
//      axiom( one>zero );
//
////      axiom( (!(X0>X1)) --> ((X0==X1) | (X1>X0)) );
//
//      if(has(Theory::PLUS)) {
//	axiom( (X1>X2) --> (X1+X0>X2+X0) );
//      }
//      if(has(Theory::SUCCESSOR)) {
//	axiom( X0++>X0 );
//      }
//    }
//
    if(has(Theory::MULTIPLY)) {
      axiom( X0*X1==X1*X0 );
      axiom( (X0*X1)*X2==X0*(X1*X2) );
      axiom( X0*one==X0 );
      axiom( X0*zero==zero );

      if(has(Theory::PLUS)) {
        axiom( X0*(X1++)==(X0*X1)+X0 );
        axiom( (X0+X1)*(X2+X3) == (X0*X2 + X0*X3 + X1*X2 + X1*X3) );
//	axiom( X0*(X1+X2) == (X0*X1 + X0*X2) );
      }
    }
    if(has(Theory::INT_DIVIDE)) {
      axiom( (ige(X0,zero) & igt(X1,zero)) --> ( ilt(X0-X1, idiv(X0,X1)*X1) & ile(idiv(X0,X1)*X1, X0) ) );
      axiom( (ilt(X0,zero) & ilt(X1,zero)) --> ( igt(X0-X1, idiv(X0,X1)*X1) & ige(idiv(X0,X1)*X1, X0) ) );
      axiom( (ige(X0,zero) & ilt(X1,zero)) --> ( ilt(X0+X1, idiv(X0,X1)*X1) & ile(idiv(X0,X1)*X1, X0) ) );
      axiom( (ilt(X0,zero) & igt(X1,zero)) --> ( igt(X0+X1, idiv(X0,X1)*X1) & ige(idiv(X0,X1)*X1, X0) ) );
      axiom( (ilt(X0,zero) & igt(X1,zero)) --> ( igt(X0+X1, idiv(X0,X1)*X1) & ige(idiv(X0,X1)*X1, X0) ) );

      axiom( (X1!=zero) --> (idiv(X0,X1)+X2==idiv(X0+(X1*X2),X1)) );
    }
//    if(has(Theory::DIVIDE)) {
//      axiom( (X1!=zero) --> ( (X0/X1==X2) -=- (X1*X2==X0) ) );
//    }
  }
};

#endif

/**
 * Add theory axioms to the @b units list that are relevant to
 * units present in the list. Update the property object @b prop.
 * Replace in each formula instances of X-Y by X+(-Y) and X++ by
 * X+1 and <,<=,>= by >.
 */
void TheoryAxioms::apply(UnitList*& units, Property* prop)
{
  CALL("TheoryAxioms::apply");

  if(!env.signature->anyInterpretedSymbols()) {
    //If we don't have any interpreted symbols (besides equality)
    //there won't be any theory axioms added anyway
    return;
  }

#if 0
  Arithmetic axGen;
  //find out which symbols are used in the problem
  SymCounter sctr(*env.signature);
  sctr.count(units,1);
  for(unsigned i=0;i<Theory::MAX_INTERPRETED_ELEMENT; i++) {
    Interpretation interp=static_cast<Interpretation>(i);
    if(!env.signature->haveInterpretingSymbol(interp)) {
      continue;
    }
    if(Theory::isFunction(interp)) {
      unsigned fn=env.signature->getInterpretingSymbol(interp);
      if(sctr.getFun(fn).occ()) {
	axGen.include(interp);
      }
    }
    else {
      unsigned pred=env.signature->getInterpretingSymbol(interp);
      SymCounter::Pred* pc=&sctr.getPred(pred);
      if(pc->pocc() || pc->nocc() || pc->docc()) {
	axGen.include(interp);
      }
    }
  }

  UnitList* newAxioms=axGen.getAxioms();
  if(newAxioms) {
    prop->scan(newAxioms);
  }

  units=UnitList::concat(newAxioms, units);

  //replace some function and predicate definitions
  if( axGen.has(Theory::MINUS) || axGen.has(Theory::SUCCESSOR) ||
      axGen.has(Theory::INT_LESS_EQUAL) || axGen.has(Theory::INT_LESS) ||
      axGen.has(Theory::INT_GREATER_EQUAL) ) {
    UnitList::DelIterator us(units);
    while (us.hasNext()) {
      Unit* u = us.next();
      Unit* v = replaceFunctions(u);
      if (v != u) {
	us.replace(v);
      }
    }
  }

#endif
}

/**
 * Replace some functions and predicates by their definitions
 */
Unit* TheoryAxioms::replaceFunctions(Unit* u)
{
  CALL("TheoryAxioms::replaceFunctions(Unit*)");

  if(!u->isClause()) {
    Formula* f=static_cast<FormulaUnit*>(u)->formula();
    Formula* g=replaceFunctions(f);
    if(f==g) {
      return u;
    }
    return new FormulaUnit(g, new Inference1(Inference::INTERPRETED_SIMPLIFICATION, u) , u->inputType());
  }

  Clause* cl=static_cast<Clause*>(u);
  unsigned clen=cl->length();

  static LiteralStack lits;
  lits.reset();
  bool modified=false;
  for(unsigned i=0;i<clen;i++) {
    Literal* l=(*cl)[i];
    Literal* m=replaceFunctions(l);
    lits.push(m);
    if(l!=m) {
      modified=true;
    }
  }

  if(!modified) {
    return u;
  }
  return Clause::fromIterator(LiteralStack::Iterator(lits), u->inputType(),
      new Inference1(Inference::INTERPRETED_SIMPLIFICATION, u));
}

/**
 * Replace some functions and predicates by their definitions
 */
Formula* TheoryAxioms::replaceFunctions(Formula* f)
{
  CALL("TheoryAxioms::replaceFunctions(Formula*)");

  switch (f->connective()) {
  case LITERAL:
    {
      Literal* lit = replaceFunctions(f->literal());
      return lit == f->literal() ? f : new AtomicFormula(lit);
    }

  case AND:
  case OR:
    {
      FormulaList* newArgs = replaceFunctions(f->args());
      if (newArgs == f->args()) {
	return f;
      }
      return new JunctionFormula(f->connective(), newArgs);
    }

  case IMP:
  case IFF:
  case XOR:
    {
      Formula* l = replaceFunctions(f->left());
      Formula* r = replaceFunctions(f->right());
      if (l == f->left() && r == f->right()) {
	return f;
      }
      return new BinaryFormula(f->connective(), l, r);
    }

  case NOT:
    {
      Formula* arg = replaceFunctions(f->uarg());
      if (f->uarg() == arg) {
	return f;
      }
      return new NegatedFormula(arg);
    }

  case FORALL:
  case EXISTS:
    {
      Formula* arg = replaceFunctions(f->qarg());
      if (arg == f->qarg()) {
	return f;
      }
      return new QuantifiedFormula(f->connective(),f->vars(),arg);
    }

  case TRUE:
  case FALSE:
    return f;

  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Replace some functions and predicates by their definitions
 */
FormulaList* TheoryAxioms::replaceFunctions(FormulaList* fs)
{
  CALL("TheoryAxioms::replaceFunctions(FormulaList*)");

  if (fs->isEmpty()) {
    return fs;
  }
  Formula* f = fs->head();
  FormulaList* tail = fs->tail();
  Formula* g = replaceFunctions(f);
  FormulaList* gs = replaceFunctions(tail);

  if (f == g && tail == gs) {
    return fs;
  }
  return new FormulaList(g,gs);

}

/**
 * Replace some functions and predicates by their definitions
 */
Literal* TheoryAxioms::replaceFunctions(Literal* l)
{
  CALL("TheoryAxioms::replaceFunctions(Literal*)");

  //Term to be replaced
  //The terms are put on the stack in a 'parents first' manner,
  //so if we replace minuses in parent terms first, we do not
  //need to rescan repeatedly the term for new minus-term occurences.
  static Stack<TermList> rTerms;
  rTerms.reset();

  SubtermIterator sit(l);
  while(sit.hasNext()) {
    TermList t=sit.next();
    if(theory->isInterpretedFunction(t, Theory::MINUS) ||
	theory->isInterpretedFunction(t, Theory::SUCCESSOR)) {
      rTerms.push(t);
    }
  }

  //now let's do the replacing
  Stack<TermList>::BottomFirstIterator rit(rTerms);
  while(rit.hasNext()) {
    TermList orig=rit.next();
    Term* ot=orig.term();
    TermList repl;
    if(theory->isInterpretedFunction(ot, Theory::MINUS)) {
      ASS_EQ(ot->arity(),2);
      TermList arg2Neg=TermList(theory->fun1(Theory::UNARY_MINUS, *ot->nthArgument(1)));
      repl=TermList(theory->fun2(Theory::PLUS, *ot->nthArgument(0), arg2Neg));
    }
    else {
      ASS(theory->isInterpretedFunction(ot, Theory::SUCCESSOR));
      ASS_EQ(ot->arity(),1);
      repl=TermList(theory->fun2(Theory::PLUS, *ot->nthArgument(0), theory->one()));
    }
    l=EqHelper::replace(l, orig, repl);
  }

  if(theory->isInterpretedPredicate(l)) {
    Interpretation itpPred=theory->interpretPredicate(l);
    //we want to transform all integer inequalities to INT_LESS_EQUAL
    if(itpPred==Theory::INT_GREATER || itpPred==Theory::INT_GREATER_EQUAL || itpPred==Theory::INT_LESS) {
      bool polarity=l->polarity();
      if(itpPred==Theory::INT_GREATER || itpPred==Theory::INT_LESS) {
	polarity^=1;
      }
      TermList arg1=*l->nthArgument(0);
      TermList arg2=*l->nthArgument(1);
      if(itpPred==Theory::INT_LESS || itpPred==Theory::INT_GREATER_EQUAL) {
	swap(arg1, arg2);
      }

      l=theory->pred2(Theory::INT_LESS_EQUAL, polarity, arg1, arg2);
    }
  }

  return l;
}

}
