
/*
 * File AxiomGenerator.cpp.
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
 * @file AxiomGenerator.cpp

 * Implements class AxiomGenerator.
 */


#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "AxiomGenerator.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

#if 1

#else

namespace AxGen
{

LazyConstant::operator TermBlock()
{
  return iConst(val);
}


TermBlock iConst(InterpretedType val)
{
  CALL("AxGen::fun0");

  return fun(env.signature->addInterpretedConstant(val), 0);
}

TermBlock fun0(Interpretation te)
{
  CALL("AxGen::fun0");

  return fun(te, 0);
}

TermBlock fun1(Interpretation te, const TermBlock& b1)
{
  CALL("AxGen::fun1");

  return fun(te, &b1);
}

TermBlock fun2(Interpretation te, const TermBlock& b1, const TermBlock& b2)
{
  CALL("AxGen::fun2");

  TermBlock args[]={b1,b2};
  return fun(te, args);
}

FormBlock pred2(Interpretation te, bool positive, const TermBlock& b1, const TermBlock& b2)
{
  CALL("AxGen::pred2");

  TermBlock args[]={b1,b2};
  return pred(te, positive, args);
}

/**
 * Create function interpreted as @b te. If the function is constant,
 * @b args must be equal to 0, and @b ctx contains pointer to the context.
 * Otherwise @b ctx can be 0, and @b args points to array of @b n elements
 * where @b n is the arity of the function corresponding to @b te.
 * (Therefore the size of the array @b args is at least 1 in this case.)
 */
TermBlock fun(Interpretation te, const TermBlock* args)
{
  CALL("AxGen::fun(Interpretation...)");

  return fun(env.signature->getInterpretingSymbol(te), args);
}

/**
 * Create predicate interpreted as @b te. If the predicate is propositional,
 * @b args must be equal to 0, and @b ctx contains pointer to the context.
 * Otherwise @b ctx can be 0, and @b args points to array of @b n elements
 * where @b n is the arity of the function corresponding to @b te.
 * (Therefore the size of the array @b args is at least 1 in this case.)
 */
FormBlock pred(Interpretation te, bool positive, const TermBlock* args)
{
  CALL("AxGen::pred(Interpretation...)");

  return pred(env.signature->getInterpretingSymbol(te), positive, args);
}

TermBlock var(unsigned num)
{
  CALL("AxGen::var");

  return TermBlock(TermList(num, false));
}

TermBlock fun(unsigned fn, const TermBlock* args)
{
  CALL("AxGen::fun(unsigned...)");

  unsigned arity=env.signature->functionArity(fn);

  static DArray<TermList> targs;
  targs.ensure(arity);

  for(unsigned i=0;i<arity;i++) {
    targs[i]=args[i].term;
  }

  Term* t=Term::create(fn, arity, targs.array());
  return TermBlock(TermList(t));
}

FormBlock pred(unsigned pred, bool positive, const TermBlock* args)
{
  CALL("AxGen::pred(unsigned...)");

  unsigned arity=env.signature->predicateArity(pred);

  Literal* lit;
  if(pred==0) {
    ASS_EQ(arity,2);
    lit=Literal::createEquality(positive, args[0].term, args[1].term);
  }
  else {
    static DArray<TermList> targs;
    targs.ensure(arity);

    for(unsigned i=0;i<arity;i++) {
      targs[i]=args[i].term;
    }
    lit=Literal::create(pred, 2, positive, false, targs.array());
  }

  return FormBlock(new AtomicFormula(lit));
}


FormBlock operator==(const TermBlock& b1, const TermBlock& b2)
{ return pred2(Theory::EQUAL, true, b1, b2); }

FormBlock operator!=(const TermBlock& b1, const TermBlock& b2)
{ return pred2(Theory::EQUAL, false, b1, b2); }

FormBlock operator>(const TermBlock& b1, const TermBlock& b2)
{ return pred2(Theory::GREATER, true, b1, b2); }

FormBlock operator<=(const TermBlock& b1, const TermBlock& b2)
{ return pred2(Theory::LESS_EQUAL, true, b1, b2); }

FormBlock operator<(const TermBlock& b1, const TermBlock& b2)
{ return pred2(Theory::LESS, true, b1, b2); }

FormBlock operator>=(const TermBlock& b1, const TermBlock& b2)
{ return pred2(Theory::GREATER_EQUAL, true, b1, b2); }

TermBlock operator+(const TermBlock& b1, const TermBlock& b2)
{ return fun2(Theory::PLUS, b1, b2); }
TermBlock operator-(const TermBlock& b1, const TermBlock& b2)
{ return fun2(Theory::MINUS, b1, b2); }
TermBlock operator*(const TermBlock& b1, const TermBlock& b2)
{ return fun2(Theory::MULTIPLY, b1, b2); }
TermBlock operator/(const TermBlock& b1, const TermBlock& b2)
{ return fun2(Theory::DIVIDE, b1, b2); }

TermBlock operator++(const TermBlock& b1,int)
{ return fun1(Theory::SUCCESSOR, b1); }
TermBlock operator-(const TermBlock& b1)
{ return fun1(Theory::UNARY_MINUS, b1); }

//formula operators

//negation
FormBlock operator!(const FormBlock& f)
{
  CALL("AxGen::operator!(FormBlock)");

  return FormBlock(new NegatedFormula(f.form));
}

//disjunction
FormBlock operator|(const FormBlock& l, const FormBlock& r)
{
  CALL("AxGen::operator&(FormBlock,FormBlock)");

  FormulaList* args=0;
  FormulaList::push(r.form, args);
  FormulaList::push(l.form, args);
  return FormBlock(new JunctionFormula(OR, args));
}

//conjunction
FormBlock operator&(const FormBlock& l, const FormBlock& r)
{
  CALL("AxGen::operator&(FormBlock,FormBlock)");

  FormulaList* args=0;
  FormulaList::push(r.form, args);
  FormulaList::push(l.form, args);
  return FormBlock(new JunctionFormula(AND, args));
}

//the following two implement --> for implication
HalfImpl operator--(const FormBlock& l, int)
{
  return HalfImpl(l);
}
FormBlock operator>(const HalfImpl& l, const FormBlock& r)
{
  CALL("AxGen::operator>(HalfImpl,FormBlock)");

  return FormBlock(new BinaryFormula(IMP, l.fb.form, r.form));
}

//the following two implement -=- for equivalence
FormBlock operator-=(const FormBlock& l, const HalfEquiv& r)
{
  CALL("AxGen::operator-=(FormBlock,HalfEquiv)");

  return FormBlock(new BinaryFormula(IFF, l.form, r.fb.form));
}
HalfEquiv operator-(const FormBlock& r)
{
  return HalfEquiv(r);
}


};

TermBlock AxiomGenerator::idiv(TermBlock arg1, TermBlock arg2)
{ return fun2(Theory::INT_QUOTIENT_E, arg1, arg2); }

FormBlock AxiomGenerator::igt(TermBlock arg1, TermBlock arg2)
{ return pred2(Theory::INT_GREATER, true, arg1, arg2); }
FormBlock AxiomGenerator::ige(TermBlock arg1, TermBlock arg2)
{ return pred2(Theory::INT_GREATER_EQUAL, true, arg1, arg2); }
FormBlock AxiomGenerator::ilt(TermBlock arg1, TermBlock arg2)
{ return pred2(Theory::INT_LESS, true, arg1, arg2); }
FormBlock AxiomGenerator::ile(TermBlock arg1, TermBlock arg2)
{ return pred2(Theory::INT_LESS_EQUAL, true, arg1, arg2); }

FormBlock AxiomGenerator::ex(TermBlock var, FormBlock f)
{
  ASS(var.term.isVar());
  Formula::VarList* vars=0;
  Formula::VarList::push(var.term.var(), vars);
  return FormBlock(new QuantifiedFormula(EXISTS, vars,0, f.form));
}


void AxiomGenerator::axiom(FormBlock b)
{
  CALL("AxiomGenerator::axiom");

  Inference* inf=new Inference(Inference::THEORY);
  UnitList::push(new FormulaUnit(b.form, inf, Unit::AXIOM), _acc);
}

UnitList* AxiomGenerator::getAxioms()
{
  CALL("AxiomGenerator::getAxioms");

  zero=LazyConstant(0);
  one=LazyConstant(1);
  X0=var(0);
  X1=var(1);
  X2=var(2);
  X3=var(3);
  X4=var(4);

  _acc=0;

  //stabilize the list of included symbols
  size_t oldPESize=_presentElements.size();
  for(;;) {
    inclusionImplications();
    if(oldPESize==_presentElements.size()) {
      break;
    }
    oldPESize=_presentElements.size();
  }
  
  enumerate();
  return _acc;
}



#endif

};


