
/*
 * File RangeColoring.cpp.
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
 * @file RangeColoring.cpp
 * Implements class RangeColoring.
 */

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

#include "Kernel/FormulaUnit.hpp"
#include "Kernel/FormulaTransformer.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/TermTransformer.hpp"


#include "RangeColoring.hpp"

namespace VUtils
{

class TermColoring::ColoringTermTransformer : public TermTransformer
{
public:
  using TermTransformer::transform;

  ColoringTermTransformer(TermColoring& parent) : _parent(parent) {}

protected:
  virtual TermList transformSubterm(TermList trm)
  {
    return _parent.applyToTerm(trm);
  }

private:
  TermColoring& _parent;
};

TermList TermColoring::applyToTerm(TermList trm)
{
  CALL("TermColoring::applyToTerm");

  if(!trm.isTerm() || !isColoredFunction(trm.term()->functor())) {
    return trm;
  }

  TermList res;
  if(_cache.find(trm, res)) {
    return res;
  }

  Color clr = getColor(trm);
  vstring name = trm.toString();
  size_t nlen = name.size();
  for(size_t i=0; i<nlen; i++) {
    if(name[i]=='(' || name[i]==')' || name[i]=='\'') {
      name[i] = '_';
    }
  }
  vstring name0 = name;
  int i=0;
  while(env.signature->functionExists(name, 0)) {
    i++;
    name = name0+Int::toString(i);
  }

  unsigned func = env.signature->addFunction(name, 0);
  Signature::Symbol* funSym = env.signature->getFunction(func);
  if(clr!=COLOR_TRANSPARENT) {
    funSym->addColor(clr);
  }
  BaseType* type = new FunctionType(SortHelper::getResultSort(trm.term()));
  funSym->setType(type);

  Term* resTerm = Term::create(func, 0, 0);
  res = TermList(resTerm);

  ALWAYS(_cache.insert(trm, res));
  return res;
}

Formula* TermColoring::applyToFormula(Formula* f)
{
  CALL("TermColoring::applyToFormula");

  ColoringTermTransformer ttrans(*this);
  TermTransformingFormulaTransformer ftrans(ttrans);

  Formula* res = ftrans.transform(f);
  return res;
}

/**
 * @c inp is a stack where premises go before their conclusions.
 * The refutation must therefore be at the top of the stack.
 *
 * The order will be preserved inside @c out
 */
void TermColoring::applyToDerivation(UnitStack& inp, UnitStack& out)
{
  CALL("TermColoring::applyToDerivation");

  DHMap<Unit*,Unit*> translated;
  UnitStack::BottomFirstIterator uit(inp);
  while(uit.hasNext()){
    FormulaUnit* fu = static_cast<FormulaUnit*>(uit.next());
    ASS(!fu->isClause());

    Formula* newForm = applyToFormula(fu->formula());

    UnitList* newPrems = 0;
    Inference* origInf = fu->inference();
    Inference::Iterator iit(origInf->iterator());
    while(origInf->hasNext(iit)) {
      Unit* premise = origInf->next(iit);
      Unit* newPremise = translated.get(premise);
      UnitList::push(newPremise, newPrems);
    }
    Inference* newInf;
    if(newPrems) {
      newPrems = newPrems->reverse();
      newInf = new InferenceMany(origInf->rule(), newPrems);
    }
    else {
      newInf = new Inference0(origInf->rule());
    }

    FormulaUnit* newUnit = new FormulaUnit(newForm, newInf, fu->inputType());
    if(newUnit->inference()->rule()==Inference::INPUT) {
      Color clr = newUnit->formula()->getColor();
      if(clr!=COLOR_TRANSPARENT) {
	newUnit->setInheritedColor(clr);
      }
    }


    out.push(newUnit);
    translated.insert(fu, newUnit);
  }
}

bool TermColoring::isLocal(Unit* u)
{
  CALL("TermColoring::isLocal");
  ASS(!u->isClause());

  FormulaUnit* fu = static_cast<FormulaUnit*>(u);

  Color clr = COLOR_TRANSPARENT;

  SubformulaIterator sfit(fu->formula());
  while(sfit.hasNext()) {
    Formula* sf = sfit.next();
    if(sf->connective()!=LITERAL) {
      continue;
    }
    Literal* lit = sf->literal();

    SubtermIterator stit(lit);
    while(stit.hasNext()) {
      TermList trm = stit.next();
      if(!trm.isTerm()) {
	continue;
      }
      unsigned func = trm.term()->functor();
      if(!isColoredFunction(func)) {
	continue;
      }
      Color tColor = getColor(trm);
      if(tColor!=COLOR_TRANSPARENT) {
	if(clr==COLOR_TRANSPARENT) {
	  clr = tColor;
	}
	if(clr!=tColor) {
	  return false;
	}
      }
    }
  }
  return true;
}

bool TermColoring::areUnitsLocal(UnitStack& units)
{
  CALL("TermColoring::areUnitsLocal");

  UnitStack::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if(!isLocal(u)) {
      cerr<<"Non-local unit: "<<u->toString()<<endl;
      return false;
    }
  }
  return true;
}

///////////////////////
// RangeColoring
//

void RangeColoring::addFunction(unsigned func)
{
  CALL("RangeColoring::addFunction");
  ASS_EQ(env.signature->functionArity(func),1);

  ALWAYS(_funcs.insert(func));
}

void RangeColoring::setMiddleValue(IntegerConstantType val)
{
  CALL("RangeColoring::setMiddleValue");

  _middle = val;
}

bool RangeColoring::isColoredFunction(unsigned func)
{
  CALL("RangeColoring::isColoredFunction");

  return _funcs.contains(func);
}


Color RangeColoring::getColor(TermList term)
{
  CALL("RangeColoring::getColor");
  ASS(term.isTerm());
  ASS(_funcs.contains(term.term()->functor()));

  TermList arg = *term.term()->nthArgument(0);
  ASS(theory->isInterpretedConstant(arg));

  IntegerConstantType val;
  ALWAYS(theory->tryInterpretConstant(arg, val));

//  if(val==0 || val==_middle) { return COLOR_TRANSPARENT; }
  if(val==_middle) { return COLOR_TRANSPARENT; }
  if(val<_middle) { return COLOR_LEFT; }
  ASS_G(val,_middle);
  return COLOR_RIGHT;
}


///////////////////////
// NameMapColoring
//

vstring NameMapColoring::normalizeName(vstring str)
{
  CALL("NameMapColoring::normalizeName");

  if(str[0]=='\'') {
    str = str.substr(1,str.size()-2);
  }
  return str;
}

bool NameMapColoring::isColoredFunction(unsigned func)
{
  CALL("NameMapColoring::isColoredFunction");

  vstring nm = normalizeName(env.signature->functionName(func));
  return _funcColors.find(nm);
}
Color NameMapColoring::getColor(TermList term)
{
  CALL("NameMapColoring::getColor");
  ASS(term.isTerm());

  vstring nm = normalizeName(term.term()->functionName());
  return _funcColors.get(nm);
}


}
