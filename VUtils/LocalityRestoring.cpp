/**
 * @file LocalityRestoring.cpp
 * Implements class LocalityRestoring.
 */

#include "Lib/Environment.hpp"

#include "Kernel/FormulaUnit.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/TermIterators.hpp"

#include "LocalityRestoring.hpp"

namespace VUtils
{

LocalityRestoring::LocalityRestoring(Stack<Unit*>& derivation, Stack<Unit*>& target)
: _der(derivation), _tgt(target)
{
  CALL("LocalityRestoring::LocalityRestoring");

  unsigned dlen = derivation.length();
  for(unsigned i=0; i<dlen; i++) {
    _unitIndexes.insert(_der[i], i);
  }

  _quantifiedColor = COLOR_LEFT;

}

bool LocalityRestoring::perform()
{
  CALL("LocalityRestoring::perform");

  buildNSC();
  collectColorsAndLocality();

  if(_allLocal) {
    _tgt = _nscDer;
    return true;
  }
  return false;
}

bool LocalityRestoring::isLocal(Unit* u)
{
  CALL("LocalityRestoring::isLocal");

  Color clr = _unitColors.get(u);

  if(clr==COLOR_INVALID) {
    return false;
  }

  UnitSpecIterator parIt = InferenceStore::instance()->getParents(UnitSpec(u));
  while(parIt.hasNext()) {
    Unit* par = parIt.next().unit();
    Color pclr = _unitColors.get(par);
    if(pclr!=COLOR_TRANSPARENT && pclr!=clr) {
      if(clr==COLOR_TRANSPARENT) {
	clr = pclr;
      }
      if(pclr!=clr) {
	return false;
      }
    }
  }
  return clr!=COLOR_INVALID;
}

/**
 * If new uni is created, also insert the translation into the map
 */
Unit* LocalityRestoring::getUnitWithMappedInference(Unit* u, DHMap<Unit*,Unit*>& map, UnitList* premisesToAdd)
{
  CALL("LocalityRestoring::getUnitWithMappedInference");
  if(u->isClause()) { NOT_IMPLEMENTED; }

  bool modified = premisesToAdd!=0;
  UnitList* newPrems = premisesToAdd;

  Inference* origInf = u->inference();
  Inference::Iterator iit(origInf->iterator());
  while(origInf->hasNext(iit)) {
    Unit* premise = origInf->next(iit);
//      LOGV(premise->toString());
    Unit* newPremise;
    if(map.find(premise, newPremise)) {
      modified = true;
    }
    else {
      newPremise = premise;
    }
    UnitList::push(newPremise, newPrems);
  }
  if(!modified) {
    return u;
  }
  ASS(newPrems);
  Inference* newInf;
  newPrems = newPrems->reverse(); //keep the same order
  newInf = new InferenceMany(origInf->rule(), newPrems);

  FormulaUnit* fu = static_cast<FormulaUnit*>(u);
  FormulaUnit* newUnit = new FormulaUnit(fu->formula(), newInf, fu->inputType());
  map.insert(u, newUnit);
  return newUnit;
}

void LocalityRestoring::collectColoredTerms(Unit* u, TermStack& acc)
{
  CALL("LocalityRestoring::collectColoredTerms");
  if(u->isClause()) { NOT_IMPLEMENTED; }

  FormulaUnit* fu = static_cast<FormulaUnit*>(u);
  Formula* form = fu->formula();

  SubformulaIterator sfit(form);
  while(sfit.hasNext()) {
    Formula* sf = sfit.next();
    if(sf->connective()!=LITERAL) {
      continue;
    }
    Literal* lit = sf->literal();
    SubtermIterator stit(lit);
    while(stit.hasNext()) {
      TermList trm = stit.next();
      if(trm.isVar()) { continue; }
      Color fnColor = env.signature->getFunction(trm.term()->functor())->color();
      if(fnColor!=COLOR_TRANSPARENT) {
	acc.push(trm);
      }
    }
  }
}

void LocalityRestoring::collectSCTerms(Unit* u, TermStack& acc)
{
  CALL("LocalityRestoring::collectSCTerms");

  static DHSet<TermList> parentTerms;
  parentTerms.reset();

  static TermStack ctAcc;
  UnitSpecIterator pars = InferenceStore::instance()->getParents(UnitSpec(u));
  while(pars.hasNext()) {
    UnitSpec par = pars.next();
    ctAcc.reset();
    collectColoredTerms(par.unit(), ctAcc);
    TermStack::Iterator ctit(ctAcc);
    while(ctit.hasNext()) {
      TermList trm = ctit.next();
      if(trm.term()->arity()!=0) { NOT_IMPLEMENTED; }
      parentTerms.insert(trm);
    }
  }

  ctAcc.reset();
  collectColoredTerms(u, ctAcc);
  TermStack::Iterator ctit(ctAcc);
  while(ctit.hasNext()) {
    TermList trm = ctit.next();
    if(trm.term()->arity()!=0) { NOT_IMPLEMENTED; }
    if(!parentTerms.contains(trm)) {
      acc.push(trm);
    }
  }
}

Unit* LocalityRestoring::makeNSCPremise(TermList trm)
{
  CALL("LocalityRestoring::makeNSCPremise");
  ASS(trm.isTerm());

  Literal* lit = Literal::createEquality(true, trm, trm);
  Formula* form = new AtomicFormula(lit);
  FormulaUnit* res = new FormulaUnit(form, new Inference(Inference::INPUT), Unit::AXIOM);
  return res;
}

void LocalityRestoring::buildNSC()
{
  CALL("LocalityRestoring::buildNSC");

  Stack<Unit*>::BottomFirstIterator uit(_der);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    TermStack scTerms;
    collectSCTerms(u, scTerms);

    UnitList* premsToAdd = 0;
    while(scTerms.isNonEmpty()) {
      TermList scTerm = scTerms.pop();
      Unit* prem = makeNSCPremise(scTerm);
      _nscDer.push(prem);
      UnitList::push(prem, premsToAdd);
    }
    Unit* nscu = getUnitWithMappedInference(u, _nscConversionMap, premsToAdd);
    _nscDer.push(nscu);
  }
}

bool LocalityRestoring::shouldProcess(Unit* u)
{
  CALL("LocalityRestoring::shouldProcess");

  if(!_unitLocality.get(u)) {
    return true;
  }
  Color uClr = _unitColors.get(u);
  if(uClr!=_quantifiedColor) {
    return false;
  }
  UnitSpecIterator pars = InferenceStore::instance()->getParents(UnitSpec(u));
  while(pars.hasNext()) {
    Unit* par = pars.next().unit();
    if(_toBeProcessed.contains(par)) {
      return true;
    }
  }
  return false;
}

void LocalityRestoring::collectColorsAndLocality()
{
  CALL("LocalityRestoring::collectColorsAndLocality");

  _allLocal = true;

  Stack<Unit*>::BottomFirstIterator uit(_nscDer);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    Color unitColor = getColor(u);
    _unitColors.insert(u, unitColor);
//    if(unitColor==COLOR_INVALID) { LOGV(u->toString()); }

    bool local = isLocal(u);
    _allLocal &= local;
    _unitLocality.insert(u, local);
//    if(u->number()==4571 || u->number()==4574) { LOG(unitColor<<" "<<u->toString()); }
//    if(u->number()==308 || u->number()==307) { LOG(unitColor<<" "<<u->toString()); }
  }
}

/**
 * Return color of the unit.
 *
 * This function doesn't regard the color of predicates.
 *
 * If there are both colors, COLOR_INVALID is returned.
 */
Color LocalityRestoring::getColor(Unit* u)
{
  CALL("LocalityRestoring::getColor");
  ASS(!u->isClause());

  FormulaUnit* fu = static_cast<FormulaUnit*>(u);

  Color unitColor = COLOR_TRANSPARENT;

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
      Color tColor = env.signature->getFunction(func)->color();
      if(tColor!=COLOR_TRANSPARENT) {
	if(unitColor==COLOR_TRANSPARENT) {
	  unitColor = tColor;
	}
	if(unitColor!=tColor) {
	  return COLOR_INVALID;
	}
      }
    }
  }
  return unitColor;
}

void LocalityRestoring::extractComponents()
{

}


}
