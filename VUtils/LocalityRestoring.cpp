
/*
 * File LocalityRestoring.cpp.
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
 * @file LocalityRestoring.cpp
 * Implements class LocalityRestoring.
 */

#include "Lib/Environment.hpp"

#include "Kernel/FormulaTransformer.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/TermTransformer.hpp"

#include "LocalityRestoring.hpp"

namespace VUtils
{

LocalityRestoring::LocalityRestoring(bool quantLeft, UnitStack& derivation, UnitStack& target)
: _der(derivation), _tgt(target)
{
  CALL("LocalityRestoring::LocalityRestoring");

  if(quantLeft) {
    _quantifiedColor = COLOR_LEFT;
    _nonQuantifiedColor = COLOR_RIGHT;
  }
  else {
    _quantifiedColor = COLOR_RIGHT;
    _nonQuantifiedColor = COLOR_LEFT;
  }

}

bool LocalityRestoring::isLocalDerivation(Unit* refutation)
{
  CALL("LocalityRestoring::perform");

  DHMap<Unit*, Color> unitColors;

  Stack<Unit*> toDo;
  unitColors.insert(refutation, getColor(refutation));
  toDo.push(refutation);
  while(toDo.isNonEmpty()) {
    Unit* u = toDo.pop();
    Color uClr;
    ALWAYS(unitColors.find(u, uClr));

    if(uClr==COLOR_INVALID) { return false; }

    UnitSpecIterator pars = InferenceStore::instance()->getParents(UnitSpec(u));
    while(pars.hasNext()) {
      Unit* par = pars.next().unit();

      Color parClr;
      if(!unitColors.find(par, parClr)) {
	parClr = getColor(par);
	unitColors.insert(par, parClr);
	toDo.push(par);
      }

      if(parClr==COLOR_TRANSPARENT || parClr==uClr) {
	continue;
      }
      if(uClr!=COLOR_TRANSPARENT) {
	return false;
      }
      uClr = parClr;
    }
  }
  return true;
}

bool LocalityRestoring::perform()
{
  CALL("LocalityRestoring::perform");

  buildNSC();
  collectColorsAndLocality();

  if(_allLocal) {
    _tgt = _nscDer;
    cerr << "Derivation was already local" << endl;
    return true;
  }
  cerr << "Derivation not local" << endl;

  processComponents();

  _tgt = _locDer;
  return isLocalDerivation(_locDer.top());
}


//////////////////////////////
// General purpose functions
//

/**
 * Return color of the unit.
 *
 * This function doesn't regard the color of predicates.
 *
 * If there are both colors, COLOR_INVALID is returned (this is
 * what makes the difference from the color retrieval functions
 * that are members of terms and formulas -- these assume there
 * is always just one color).
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

/**
 * Add premisesToAdd among clause premises and transform existing premises by @c map.
 * If allowedPremises is not null, make sure that all original premises are allowed after
 * transformation and add the transformed unit among the allowed when all is done.
 *
 * If new uni is created, also insert the translation into the map
 */
Unit* LocalityRestoring::getUnitWithMappedInference(Unit* u, DHMap<Unit*,Unit*>& map, UnitList* premisesToAdd,
    DHSet<Unit*>* allowedPremises)
{
  CALL("LocalityRestoring::getUnitWithMappedInference");
  if(u->isClause()) { NOT_IMPLEMENTED; }

  bool modified = premisesToAdd!=0;
  UnitList* newPrems = premisesToAdd;

  Inference* origInf = u->inference();
  Inference::Iterator iit(origInf->iterator());
  while(origInf->hasNext(iit)) {
    Unit* premise = origInf->next(iit);
    Unit* newPremise;
    if(map.find(premise, newPremise)) {
      modified = true;
      ASS(!map.find(newPremise));
    }
    else {
      newPremise = premise;
    }
    ASS_REP2(!allowedPremises || allowedPremises->contains(newPremise), newPremise->toString(), u->toString());
    UnitList::push(newPremise, newPrems);
  }
  if(!modified) {
    if(allowedPremises) { allowedPremises->insert(u); }
    return u;
  }
  ASS(newPrems);
  Inference* newInf;
  newPrems = newPrems->reverse(); //keep the same order
  newInf = new InferenceMany(origInf->rule(), newPrems);

  FormulaUnit* fu = static_cast<FormulaUnit*>(u);
  FormulaUnit* newUnit = new FormulaUnit(fu->formula(), newInf, fu->inputType());
  ALWAYS(map.insert(u, newUnit));
  if(allowedPremises) { allowedPremises->insert(newUnit); }
  return newUnit;
}

/////////////////////////////
// Surprising color removal
//

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

/**
 * Collect colored terms that occur in @c u but not in any of its premises.
 */
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

/**
 * Return tautology input clause that contains term @c trm.
 */
Unit* LocalityRestoring::makeNSCPremise(TermList trm)
{
  CALL("LocalityRestoring::makeNSCPremise");
  ASS(trm.isTerm());

  Literal* lit = Literal::createEquality(true, trm, trm, SortHelper::getResultSort(trm.term()));
  Formula* form = new AtomicFormula(lit);
  FormulaUnit* res = new FormulaUnit(form, new Inference0(Inference::INPUT), Unit::AXIOM);
  return res;
}

/**
 * Based on content of @c _der (which contains topologically ordered derivation)
 * build _nscDer where all units except inputs have only the colored terms of their parents.
 */
void LocalityRestoring::buildNSC()
{
  CALL("LocalityRestoring::buildNSC");

#if VDEBUG
  DHSet<Unit*> processedUnits;
  DHSet<Unit*>* processedUnitsChecker = &processedUnits;
#else
  DHSet<Unit*>* processedUnitsChecker = 0;
#endif


  UnitStack::BottomFirstIterator uit(_der);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    TermStack scTerms;
    collectSCTerms(u, scTerms);
    makeUnique(scTerms);

    UnitList* premsToAdd = 0;
    while(scTerms.isNonEmpty()) {
      TermList scTerm = scTerms.pop();
      Unit* prem = makeNSCPremise(scTerm);
      _nscDer.push(prem);
      if(processedUnitsChecker) { processedUnitsChecker->insert(prem); }
      UnitList::push(prem, premsToAdd);
    }
    Unit* nscu = getUnitWithMappedInference(u, _nscConversionMap, premsToAdd, processedUnitsChecker);
    _nscDer.push(nscu);
  }
}

///////////////////////
// Component collection
//

struct LocalityRestoring::CompRecord
{
public:
  //these members are populated from outside

  UnitStack fringe;

  /** In preprocessComponent() the stack gets sorted so that premises
   * go before their consequences */
  UnitStack members;

public:
  //the below members are populated by preprocessing

  /** set of fringe and member units */
  DHSet<Unit*> involvedUnits;

  /**
   * for involved units contains number of the latest unit refering to it
   */
  DHMap<Unit*, Unit*> lastReferringUnits;

  static bool unitNumberComparator(Unit* u1, Unit* u2)
  {
    CALL("LocalityRestoring::CompRecord::unitNumberComparator");

    return u1->number() < u2->number();
  }

  void preprocessComponent()
  {
    CALL("LocalityRestoring::CompRecord::preprocessComponent");

    std::sort(members.begin(), members.end(), unitNumberComparator);

    involvedUnits.loadFromIterator(UnitStack::Iterator(fringe));
    involvedUnits.loadFromIterator(UnitStack::Iterator(members));

    UnitStack::BottomFirstIterator mit(members);
    while(mit.hasNext()) {
      Unit* u = mit.next();
      UnitSpecIterator pars = InferenceStore::instance()->getParents(UnitSpec(u));
      while(pars.hasNext()) {
	Unit* par = pars.next().unit();
	if(!involvedUnits.contains(par)) {
	  continue;
	}
	lastReferringUnits.set(par, u);
      }
    }
  }
};

/**
 * Return true if u is local and conclusion of local inference
 */
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

bool LocalityRestoring::shouldProcess(Unit* u)
{
  CALL("LocalityRestoring::shouldProcess");

  if(!_unitLocality.get(u)) {
    return true;
  }
  Color uClr = _unitColors.get(u);
//  if(uClr!=_quantifiedColor) {
//    return false;
//  }

  bool selfColored = uClr==_quantifiedColor;
  bool childOfUnprocessedQuantifColored = false;
  unsigned processedParCnt = 0;


  UnitSpecIterator pars = InferenceStore::instance()->getParents(UnitSpec(u));
  while(pars.hasNext()) {
    Unit* par = pars.next().unit();
    if(_toBeProcessed.contains(par)) {
      processedParCnt++;
      continue;
    }
    Color parColor = _unitColors.get(par);
    if(parColor==_quantifiedColor) {
      childOfUnprocessedQuantifColored = true;
    }
  }
  if(processedParCnt==0) {
    return false;
  }
  if(processedParCnt>1) {
    return true;
  }
  return selfColored || childOfUnprocessedQuantifColored;
}

void LocalityRestoring::scanForProcessing(Unit* u, IntUnionFind& procComponentUF)
{
  CALL("LocalityRestoring::scanForProcessing");

  if(!shouldProcess(u)) {
    return;
  }
  _toBeProcessed.insert(u);

  unsigned uNumber = u->number();

  UnitSpecIterator pars = InferenceStore::instance()->getParents(UnitSpec(u));
  while(pars.hasNext()) {
    Unit* par = pars.next().unit();
    if(_toBeProcessed.contains(par)) {
      procComponentUF.doUnion(uNumber, par->number());
    }
  }
}

void LocalityRestoring::addComponent(UnitStack& units)
{
  CALL("LocalityRestoring::addComponent");

  CompRecord* rec = new CompRecord();
  rec->members.loadFromIterator(UnitStack::Iterator(units));

  static DHSet<Unit*> fringeSet;
  fringeSet.reset();

  static DHSet<Unit*> memberSet;
  memberSet.reset();
  memberSet.loadFromIterator(UnitStack::Iterator(units));

  UnitStack::Iterator mit(units);
  while(mit.hasNext()) {
    Unit* member = mit.next();
    UnitSpecIterator pars = InferenceStore::instance()->getParents(UnitSpec(member));
    while(pars.hasNext()) {
      Unit* parent = pars.next().unit();
      if(memberSet.contains(parent) || _unitColors.get(parent)!=_quantifiedColor) {
	continue;
      }
      if(!fringeSet.insert(parent)) {
	continue;
      }
      rec->fringe.push(parent);
    }
  }

  rec->preprocessComponent();
  _comps.push(rec);
}

void LocalityRestoring::collectColorsAndLocality()
{
  CALL("LocalityRestoring::collectColorsAndLocality");

  _allLocal = true;

  unsigned maxUnitNumber = _nscDer.top()->number();
  IntUnionFind procComponentUF(maxUnitNumber+1);

  DHMap<unsigned,Unit*> unitsByNumbers;

  UnitStack::BottomFirstIterator uit(_nscDer);
  while(uit.hasNext()) {
    Unit* u = uit.next();

    unitsByNumbers.insert(u->number(), u);

    Color unitColor = getColor(u);
    _unitColors.insert(u, unitColor);

    bool local = isLocal(u);
    _allLocal &= local;
    _unitLocality.insert(u, local);

    scanForProcessing(u, procComponentUF);
  }

  if(_allLocal) { return; }

  static Stack<int> compEls;
  static UnitStack compUnits;

  procComponentUF.evalComponents();
  IntUnionFind::ComponentIterator cit(procComponentUF);
  while(cit.hasNext()) {
    IntUnionFind::ElementIterator eit = cit.next();
    compEls.reset();
    compEls.loadFromIterator(eit);


    if(compEls.size()==1) {
      Unit* u;
      if(!unitsByNumbers.find(compEls.top(), u)) {
        //this component doesn't correspond to any analyzed unit
        continue;
      }
      if(!_toBeProcessed.contains(u)) {
	continue;
      }
    }

    compUnits.reset();
    while(compEls.isNonEmpty()) {
      unsigned num = compEls.pop();
      Unit* u = unitsByNumbers.get(num);
      ASS(_toBeProcessed.contains(u));
      compUnits.push(u);
    }
    addComponent(compUnits);
  }
}


/////////////////////////
// Component processing
//

class LocalityRestoring::FormulaSimplifier : public FormulaTransformer
{
protected:
  virtual Formula* applyLiteral(Formula* form)
  {
    CALL("LocalityRestoring::FormulaSimplifier::applyLiteral");

    Literal* lit = form->literal();
    if(lit->isEquality() && *lit->nthArgument(0)==*lit->nthArgument(1)) {
      return new Formula(lit->isPositive());
    }
    return form;
  }
};

class LocalityRestoring::QuantifyingTermTransformer : public TermTransformer
{
public:
  QuantifyingTermTransformer(LocalityRestoring& parent, unsigned firstAvailableVar)
  : _parent(parent), _nextVar(firstAvailableVar), _introducedVars(0) {}

  void reset(unsigned firstAvailableVar) {
    _nextVar = firstAvailableVar;
    _cache.reset();
    _introducedVars = 0;
  }

  virtual TermList transformSubterm(TermList trm)
  {
    CALL("LocalityRestoring::QuantifyingTermTransformer::transform");

    if(!trm.isTerm()) { return trm; }
    unsigned func = trm.term()->functor();
    Color clr = env.signature->getFunction(func)->color();
    if(clr!=_parent._quantifiedColor) { return trm; }
    if(trm.term()->arity()!=0) {
      ASSERTION_VIOLATION;
      INVALID_OPERATION("cannot restore locality for non-constant colored functions");
    }

    TermList res;
    if(_cache.find(trm, res)) {
      return res;
    }
    res = TermList(_nextVar, false);
    Formula::VarList::push(_nextVar, _introducedVars);
    _nextVar++;
    _cache.insert(trm, res);
    return res;
  }

  /**
   * The variable list returned by this function is never destroyed, so it can be used
   * e.g. by quantifiers
   */
  Formula::VarList* getIntroducedVars() { return _introducedVars; }

private:
  LocalityRestoring& _parent;
  unsigned _nextVar;
  DHMap<TermList,TermList> _cache;
  Formula::VarList* _introducedVars;
};

class LocalityRestoring::FringeKeeper
{
public:

  FringeKeeper(LocalityRestoring& parent, CompRecord& comp) :
    _parent(parent), _comp(comp), _qttransf(parent, 0), _qftransf(_qttransf),
    _currFringeUnit(0)
  {
    CALL("LocalityRestoring::FringeKeeper::FringeKeeper");

    UnitStack::Iterator fit(comp.fringe);
    while(fit.hasNext()) {
      Unit* frUnit = fit.next();
      ASS(getColor(frUnit)==_parent._quantifiedColor);
      Formula* form = getBaseFormula(frUnit);
      _baseForms.push(form);
    }
    _fringePremises = comp.fringe;


    _firstAvailableVar = getFirstAvailableVar(_baseForms);
    _qttransf.reset(_firstAvailableVar);
    requantify();
  }

  FormulaUnit* getFringeUnit()
  {
    CALL("LocalityRestoring::FringeKeeper::getFringeUnit");
    ASS(_fringePremises.isNonEmpty());

    if(_currFringeUnit) { return _currFringeUnit; }

    Formula* form = getFringeFormula();

    UnitList* premiseList = 0;
    UnitList::pushFromIterator(UnitStack::Iterator(_fringePremises), premiseList);

    Inference* inf = new InferenceMany(Inference::COLOR_UNBLOCKING, premiseList);

    FormulaUnit* res = new FormulaUnit(form, inf, Unit::AXIOM);

    _currFringeUnit = res; //this is mandatory, we need to give the same fringe unit for the same fringe
    return res;
  }

  void nextFringe(Unit* unit)
  {
    CALL("LocalityRestoring::FringeKeeper::getBaseFormula");

    FormulaUnit* oldFringe = getFringeUnit();

    _currFringeUnit = 0;

    _fringePremises.reset();
    collectOutsidePremises(unit, _fringePremises);
    _fringePremises.push(oldFringe);

    retireFringeFormulas(unit);

    Formula* baseForm = getBaseFormula(unit);
    _baseForms.push(baseForm);

    unsigned newFormFirstAvailVar = getFirstAvailableVar(baseForm);
    if(newFormFirstAvailVar>_firstAvailableVar) {
      _firstAvailableVar = newFormFirstAvailVar;
      _qttransf.reset(_firstAvailableVar);
      requantify();
    }
    else {
      Formula* qform = quantifyForm(baseForm);
      _quantifiedForms.push(qform);
    }

  }

private:

  Formula* getBaseFormula(Unit* u)
  {
    CALL("LocalityRestoring::FringeKeeper::getBaseFormula");

    if(u->isClause()) { NOT_IMPLEMENTED; }
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    Formula* form = fu->formula();
    Formula* res = Formula::quantify(form);
    _baseFormulaOrigins.insert(res, u);
    return res;
  }

  Formula* getFringeFormula()
  {
    CALL("LocalityRestoring::FringeKeeper::getFringeFormula");
    ASS(_quantifiedForms.isNonEmpty());
    ASS_EQ(_quantifiedForms.size(), _baseForms.size());

    Formula* form;
    if(_quantifiedForms.size()==1) {
      form = _quantifiedForms.top();
    }
    else {
      FormulaList* formList = 0;
      FormulaList::pushFromIterator(FormulaStack::Iterator(_quantifiedForms), formList);
      form = new JunctionFormula(AND, formList);
    }

    Formula* res = new QuantifiedFormula(EXISTS, _qttransf.getIntroducedVars(), 0,form);
    return res;
  }


  Formula* quantifyForm(Formula* form)
  {
    CALL("LocalityRestoring::FringeKeeper::requantify");

    Formula* qform = _qftransf.transform(form);
    qform = FormulaSimplifier().transform(qform);
    return qform;
  }

  void requantify()
  {
    CALL("LocalityRestoring::FringeKeeper::requantify");

    _quantifiedForms.reset();
    FormulaStack::BottomFirstIterator bfit(_baseForms);
    while(bfit.hasNext()) {
      Formula* baseForm = bfit.next();
      Formula* qform = quantifyForm(baseForm);
      _quantifiedForms.push(qform);
    }
  }

  void collectOutsidePremises(Unit* u, UnitStack& acc)
  {
    CALL("LocalityRestoring::FringeKeeper::collectPremises");

    UnitSpecIterator pars = InferenceStore::instance()->getParents(UnitSpec(u));
    while(pars.hasNext()) {
      Unit* par = pars.next().unit();
      if(!_comp.involvedUnits.contains(par)) {
        acc.push(par);
      }
    }
  }

  void retireFringeFormulas(Unit* processedUnit)
  {
    CALL("LocalityRestoring::FringeKeeper::retireFringeFormulas");
    ASS_EQ(_baseForms.size(), _quantifiedForms.size());

    FormulaStack::StableDelIterator bfit(_baseForms);
    FormulaStack::StableDelIterator qfit(_quantifiedForms);
    while(bfit.hasNext()) {
      ALWAYS(qfit.hasNext());
      Formula* form = bfit.next();
      ALWAYS(qfit.next());

      Unit* fOrigin = _baseFormulaOrigins.get(form);

      Unit* lastReferring;
      if(_comp.lastReferringUnits.find(fOrigin, lastReferring) && lastReferring==processedUnit) {
        bfit.del();
        qfit.del();
      }
    }
    ASS(!qfit.hasNext());
  }


  static unsigned getFirstAvailableVar(FormulaStack& forms)
  {
    CALL("LocalityRestoring::FringeKeeper::getFirstAvailableVar(FormulaStack&)");

    unsigned res = 0;
    FormulaStack::Iterator fit(forms);
    while(fit.hasNext()) {
      Formula* f = fit.next();
      unsigned fav = getFirstAvailableVar(f);
      if(fav>res) { res = fav; }
    }
    return res;
  }

  static unsigned getFirstAvailableVar(Formula* form)
  {
    CALL("LocalityRestoring::FringeKeeper::getFirstAvailableVar(Formula*)");

    Formula::VarList* fv = form->freeVariables();
    Formula::VarList* bv = form->boundVariables();
    VirtualIterator<int> vars = pvi( getConcatenatedIterator(
	Formula::VarList::DestructiveIterator(fv), Formula::VarList::DestructiveIterator(bv)) );
    unsigned res = 0;
    while(vars.hasNext()) {
      unsigned v = vars.next();
      if(v>=res) { res = v+1; }
    }
    return res;
  }


private:
  LocalityRestoring& _parent;
  CompRecord& _comp;

  unsigned _firstAvailableVar;

  QuantifyingTermTransformer _qttransf;
  TermTransformingFormulaTransformer _qftransf;

  FormulaStack _baseForms;
  FormulaStack _quantifiedForms;
  UnitStack _fringePremises;

  FormulaUnit* _currFringeUnit;

  DHMap<Formula*, Unit*> _baseFormulaOrigins;
};

Unit* LocalityRestoring::copyWithNewInference(Unit* u, Inference* inf)
{
  CALL("LocalityRestoring::copyWithNewInference");

  if(u->isClause()) { NOT_IMPLEMENTED; }

  FormulaUnit* fu = static_cast<FormulaUnit*>(u);
  Formula* form = fu->formula();
  FormulaUnit* res = new FormulaUnit(form, inf, u->inputType());
  return res;
}

void LocalityRestoring::processComponent(CompRecord& comp)
{
  CALL("LocalityRestoring::processComponent");
  ASS(comp.fringe.isNonEmpty());
  ASS(comp.members.isNonEmpty());

  FringeKeeper fringeKeeper(*this, comp);


  {
    FormulaUnit* fringe = fringeKeeper.getFringeUnit();
    //ensure the initial fringe to be added among the formulas
    Unit* firstUnit = *comp.members.begin();
    _initialFringeTriggerringMap.insert(firstUnit, fringe);
  }

  static UnitStack fringePremises;

  UnitStack::BottomFirstIterator mit(comp.members);
  while(mit.hasNext()) {
    Unit* member = mit.next();
    fringeKeeper.nextFringe(member);

    FormulaUnit* newFringe=fringeKeeper.getFringeUnit();

    Color fuColor = _unitColors.get(member);

    if(fuColor!=COLOR_TRANSPARENT && fuColor!=_nonQuantifiedColor) {
      ALWAYS(_processingResultMap.insert(member, newFringe));
    }
    else {
      ALWAYS(_fringePremiseTriggerringMap.insert(member, newFringe));

      Unit* transpWithFringePremise =
	  copyWithNewInference(member, new Inference1(Inference::COLOR_UNBLOCKING, newFringe));
      ALWAYS(_processingResultMap.insert(member, transpWithFringePremise));
    }
  }
}

void LocalityRestoring::processComponents()
{
  CALL("LocalityRestoring::processComponents");

  while(_comps.isNonEmpty()) {
    CompRecord* comp = _comps.pop();
    processComponent(*comp);
    delete comp;
  }

#if VDEBUG && 0
  DHSet<Unit*> processedUnits;
  DHSet<Unit*>* processedUnitsChecker = &processedUnits;
#else
  DHSet<Unit*>* processedUnitsChecker = 0;
#endif

  UnitStack::BottomFirstIterator uit(_nscDer);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    {
      Unit* fringeUnit;
      if(_initialFringeTriggerringMap.find(u, fringeUnit)) {
	Unit* newFU = getUnitWithMappedInference(fringeUnit, _localConversionMap, 0, processedUnitsChecker);
	_locDer.push(newFU);
      }
    }
    {
      Unit* fringePremiseUnit;
      if(_fringePremiseTriggerringMap.find(u, fringePremiseUnit)) {
	Unit* newFPU = getUnitWithMappedInference(fringePremiseUnit, _localConversionMap, 0, processedUnitsChecker);
	_locDer.push(newFPU);
      }
    }

    Unit* procResult;
    if(_processingResultMap.find(u, procResult)) {
      Unit* newPR = getUnitWithMappedInference(procResult, _localConversionMap, 0, processedUnitsChecker);
      _locDer.push(newPR);
      ALWAYS(_localConversionMap.insert(u, newPR));
    }
    else {
      Unit* newUnit = getUnitWithMappedInference(u, _localConversionMap, 0, processedUnitsChecker);
      _locDer.push(newUnit);
    }
  }

//  {
//    UnitStack::BottomFirstIterator uit2(_nscDer);
//    while(uit2.hasNext()) {
//      Unit* u = uit2.next();
//      UnitSpecIterator pit = InferenceStore::instance()->getParents(UnitSpec(u));
//      unsigned unitNumber = 3728;
//      if(u->number()==unitNumber) {
//	Unit* tgt;
//      }
//
//      while(pit.hasNext()) {
//	Unit* par = pit.next().unit();
////	if(_processingResultMap.find(par)) {
////	}
//      }
//    }
////    InferenceStore::instance()->outputProof(cout, _locDer.top());
//  }
}



}
