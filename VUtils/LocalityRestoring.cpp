/**
 * @file LocalityRestoring.cpp
 * Implements class LocalityRestoring.
 */

#include "Lib/Environment.hpp"

#include "Kernel/FormulaTransformer.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/TermTransformer.hpp"

#include "LocalityRestoring.hpp"

namespace VUtils
{

LocalityRestoring::LocalityRestoring(UnitStack& derivation, UnitStack& target)
: _der(derivation), _tgt(target)
{
  CALL("LocalityRestoring::LocalityRestoring");

  _quantifiedColor = COLOR_LEFT;
  _nonQuantifiedColor = COLOR_RIGHT;

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
  return true;
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
      UnitList::push(prem, premsToAdd);
    }
    Unit* nscu = getUnitWithMappedInference(u, _nscConversionMap, premsToAdd);
    _nscDer.push(nscu);
  }
}

///////////////////////
// Component collection
//

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
//    LOGV(member->toString());
    UnitSpecIterator pars = InferenceStore::instance()->getParents(UnitSpec(member));
    while(pars.hasNext()) {
      Unit* parent = pars.next().unit();
      if(memberSet.contains(parent) || _unitColors.get(parent)!=_quantifiedColor) {
	continue;
      }
      if(!fringeSet.insert(parent)) {
	continue;
      }
//      LOGV(parent->toString());
      rec->fringe.push(parent);
    }
  }
//  LOGV(rec->fringe.size());

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
//    if(unitColor==COLOR_INVALID) { LOGV(u->toString()); }

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

bool unitNumberComparator(Unit* u1, Unit* u2)
{
  CALL("unitNumberComparator");

  return u1->number() < u2->number();
}

class LocalityRestoring::QuantifyingTermTransformer : public TermTransformer
{
public:
  QuantifyingTermTransformer(LocalityRestoring& parent, unsigned firstAvailableVar)
  : _parent(parent), _nextVar(firstAvailableVar), _introducedVars(0) {}

  virtual TermList transform(TermList trm)
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

  Formula::VarList* getIntroducedVars() { return _introducedVars; }

  static unsigned getFirstAvailableVar(Formula* form)
  {
    CALL("LocalityRestoring::QuantifyingTermTransformer::getFirstAvailableVar");

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
  unsigned _nextVar;
  DHMap<TermList,TermList> _cache;
  Formula::VarList* _introducedVars;
};

FormulaUnit* LocalityRestoring::generateQuantifiedFormula(FormulaIterator forms, UnitIterator premises)
{
  CALL("LocalityRestoring::generateQuantifiedFormula");
  ASS(forms.hasNext());

  FormulaList* formList = 0;
  FormulaList::pushFromIterator(forms, formList);

  Formula* form;
  if(formList->tail()) {
    form = new JunctionFormula(AND, formList);
  }
  else {
    form = FormulaList::pop(formList);
  }

  unsigned firstAvVar = QuantifyingTermTransformer::getFirstAvailableVar(form);
  QuantifyingTermTransformer ttransf(*this, firstAvVar);
  TermTransformingFormulaTransformer ftransf(ttransf);

  Formula* qformBody = ftransf.transform(form);
  Formula* qform = new QuantifiedFormula(EXISTS, ttransf.getIntroducedVars(), qformBody);

  UnitList* premiseList = 0;
  UnitList::pushFromIterator(premises, premiseList);

#if VDEBUG
  {
    UnitList::Iterator pit(premiseList);
    while(pit.hasNext()) {
      Unit* premise = pit.next();
      Color pclr = getColor(premise);
      ASS_REP(pclr!=COLOR_INVALID, premise->toString());
    }
  }
#endif

  Inference* inf = new InferenceMany(Inference::COLOR_UNBLOCKING, premiseList);

  FormulaUnit* res = new FormulaUnit(qform, inf, Unit::AXIOM);
  return res;
}

void LocalityRestoring::collectPremises(Unit* u, DHSet<Unit*>& skippedPremises, UnitStack& acc)
{
  CALL("LocalityRestoring::collectPremises");

  UnitSpecIterator pars = InferenceStore::instance()->getParents(UnitSpec(u));
  while(pars.hasNext()) {
    Unit* par = pars.next().unit();
    if(!skippedPremises.contains(par)) {
      acc.push(par);
    }
  }
}

void LocalityRestoring::processComponent(CompRecord& comp)
{
  CALL("LocalityRestoring::processComponent");
  ASS(comp.fringe.isNonEmpty());
  ASS(comp.members.isNonEmpty());

  std::sort(comp.members.begin(), comp.members.end(), unitNumberComparator);

  FormulaStack fringeArgs;

  UnitStack::Iterator fit(comp.fringe);
  while(fit.hasNext()) {
    Unit* frUnit = fit.next();
    ASS(_unitColors.get(frUnit)==_quantifiedColor);
    if(frUnit->isClause()) { NOT_IMPLEMENTED; }
    FormulaUnit* fu = static_cast<FormulaUnit*>(frUnit);
    Formula* form = fu->formula();
    fringeArgs.push(form);
  }

  FormulaUnit* fringe = generateQuantifiedFormula(pvi( FormulaStack::Iterator(fringeArgs) ),
      pvi( UnitStack::Iterator(comp.fringe) ));

  {
    //ensure the initial fringe to be added among the formulas
    Unit* firstUnit = *comp.members.begin();
    _initialFringeTriggerringMap.insert(firstUnit, fringe);
  }

  DHSet<Unit*> skippedPremises;
  skippedPremises.loadFromIterator(UnitStack::Iterator(comp.fringe));
  skippedPremises.loadFromIterator(UnitStack::Iterator(comp.members));

  static UnitStack fringePremises;

  UnitStack::BottomFirstIterator mit(comp.members);
  while(mit.hasNext()) {
    Unit* member = mit.next();
    if(member->isClause()) { NOT_IMPLEMENTED; }
    FormulaUnit* fu = static_cast<FormulaUnit*>(member);
    Formula* form = fu->formula();
    fringeArgs.push(form);

    fringePremises.reset();
    collectPremises(fu, skippedPremises, fringePremises);
    fringePremises.push(fringe);

    FormulaUnit* newFringe=generateQuantifiedFormula(pvi( FormulaStack::Iterator(fringeArgs) ),
	pvi( UnitStack::Iterator(fringePremises) ));

    Color fuColor = _unitColors.get(fu);

//    LOGV(fu->toString());
//    LOG("");
//    LOGV(newFringe->toString());

    if(fuColor!=COLOR_TRANSPARENT && fuColor!=_nonQuantifiedColor) {
      _processingResultMap.insert(fu, newFringe);
    }
    else {
      _fringePremiseTriggerringMap.insert(fu, newFringe);
      FormulaUnit* transpWithFringePremise = new FormulaUnit(form, new Inference1(Inference::COLOR_UNBLOCKING, newFringe), fu->inputType());
      _processingResultMap.insert(fu, transpWithFringePremise);
//      LOGV(transpWithFringePremise->toString());
    }

    fringe = newFringe;
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

  UnitStack::BottomFirstIterator uit(_nscDer);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    {
      Unit* fringeUnit;
      if(_initialFringeTriggerringMap.find(u, fringeUnit)) {
	Unit* newFU = getUnitWithMappedInference(fringeUnit, _localConversionMap);
	_locDer.push(newFU);
      }
    }
    {
      Unit* fringePremiseUnit;
      if(_fringePremiseTriggerringMap.find(u, fringePremiseUnit)) {
	Unit* newFPU = getUnitWithMappedInference(fringePremiseUnit, _localConversionMap);
	_locDer.push(newFPU);
      }
    }

    Unit* procResult;
    if(_processingResultMap.find(u, procResult)) {
      Unit* newPR = getUnitWithMappedInference(procResult, _localConversionMap);
      _locDer.push(newPR);
      ALWAYS(_localConversionMap.insert(u, newPR));
    }
    else {
      Unit* newUnit = getUnitWithMappedInference(u, _localConversionMap);
      _locDer.push(newUnit);
    }
  }
}



}
