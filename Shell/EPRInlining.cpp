/**
 * @file EPRInlining.cpp
 * Implements class EPRInlining.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/MultiCounter.hpp"
#include "Lib/SCCAnalyzer.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Shell/Options.hpp"

#include "Flattening.hpp"
#include "PDUtils.hpp"
#include "Rectify.hpp"
#include "SimplifyFalseTrue.hpp"
#include "Statistics.hpp"
#include "VarManager.hpp"

#include "EPRInlining.hpp"

namespace Shell
{
/**
 * @warning The units must not contain formulas with predicate equivalences
 * (these are formulas which can be interpreted as predicate
 * definitions in two ways).
 */
void EPRRestoring::scan(UnitList* units)
{
  CALL("EPRRestoring::scan");  

  UnitList::Iterator it(units);
  while(it.hasNext()) {
    Unit* u = it.next();
    if(u->isClause()) {
      continue;
    }
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    if(PDUtils::hasDefinitionShape(fu)) {
      if(scanDefinition(fu)) {
	continue;
      }
    }
  }

  performClosure();
  processActiveDefinitions(units);
}

void EPRRestoring::performClosure()
{
  CALL("EPRRestoring::performClosure");

  while(_newNEPreds.isNonEmpty()) {
    unsigned p = _newNEPreds.pop_front();
    int polarity = _nonEprDefPolarities[p];
    DepMap::ValList::Iterator deps = _dependent.keyIterator(p);
    while(deps.hasNext()) {
      pair<FormulaUnit*,int> depRecord = deps.next(); //unit and the polarity with which p appears in it
      FormulaUnit* u = depRecord.first;
      int inheritedPolarity = polarity*depRecord.second*(_nonEprReversedPolarity[p] ? -1 : 1);
      addNEDef(u, _defPreds.get(u), inheritedPolarity);
    }
  }

  // for each NE predicate contains number of NE predicates on which it depends
  // for predicates which were removing in order to break cycles, contains negative value
  ZIArray<int> dependencyCnt;
  MapToLIFO<unsigned,unsigned> dependencies;
  static Stack<unsigned> zeroPreds;
  static Stack<unsigned> deps;
  zeroPreds.reset();

  Stack<unsigned>::Iterator neIt(_nonEprPreds);
  while(neIt.hasNext()) {
    unsigned p = neIt.next();
    FormulaUnit* u = _nonEprDefs[p];
    ASS(u);
    deps.reset();
    u->collectPredicates(deps);
    makeUnique(deps);

    unsigned neDepCnt = 0;
    while(deps.isNonEmpty()) {
      unsigned dep = deps.pop();
      if(dep!=p && _nonEprDefs[dep]) {
	neDepCnt++;
	dependencies.pushToKey(dep, p);
      }
    }
    if(neDepCnt==0) {
      zeroPreds.push(p);
    }
    else {
      dependencyCnt[p] = neDepCnt;
    }
  }

  {
    MapToLIFOGraph<unsigned> gr(dependencies);
    SCCAnalyzer<MapToLIFOGraph<unsigned> > scca(gr);
    if(scca.breakingNodes().isNonEmpty()) {
      if (env->options->showPreprocessing()) {
        env->beginOutput();
        env->out() << "[PP] Cycle among definitions detected" << std::endl;
        env->endOutput();
      }
      Stack<unsigned>::ConstIterator bpIt1(scca.breakingNodes());
      while(bpIt1.hasNext()) {
	unsigned breakingPred = bpIt1.next();
	dependencyCnt[breakingPred] = -1;
      }
      Stack<unsigned>::ConstIterator bpIt(scca.breakingNodes());
      while(bpIt.hasNext()) {
	unsigned breakingPred = bpIt.next(); //cycle-breaking predicate (will be removed to break cycle)
  if (env->options->showPreprocessing()) {
    env->beginOutput();
    env->out() << "[PP]  - breaking cycle by ignoring definition "
            << _nonEprDefs[breakingPred]->toString() << std::endl;
    env->endOutput();
  }

	MapToLIFO<unsigned,unsigned>::ValList::Iterator depIt=dependencies.keyIterator(breakingPred);
	while(depIt.hasNext()) {
	  unsigned dep = depIt.next();
	  dependencyCnt[dep]--;
	  if(dependencyCnt[dep]==0) {
	    zeroPreds.push(dep);
	  }
	}
      }
    }
  }

  while(zeroPreds.isNonEmpty()) {
    unsigned p = zeroPreds.pop();
    FormulaUnit* u = _nonEprDefs[p];
    _activeUnits.insert(u);
    _activePreds.push(p);

    if (env->options->showPreprocessing()) {
      env->beginOutput();
      env->out() << "[PP] Unit "<<(*u)<<" activated" << std::endl;
      env->endOutput();
    }

    MapToLIFO<unsigned,unsigned>::ValList::Iterator depIt=dependencies.keyIterator(p);
    while(depIt.hasNext()) {
      unsigned dep = depIt.next();
      dependencyCnt[dep]--;
      if(dependencyCnt[dep]==0) {
	zeroPreds.push(dep);
      }
    }
  }
}

bool EPRRestoring::addNEDef(FormulaUnit* unit, unsigned pred, int polarity)
{
  CALL("EPRRestoring::addNEDef");

  if(_nonEprDefs[pred]) {
    if(_nonEprDefs[pred]!=unit) {
      if (env->options->showPreprocessing()) {
        env->beginOutput();
        env->out() << "[PP] Unit "<<(*unit)<<" identified as EPR violating definition and ignored "
            "because there is already such definition for the predicate" << std::endl;
        env->endOutput();
      }
      //we already have a different non-epr definition, so we'll ignore this one
      return false;
    }
    int newPolarity = combinePolarities(_nonEprDefPolarities[pred],polarity);
    if(_nonEprDefPolarities[pred]==newPolarity) {
      return true;
    }
    _nonEprDefPolarities[pred] = newPolarity;
  }
  else {
    if (env->options->showPreprocessing()) {
      env->beginOutput();
      env->out() << "[PP] Unit "<<(*unit)<<" identified as EPR violating definition" << std::endl;
      env->endOutput();
    }
    _nonEprDefs[pred] = unit;
    _nonEprDefPolarities[pred] = polarity;
    _nonEprPreds.push(pred);
  }
  _newNEPreds.push_back(pred);
  return true;
}

bool EPRRestoring::scanDefinition(FormulaUnit* unit)
{
  CALL("EPRRestoring::scanDefinition");
  ASS(!PDUtils::isPredicateEquivalence(unit)); //predicate equivalences must be removed before applying this rule

  Literal* lhs;
  Formula* rhs;
  PDUtils::splitDefinition(unit, lhs, rhs);
  unsigned pred = lhs->functor();

  _defPreds.insert(unit, pred);

  int polarity;
  if(isNonEPRDef(lhs, rhs, polarity)) {
    if(!addNEDef(unit, pred, polarity)) {
      //we already have a non-epr definition, so we'll ignore this one
      return false;
    }
    _nonEprReversedPolarity[pred] = lhs->isNegative();
  }

  static Stack<pair<unsigned,int> > dependencies;
  rhs->collectPredicatesWithPolarity(dependencies);
  makeUnique(dependencies);
  while(dependencies.isNonEmpty()) {
    pair<unsigned,int> d = dependencies.pop();
    int polarity = d.second;
    _dependent.pushToKey(d.first, make_pair(unit, polarity));
  }

  return true;
}

/**
 * Return true if clausification of definition @c lhs<=>rhs will lead
 * to introduction of non-constant skolem functions
 */
bool EPRRestoring::isNonEPRDef(Literal* lhs, Formula* rhs, int& polarity)
{
  CALL("EPRRestoring::isNonEPRDef/3");

  if(lhs->arity()==0) {
    return false;
  }
  bool haveUniversal = false;
  bool haveExistential = false;
  SubformulaIterator sfit(rhs);
  while(sfit.hasNext()) {
    int sfPol;
    Formula* sf = sfit.next(sfPol);
    if(sf->connective()!=FORALL && sf->connective()!=EXISTS) {
      continue;
    }
    if(sfPol==0) {
      polarity = 0;
      return true;
    }
    if( (sf->connective()==FORALL) == (sfPol==1) ) {
      haveUniversal = true;
    }
    else {
      haveExistential = true;
    }
  }
  if(!haveUniversal && !haveExistential) {
    return false;
  }
  polarity = (!haveExistential) ? -1 : (!haveUniversal) ? 1 : 0;
  return true;
}

int EPRRestoring::combinePolarities(int p1, int p2)
{
  CALL("EPRRestoring::combinePolarities");

  return (p1==p2) ? p1 : 0;
}

///////////////////////
// EPRInlining
//

void EPRInlining::apply(Problem& prb)
{
  CALL("EPRInlining::apply(Problem&)");

  if(apply(prb.units())) {
    prb.invalidateProperty();
  }
}

bool EPRInlining::apply(UnitList*& units)
{
  CALL("EPRInlining::apply");  

  bool modified = false;

  {
    //remove predicate equivalences    
    PDInliner pdi(false);
    bool eqInlinerModified = pdi.apply(units, true);
    modified |= eqInlinerModified;
  }

  scan(units);

  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    Unit* newUnit = apply(u);
    if(u==newUnit) {
      continue;
    }
    if(newUnit) {
      uit.replace(newUnit);
    }
    else {
      uit.del();
    }
    modified = true;
  }
  return modified;
}

void EPRInlining::processActiveDefinitions(UnitList* units)
{
  CALL("EPRInlining::processActiveDefinitions");
  
  PDInliner defInliner(false);

  Stack<unsigned>::BottomFirstIterator apit(_activePreds);
  while(apit.hasNext()) {
    unsigned p = apit.next();
    FormulaUnit* u = _nonEprDefs[p];
    u = static_cast<FormulaUnit*>(defInliner.apply(u));
    ASS(!u->isClause());
    ALWAYS(defInliner.tryGetDef(u));
    _nonEprDefs[p] = u;

    int polarity = _nonEprDefPolarities[p];
    Literal* lhs;
    Formula* rhs;
    PDUtils::splitDefinition(u, lhs, rhs);
    switch(polarity) {
    case 1:
      _inliner.addAsymetricDefinition(lhs, rhs, 0, rhs, u);
      break;
    case -1:
      _inliner.addAsymetricDefinition(lhs, 0, rhs, rhs, u);
      break;
    case 0:
      _inliner.addAsymetricDefinition(lhs, rhs, rhs, rhs, u);
      break;
    default:
      ASSERTION_VIOLATION;
    }
  }
}

Unit* EPRInlining::apply(Unit* unit)
{
  CALL("EPRInlining::apply");  

  if(_activeUnits.find(unit)) {
    unsigned pred = _defPreds.get(unit);
    if(_nonEprDefPolarities[pred]==0) {
      //we are inlining all occurences, so we may delete the definition
      return 0;
    }
    else {
      //we are inlining just one polarity, the UPDR will take care of simplifying
      //this definition
      return unit;
    }
  }
  return _inliner.apply(unit);
}

}
