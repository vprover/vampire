/**
 * @file AIGInliner.cpp
 * Implements class AIGInliner.
 */

#include "Lib/MapToLIFO.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Term.hpp"

#include "Options.hpp"
#include "PDUtils.hpp"

#include "AIGInliner.hpp"

namespace Shell
{

AIGInliner::AIGInliner()
{
  CALL("AIGInliner::AIGInliner");

  _onlySingleAtomPreds = false;
}

void AIGInliner::updateModifiedProblem(Problem& prb)
{
  CALL("AIGInliner::updateModifiedProblem");

  prb.invalidateByRemoval();
}


void AIGInliner::scanOccurrences(UnitList* units)
{
  CALL("AIGInliner::scanOccurrences");

  DHSet<Literal*> seenPosLits;
  //used locally inside the loop
  Stack<unsigned> locClPreds;
  LiteralStack uLits;

  UnitList::Iterator uit1(units);
  while(uit1.hasNext()) {
    Unit* u = uit1.next();

    if(u->isClause()) {
      locClPreds.reset();
      u->collectPredicates(locClPreds);
      _clPreds.loadFromIterator(Stack<unsigned>::Iterator(locClPreds));
      continue;
    }

    ASS(uLits.isEmpty());
    u->collectAtoms(uLits);
    while(uLits.isNonEmpty()) {
      Literal* l = uLits.pop();
      if(seenPosLits.contains(l)) {
	continue;
      }
      seenPosLits.insert(l);
      _predLits.pushToKey(l->functor(), l);
    }
  }
}

void AIGInliner::collectDefinitions(UnitList* units,
    FormulaStack& lhsForms, FormulaStack& rhsForms, Stack<FormulaUnit*>& defUnits)
{
  CALL("AIGInliner::collectDefinitions");

  UnitList::Iterator uit2(units);
  while(uit2.hasNext()) {
    Unit* u = uit2.next();

    if(u->isClause()) {
      continue;
    }

    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    ASS(!PDUtils::isPredicateEquivalence(fu));
    if(!PDUtils::hasDefinitionShape(u)) {
      continue;
    }
    Literal* lhs;
    Formula* rhs;
    PDUtils::splitDefinition(fu, lhs, rhs);

    if(_onlySingleAtomPreds) {
      unsigned pred = lhs->functor();
      if(_clPreds.contains(pred) || _predLits.keyValCount(pred)>1) {
	continue;
      }
    }

    lhsForms.push(new AtomicFormula(lhs));
    rhsForms.push(rhs);
    defUnits.push(fu);
  }
}

void AIGInliner::addDefinitionReplacement(Formula* lhs, Formula* rhs, FormulaUnit* def)
{
  CALL("AIGInliner::addDefinitionReplacement");

  unsigned pred = lhs->literal()->functor();

  ASS_G(_predLits.keyValCount(pred),0);
  ASS(_predLits.keyValCount(pred)!=1 || _predLits.keyVals(pred)->head()==Literal::positiveLiteral(lhs->literal()));

  bool safeToRemove = !_clPreds.contains(pred) || _predLits.keyValCount(pred)>1;
  if(safeToRemove) {
    ALWAYS(_defReplacements.insert(def, 0));
    return;
  }
  rhs = _fsh.apply(rhs).first;
  Formula* form = new BinaryFormula(IFF, lhs, rhs);
  Formula::VarList* freeVars = form->freeVariables();
  if(freeVars) {
    form = new QuantifiedFormula(FORALL, freeVars, form);
  }
  //TODO: add proper inferences
  FormulaUnit* defTgt = new FormulaUnit(form, new Inference1(Inference::DEFINITION_UNFOLDING, def), def->inputType());
  ALWAYS(_defReplacements.insert(def, defTgt));
}

/**
 * Units must not contain predicate eqivalences
 */
void AIGInliner::scan(UnitList* units)
{
  CALL("AIGInliner::scan");

  scanOccurrences(units);

  FormulaStack lhsForms;
  FormulaStack rhsForms;
  Stack<FormulaUnit*> defUnits;

  collectDefinitions(units, lhsForms, rhsForms, defUnits);

  ASS_EQ(lhsForms.size(), rhsForms.size());
  ASS_EQ(lhsForms.size(), defUnits.size());
  Stack<unsigned> usedIdxs;
  _fsh.addRewriteRules(lhsForms.size(), lhsForms.begin(), rhsForms.begin(), &usedIdxs);

  while(usedIdxs.isNonEmpty()) {
    unsigned idx = usedIdxs.pop();
    Formula* lhs = lhsForms[idx];
    Formula* rhs = rhsForms[idx];
    FormulaUnit* def = defUnits[idx];

    addDefinitionReplacement(lhs, rhs, def);
  }
}

bool AIGInliner::apply(FormulaUnit* unit, FormulaUnit*& res)
{
  CALL("AIGInliner::apply(FormulaUnit*,FormulaUnit*&)");

  if(_defReplacements.find(unit, res)) {
    return true;
  }
  return _fsh.apply(unit, res);
}


////////////////////////////
// AIGDefinitionIntroducer
//

AIGDefinitionIntroducer::AIGDefinitionIntroducer(Options& opts)
{
  CALL("AIGDefinitionIntroducer::AIGDefinitionIntroducer");

  _eprPreserving = opts.eprPreservingNaming();
  _namingRefCntThreshold = 3; //TODO: add option
}

void AIGDefinitionIntroducer::scanDefinition(FormulaUnit* def)
{
  CALL("AIGDefinitionIntroducer::scanDefinition");

  Literal* lhs;
  Formula* rhs;
  PDUtils::splitDefinition(def, lhs, rhs);

  AIGRef rhsAig = _fsh.apply(rhs).second;

  if(!_defs.insert(rhsAig, lhs)) {
    //rhs is already defined
    Literal* oldDefTgt;
    ALWAYS(_defs.find(rhsAig, oldDefTgt));
    _equivs.insert(lhs, oldDefTgt);
    return;
  }
  ALWAYS(_defUnits.insert(rhsAig,def));

  _toplevelAIGs.push(rhsAig);
}

void AIGDefinitionIntroducer::collectTopLevelAIGsAndDefs(UnitList* units)
{
  CALL("AIGDefinitionIntroducer::collectTopLevelAIGsAndDefs");

  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if(u->isClause()) {
      continue;
    }
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);

    if(PDUtils::hasDefinitionShape(fu)) {
      scanDefinition(fu);
      continue;
    }

    Formula* form = fu->formula();
    AIGRef formAig = _fsh.apply(form).second;
    _toplevelAIGs.push(formAig);
  }
}

void AIGDefinitionIntroducer::doFirstRefAIGPass()
{
  CALL("AIGDefinitionIntroducer::doFirstRefAIGPass");

  ASS(_refAIGInfos.isEmpty());
  size_t aigCnt = _refAIGs.size();
  for(size_t i=0; i<aigCnt; ++i) {
    AIGRef r = _refAIGs[i];
    ASS(r.polarity());
    _aigIndexes.insert(r, i);

    _refAIGInfos.push(NodeInfo());
    NodeInfo& ni = _refAIGInfos.top();

    ni._directRefCnt = 0;
    if(!_defs.find(r, ni._name)) {
      ni._name = 0;
    }

    ni._hasQuant[0] = false;
    ni._hasQuant[1] = r.isQuantifier();

    unsigned parCnt = r.parentCnt();
    for(unsigned pi = 0; pi<parCnt; ++pi) {
      AIGRef par = r.parent(pi);
      bool neg = !par.polarity();
      AIGRef posPar = neg ? par.neg() : par;
      unsigned parStackIdx = _aigIndexes.get(posPar);
      NodeInfo& pni = _refAIGInfos[parStackIdx];

      pni._directRefCnt++;
      ni._hasQuant[0^neg] |= pni._hasQuant[0];
      ni._hasQuant[1^neg] |= pni._hasQuant[1];
    }

    //initialize values for the second pass
    ni._inPol[0] = ni._inPol[1] = false;
    ni._inQuant[0] = ni._inQuant[1] = false;
    ni._formRefCnt = 0;

  }
}

bool AIGDefinitionIntroducer::shouldIntroduceName(unsigned aigStackIdx)
{
  CALL("AIGDefinitionIntroducer::shouldIntroduceName");

  AIGRef a = _refAIGs[aigStackIdx];
  NodeInfo& ni = _refAIGInfos[aigStackIdx];

//  if(_eprPreserving) {
//    if(ni._inPol[1] && ni._inQuant[1] && ni._hasQuant )
//  }

  return _namingRefCntThreshold && ni._formRefCnt>=_namingRefCntThreshold;
}

void AIGDefinitionIntroducer::doSecondRefAIGPass()
{
  CALL("AIGDefinitionIntroducer::doSecondRefAIGPass");

  AIGStack::Iterator tlit(_toplevelAIGs);
  while(tlit.hasNext()) {
    AIGRef a = tlit.next();
    bool neg = !a.polarity();
    AIGRef aPos = neg ? a.neg() : a;
    unsigned stackIdx = _aigIndexes.get(aPos);
    NodeInfo& ni = _refAIGInfos[stackIdx];
    ni._formRefCnt++;
    ni._inPol[a.polarity()] = true;
  }

  ASS(_refAIGInfos.isEmpty());
  size_t aigCnt = _refAIGs.size();
  for(size_t i=aigCnt; i>0;) {
    i--;

    AIGRef r = _refAIGs[i];
    NodeInfo& ni = _refAIGInfos[i];



    unsigned parCnt = r.parentCnt();
    for(unsigned pi = 0; pi<parCnt; ++pi) {
      AIGRef par = r.parent(pi);
      bool neg = !par.polarity();
      AIGRef posPar = neg ? par.neg() : par;
      unsigned parStackIdx = _aigIndexes.get(posPar);
      NodeInfo& pni = _refAIGInfos[parStackIdx];

      pni._directRefCnt++;
      ni._hasQuant[0^neg] |= pni._hasQuant[0];
      ni._hasQuant[1^neg] |= pni._hasQuant[1];
    }
  }
}

void AIGDefinitionIntroducer::scan(UnitList* units)
{
  CALL("AIGDefinitionIntroducer::scan");

  collectTopLevelAIGsAndDefs(units);

  _refAIGs = _toplevelAIGs;
  _fsh.aigTransf().makeOrderedAIGGraphStack(_refAIGs);

  doFirstRefAIGPass();


}

bool AIGDefinitionIntroducer::apply(FormulaUnit* unit, FormulaUnit*& res)
{
  CALL("AIGDefinitionIntroducer::apply");
  NOT_IMPLEMENTED;
}


}

