/**
 * @file AIGDefinitionIntroducer.cpp
 * Implements class AIGDefinitionIntroducer.
 */

#include "Lib/SharedSet.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Flattening.hpp"
#include "PDUtils.hpp"
#include "SimplifyFalseTrue.hpp"

#include "AIGDefinitionIntroducer.hpp"

namespace Shell
{

////////////////////////////
// AIGDefinitionIntroducer
//

AIGDefinitionIntroducer::AIGDefinitionIntroducer(unsigned threshold)
 : _arwr(_fsh.aig())
{
  CALL("AIGDefinitionIntroducer::AIGDefinitionIntroducer");

  _namingRefCntThreshold = threshold;
  _mergeEquivDefs = false; //not implemented yet
}

/**
 * Add a definition into _defs and return true, or return false
 * if @c rhs already as a definition
 *
 * namingUnit may be zero, that means that the naming unit will be created lazily later
 */
bool AIGDefinitionIntroducer::addAIGName(AIGRef rhs, AIGRef nameAtom, FormulaUnit* namingUnit)
{
  CALL("AIGDefinitionIntroducer::addAIGDefinition");
  ASS(nameAtom.isAtom());
  ASS(!rhs.isPropConst());

  if(!_defs.insert(rhs, nameAtom)) {
    return false;
  }
  if(namingUnit) {
    ALWAYS(_defUnits.insert(rhs, namingUnit));
  }
  return true;
}

/** @c rhs must have a name, this will be returned. */
AIGRef AIGDefinitionIntroducer::getName(AIGRef rhs) const
{
  CALL("AIGDefinitionIntroducer::getName");
  ASS(hasName(rhs));

  return _defs.get(rhs);
}


bool AIGDefinitionIntroducer::scanDefinition(FormulaUnit* def)
{
  CALL("AIGDefinitionIntroducer::scanDefinition");

  Literal* lhs;

  AIGRef rhsAig;

  Literal* rhsLit; //valid only from pred equiv
  if(PDUtils::isPredicateEquivalence(def, lhs, rhsLit)) {
    rhsAig = _fsh.apply(rhsLit);
  }
  else {
    Formula* rhs;
    PDUtils::splitDefinition(def, lhs, rhs);
    rhsAig = _fsh.apply(rhs).second;
  }

  if(rhsAig.isPropConst()) {
    return false;
  }

  if(lhs->color()!=COLOR_TRANSPARENT) {
    return false;
  }

  AIGRef lhsAig = _fsh.apply(lhs);

  if(!rhsAig.polarity()) {
    rhsAig = rhsAig.neg();
    lhsAig = lhsAig.neg();
  }

  if(!addAIGName(rhsAig, lhsAig, def)) {
    //rhs is already defined
    AIGRef oldDefTgt;
    oldDefTgt = getName(rhsAig);
    if(_mergeEquivDefs) {
//      _equivs.insert(lhs, oldDefTgt);
      NOT_IMPLEMENTED;
    }
    return false;
  }

  _toplevelAIGs.push(rhsAig);
  return true;
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
      if(scanDefinition(fu)) {
	continue;
      }
    }

    Formula* form = fu->formula();
    AIGRef formAig = _fsh.apply(form).second;
    _toplevelAIGs.push(formAig);
  }
}

AIGDefinitionIntroducer::VarSet* AIGDefinitionIntroducer::getAtomVars(Literal* l)
{
  CALL("AIGDefinitionIntroducer::getAtomVars");

  static Stack<unsigned> vars;
  vars.reset();
  static VariableIterator vit;
  vit.reset(l);
  while(vit.hasNext()) {
    TermList vt = vit.next();
    unsigned var = vt.var();
    vars.push(var);
  }
  return VarSet::getFromIterator(Stack<unsigned>::Iterator(vars));
}

AIGDefinitionIntroducer::NodeInfo& AIGDefinitionIntroducer::getNodeInfo(AIGRef r)
{
  CALL("AIGDefinitionIntroducer::doFirstRefAIGPass");

  AIGRef rPos = r.getPositive();
  size_t idx = _aigIndexes.get(rPos);
  return _refAIGInfos[idx];
}

void AIGDefinitionIntroducer::doFirstRefAIGPass()
{
  CALL("AIGDefinitionIntroducer::doFirstRefAIGPass");

  ASS(_refAIGInfos.isEmpty());
  size_t aigCnt = _refAIGs.size();
  for(size_t i=0; i<aigCnt; ++i) {
    AIGRef r = _refAIGs[i];
    LOG("pp_aigdef_used_aigs","used at "<<i<<": "<<r.toInternalString());
    ASS(r.polarity());
    _aigIndexes.insert(r, i);

    _refAIGInfos.push(NodeInfo());
    NodeInfo& ni = _refAIGInfos.top();

    ni._directRefCnt = 0;
    ni._hasName = findName(r, ni._name);


    ni._hasQuant[0] = false;
    ni._hasQuant[1] = r.isQuantifier();

    if(r.isAtom()) {
      Literal* lit = r.getPositiveAtom();
      ni._freeVars = getAtomVars(lit);
      ni._clr = lit->color();
    }
    else if(r.isPropConst()) {
      ni._freeVars = VarSet::getEmpty();
      ni._clr = COLOR_TRANSPARENT;
    }
    else if(r.isConjunction()) {
      NodeInfo& pni1 = getNodeInfo(r.parent(0));
      NodeInfo& pni2 = getNodeInfo(r.parent(1));
      ni._freeVars = pni1._freeVars->getUnion(pni2._freeVars);
      ni._clr = ColorHelper::combine(pni1._clr, pni2._clr);
      if(ni._clr==COLOR_INVALID) {
	USER_ERROR("mixing colors in "+r.toString());
      }
    }
    else {
      ASS(r.isQuantifier());
      NodeInfo& pni = getNodeInfo(r.parent(0));
      VarSet* qVars = r.getQuantifierVars();
      ni._freeVars = pni._freeVars->subtract(qVars);
      ni._clr = pni._clr;
    }

    unsigned parCnt = r.parentCnt();
    for(unsigned pi = 0; pi<parCnt; ++pi) {
      AIGRef par = r.parent(pi);
      bool neg = !par.polarity();
      NodeInfo& pni = getNodeInfo(par);

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

/**
 * Return the aig at given index before names are introduced but after
 * the AIG compression.
 *
 * Can be called after the call to @c doFirstRefAIGPass returns.
 */
AIGRef AIGDefinitionIntroducer::getPreNamingAig(unsigned aigStackIdx)
{
  CALL("AIGDefinitionIntroducer::getPreNamingAig");

  return _refAIGs[aigStackIdx];
}

bool AIGDefinitionIntroducer::shouldIntroduceName(unsigned aigStackIdx)
{
  CALL("AIGDefinitionIntroducer::shouldIntroduceName");

  AIGRef a = getPreNamingAig(aigStackIdx);
  if(a.isPropConst() || a.isAtom()) {
    return false;
  }
  NodeInfo& ni = _refAIGInfos[aigStackIdx];

  if(!_namingRefCntThreshold || ni._formRefCnt<_namingRefCntThreshold) {
    return false;
  }
  if(hasName(a)) {
    return false;
  }
  return true;
}

Literal* AIGDefinitionIntroducer::getNameLiteral(unsigned aigStackIdx)
{
  CALL("AIGDefinitionIntroducer::getNameLiteral");

  AIGRef a = getPreNamingAig(aigStackIdx);
  const NodeInfo& ni = getNodeInfo(a);
  VarSet* freeVars = ni._freeVars;
  Formula* rhs = _fsh.aigToFormula(a);

  static TermStack args;
  args.reset();
  static Stack<unsigned> argSorts;
  argSorts.reset();

  if(!freeVars->isEmpty()) {
    static DHMap<unsigned,unsigned> varSorts;
    varSorts.reset();
    SortHelper::collectVariableSorts(rhs, varSorts); //careful!! this traverses the formula as tree, not as DAG, so may take exponential time!

    VarSet::Iterator vit(*freeVars);
    while(vit.hasNext()) {
      unsigned var = vit.next();
      args.push(TermList(var, false));
      argSorts.push(varSorts.get(var));
    }
  }

  unsigned arity = args.size();
  unsigned pred = env.signature->addFreshPredicate(arity, "sP","aig_name");
  Signature::Symbol* psym = env.signature->getPredicate(pred);
  psym->setType(PredicateType::makeType(arity, argSorts.begin(), Sorts::SRT_BOOL));
  if(ni._clr!=COLOR_TRANSPARENT) {
    psym->addColor(ni._clr);
  }

  Literal* res = Literal::create(pred, arity, true, false, args.begin());
  return res;
}

void AIGDefinitionIntroducer::introduceName(unsigned aigStackIdx)
{
  CALL("AIGDefinitionIntroducer::introduceName");

  AIGRef a = getPreNamingAig(aigStackIdx);
  NodeInfo& ni = _refAIGInfos[aigStackIdx];
  ASS(!ni._hasName);
  ASS(!hasName(a.getPositive()));

  ni._formRefCnt = 1;
  Literal* nameLit = getNameLiteral(aigStackIdx);
  ni._hasName = true;
  ni._name = _fsh.apply(nameLit);
  if(a.polarity()) {
    ALWAYS(addAIGName(a, ni._name, 0));
  }
  else {
    ALWAYS(addAIGName(a.neg(), ni._name.neg(), 0));
  }
}

void AIGDefinitionIntroducer::doSecondRefAIGPass()
{
  CALL("AIGDefinitionIntroducer::doSecondRefAIGPass");

  TopLevelStack::Iterator tlit(_toplevelAIGs);
  while(tlit.hasNext()) {
    AIGRef a = tlit.next();
    AIGRef aPos = a.getPositive();
    unsigned stackIdx = _aigIndexes.get(aPos);
    NodeInfo& ni = _refAIGInfos[stackIdx];
    ni._formRefCnt++;
    ni._inPol[a.polarity()] = true;
  }

  size_t aigCnt = _refAIGs.size();
  for(size_t i=aigCnt; i>0;) {
    i--;

    AIGRef r = _refAIGs[i];
    NodeInfo& ni = _refAIGInfos[i];

    if(ni._hasName) {
      ni._formRefCnt = 1;
    }
    if(shouldIntroduceName(i)) {
      introduceName(i);
    }

    unsigned parCnt = r.parentCnt();
    for(unsigned pi = 0; pi<parCnt; ++pi) {
      AIGRef par = r.parent(pi);
      bool neg = !par.polarity();
      AIGRef posPar = par.getPositive();
      unsigned parStackIdx = _aigIndexes.get(posPar);
      NodeInfo& pni = _refAIGInfos[parStackIdx];

      if(r.isQuantifier()) {
	pni._inQuant[!neg] = true;
      }

      pni._inQuant[0^neg] |= ni._inQuant[0];
      pni._inQuant[1^neg] |= ni._inQuant[1];

      pni._inPol[0^neg] |= ni._inPol[0];
      pni._inPol[1^neg] |= ni._inPol[1];

      pni._formRefCnt += ni._formRefCnt;
    }
  }
}

FormulaUnit* AIGDefinitionIntroducer::createNameUnit(AIGRef rhs, AIGRef atomName)
{
  CALL("AIGDefinitionIntroducer::createNameUnit");
  ASS(atomName.isAtom());
  ASS(!rhs.isAtom());
  ASS(!rhs.isPropConst());

  if(!atomName.polarity()) {
    atomName = atomName.neg();
    rhs = rhs.neg();
  }

  Formula* lhsForm = new AtomicFormula(atomName.getPositiveAtom());
  Formula* rhsForm = _fsh.aigToFormula(rhs);
  //TODO: weaken definition based on the way subformula occurrs
  Formula* equiv = new BinaryFormula(IFF, lhsForm, rhsForm);
  //by the behavior of getNameLiteral lhs contains all the free variables of rhs (but unlike rhs contains just one atom)
  Formula::VarList* vars = lhsForm->freeVariables();
  if(vars) {
    equiv = new QuantifiedFormula(FORALL, vars, equiv);
  }
  ASS_REP(equiv->freeVariables()->isEmpty(), *equiv);
  FormulaUnit* def = new FormulaUnit(equiv, new Inference(Inference::PREDICATE_DEFINITION), Unit::AXIOM);
  _newDefs.push(def);

  LOG_UNIT("pp_aigdef_intro", def);
  return def;
}

void AIGDefinitionIntroducer::doThirdRefAIGPass()
{
  CALL("AIGDefinitionIntroducer::doThirdRefAIGPass");

  size_t aigCnt = _refAIGs.size();
  for(size_t i=0; i<aigCnt; i++) {
    AIGRef r = _refAIGs[i];

    NodeInfo& ni = _refAIGInfos[i];

    AIGRewriter::PremiseSet* prems;
    AIGRef tgt = _arwr.lev1Deref(r, _defsSaturated, &prems);

    //if're not supposed to be naming, or if the tgt is prop constant or
    //an atom, we don't introduce name and just put the target into the map
    if(!ni._hasName || tgt.isPropConst() || tgt.isAtom()) {
      if(r!=tgt) {
	ALWAYS(_defsSaturated.insert(r, AIGRewriter::PremRef(tgt, prems)));
      }
      continue;
    }

    if(!_defUnits.find(r, ni._namingUnit)) {
      ni._namingUnit = createNameUnit(tgt, ni._name);
    }

    AIGRewriter::PremiseSet* selfNamingPrems = prems->getUnion(AIGRewriter::PremiseSet::getSingleton(i));
    ALWAYS(_defsSaturated.insert(r, AIGRewriter::PremRef(ni._name, selfNamingPrems)));
  }
}

void AIGDefinitionIntroducer::scan(UnitList* units)
{
  CALL("AIGDefinitionIntroducer::scan");

  collectTopLevelAIGsAndDefs(units);

  processTopLevelAIGs();
}

void AIGDefinitionIntroducer::processTopLevelAIGs()
{
  CALL("AIGDefinitionIntroducer::processTopLevelAIGs");

  _refAIGs.loadFromIterator( TopLevelStack::Iterator(_toplevelAIGs) );
  _fsh.aigTransf().makeOrderedAIGGraphStack(_refAIGs);

  doFirstRefAIGPass();
  doSecondRefAIGPass();
  doThirdRefAIGPass();
//  _defsSaturated.loadFromMap(_defs);
//  _fsh.aigTransf().saturateMap(_defsSaturated);
}

Inference* AIGDefinitionIntroducer::getInferenceFromPremIndexes(Unit* orig, AIGRewriter::PremiseSet* premIndexes)
{
  CALL("AIGDefinitionIntroducer::getInferenceFromPremIndexes");

  if(premIndexes->size()==0) {
    return new Inference1(Inference::DEFINITION_FOLDING, orig);
  }
  if(premIndexes->size()==1) {
    unsigned nmPremIdx = premIndexes->sval();
    Unit* nmPrem = _refAIGInfos[nmPremIdx]._namingUnit;
    ASS(nmPrem);
    return new Inference2(Inference::DEFINITION_FOLDING, nmPrem, orig);
  }



  UnitList* prems = 0;
  UnitList::push(orig, prems);
  AIGRewriter::PremiseSet::Iterator psit(*premIndexes);
  while(psit.hasNext()) {
    unsigned nmPremIdx = psit.next();
    Unit* nmPrem = _refAIGInfos[nmPremIdx]._namingUnit;
    UnitList::push(nmPrem, prems);
  }

  return new InferenceMany(Inference::DEFINITION_FOLDING, prems);
}

bool AIGDefinitionIntroducer::apply(FormulaUnit* unit, Unit*& res)
{
  CALL("AIGDefinitionIntroducer::apply(FormulaUnit*,Unit*&)");

  Formula* f0 = unit->formula();

  AIGRef f0Aig = _fsh.apply(f0).second;
  AIGRewriter::PremiseSet* premIndexes;
  AIGRef resAig = _arwr.lev0Deref(f0Aig, _defsSaturated, &premIndexes);
  if(f0Aig==resAig) {
    return false;
  }
  Formula* f = _fsh.aigToFormula(resAig);

  if(f->connective()==TRUE) {
    res = 0;
    LOG("pp_aigdef_apply","orig: " << (*unit) << endl << "  simplified to tautology");
    return true;
  }

  ASS_REP2(f->freeVariables()->isEmpty(), *f, *unit);

  //TODO add proper inferences
  Inference* inf = getInferenceFromPremIndexes(unit, premIndexes);
  res = new FormulaUnit(f, inf, unit->inputType());
  LOG("pp_aigdef_apply","orig: " << (*unit) << endl << "intr: " << (*res));
  ASS(!res->isClause());
  res = SimplifyFalseTrue().simplify(static_cast<FormulaUnit*>(res));
  res = Flattening::flatten(static_cast<FormulaUnit*>(res));
  return true;
}

///**
// * Introduce definitions into a formula and return modifier formuls.
// * The introducedDefinitions add to the @c introducedDefs list.
// */
//Formula* AIGDefinitionIntroducer::apply(Formula* f0, UnitList*& introducedDefs)
//{
//  CALL("AIGDefinitionIntroducer::apply(Formula*,UnitList*&)");
//  ASS(_newDefs.isEmpty());
//
//  AIGRef f0Aig = _fsh.apply(f0).second;
//
//  _toplevelAIGs.push(f0Aig);
//
//  processTopLevelAIGs();
//
//  AIGRef resAig = AIGTransformer::lev0Deref(f0Aig, _defs);
//  if(f0Aig==resAig) {
//    return f0;
//  }
////  LOGV("bug",f0Aig);
////  LOGV("bug",resAig);
//  Formula* f = _fsh.aigToFormula(resAig);
//
//
//  Stack<FormulaUnit*>::Iterator uit(_newDefs);
//  while(uit.hasNext()) {
//    FormulaUnit* def0 = uit.next();
//    Unit* def;
//    if(!apply(def0, def)) {
//      def = def0;
//    }
//    UnitList::push(def, introducedDefs);
//  }
//
//  return f;
//}

UnitList* AIGDefinitionIntroducer::getIntroducedFormulas()
{
  CALL("AIGDefinitionIntroducer::getIntroducedFormulas");
  LOG("pp_aigdef_apply","processing definitions");

  UnitList* res = 0;

  Stack<FormulaUnit*>::Iterator uit(_newDefs);
  while(uit.hasNext()) {
    FormulaUnit* def0 = uit.next();
    Unit* def;
    if(!apply(def0, def)) {
      def = def0;
    }
    UnitList::push(def, res);
  }
  return res;
}

void AIGDefinitionIntroducer::updateModifiedProblem(Problem& prb)
{
  CALL("AIGDefinitionIntroducer::updateModifiedProblem");

  prb.invalidateProperty();
}

}
