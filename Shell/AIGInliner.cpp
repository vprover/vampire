/**
 * @file AIGInliner.cpp
 * Implements class AIGInliner.
 */

#include <climits>

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/MapToLIFO.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"

#include "Options.hpp"
#include "PDUtils.hpp"
#include "SimplifyFalseTrue.hpp"

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
    if(!PDUtils::hasDefinitionShape(u)) {
      continue;
    }
    Literal* peLit1;
    Literal* peLit2;
    if(PDUtils::isPredicateEquivalence(fu, peLit1, peLit2)) {
      //TODO:do something smarter
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

AIGDefinitionIntroducer::AIGDefinitionIntroducer(const Options& opts)
{
  CALL("AIGDefinitionIntroducer::AIGDefinitionIntroducer");

  _eprPreserving = opts.eprPreservingNaming();
  _namingRefCntThreshold = 4; //TODO: add option
  _mergeEquivDefs = false; //not implemented yet
}

void AIGDefinitionIntroducer::scanDefinition(FormulaUnit* def)
{
  CALL("AIGDefinitionIntroducer::scanDefinition");

  Literal* lhs;
  Formula* rhs;
  PDUtils::splitDefinition(def, lhs, rhs);

  AIGRef rhsAig = _fsh.apply(rhs).second;
  AIGRef lhsAig = _fsh.apply(lhs);

  if(!rhsAig.polarity()) {
    rhsAig = rhsAig.neg();
    lhsAig = lhsAig.neg();
  }

  if(!_defs.insert(rhsAig, lhsAig)) {
    //rhs is already defined
    AIGRef oldDefTgt;
    ALWAYS(_defs.find(rhsAig, oldDefTgt));
    if(_mergeEquivDefs) {
//      _equivs.insert(lhs, oldDefTgt);
      NOT_IMPLEMENTED;
    }
    return;
  }
  ALWAYS(_defUnits.insert(rhsAig,def));

  _toplevelAIGs.push(make_pair(rhsAig,def));
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
    _toplevelAIGs.push(make_pair(formAig,fu));
  }
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
    ni._hasName = _defs.find(r, ni._name);

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
  if(_defs.find(a)) {
    return false;
  }
  return true;
}

Literal* AIGDefinitionIntroducer::getNameLiteral(unsigned aigStackIdx)
{
  CALL("AIGDefinitionIntroducer::getNameLiteral");

  AIGRef a = getPreNamingAig(aigStackIdx);
  Formula* rhs = _fsh.aigToFormula(a);
  Formula::VarList* freeVars = rhs->freeVariables(); //careful!! this traverses the formula as tree, not as DAG, so may take exponential time!

  static DHMap<unsigned,unsigned> varSorts;
  varSorts.reset();
  SortHelper::collectVariableSorts(rhs, varSorts); //careful!! this traverses the formula as tree, not as DAG, so may take exponential time!

  static TermStack args;
  args.reset();
  static Stack<unsigned> argSorts;
  argSorts.reset();
  while(freeVars) {
    unsigned var = Formula::VarList::pop(freeVars);
    args.push(TermList(var, false));
    argSorts.push(varSorts.get(var));
  }

  unsigned arity = args.size();
  unsigned pred = env.signature->addFreshPredicate(arity, "sP","aig_name");
  env.signature->getPredicate(pred)->setType(PredicateType::makeType(arity, argSorts.begin(), Sorts::SRT_BOOL));

  Literal* res = Literal::create(pred, arity, true, false, args.begin());
  return res;
}

void AIGDefinitionIntroducer::introduceName(unsigned aigStackIdx)
{
  CALL("AIGDefinitionIntroducer::introduceName");

  AIGRef a = getPreNamingAig(aigStackIdx);
  NodeInfo& ni = _refAIGInfos[aigStackIdx];
  ASS(!ni._hasName);
  ASS(!_defs.find(a.getPositive()));

  ni._formRefCnt = 1;
  Literal* nameLit = getNameLiteral(aigStackIdx);
  ni._hasName = true;
  ni._name = _fsh.apply(nameLit);
  if(a.polarity()) {
    ALWAYS(_defs.insert(a, ni._name));
  }
  else {
    ALWAYS(_defs.insert(a.neg(), ni._name.neg()));
  }

  Formula* lhs = new AtomicFormula(nameLit);
  Formula* rhs = _fsh.aigToFormula(a);
  //TODO: weaken definition based on the way subforula occurrs
  Formula* equiv = new BinaryFormula(IFF, lhs, rhs);
  Formula::VarList* vars = equiv->freeVariables(); //careful!! this traverses the formula as tree, not as DAG, so may take exponential time!
  if(vars) {
    equiv = new QuantifiedFormula(FORALL, vars, equiv);
  }
  FormulaUnit* def = new FormulaUnit(equiv, new Inference(Inference::PREDICATE_DEFINITION), Unit::AXIOM);
  ALWAYS(_defUnits.insert(a, def));
  _newDefs.push(def);

  LOG_UNIT("pp_aigdef_intro", def);
}

void AIGDefinitionIntroducer::doSecondRefAIGPass()
{
  CALL("AIGDefinitionIntroducer::doSecondRefAIGPass");

  TopLevelStack::Iterator tlit(_toplevelAIGs);
  while(tlit.hasNext()) {
    AIGRef a = tlit.next().first;
    bool neg = !a.polarity();
    AIGRef aPos = neg ? a.neg() : a;
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
      AIGRef posPar = neg ? par.neg() : par;
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

void AIGDefinitionIntroducer::scan(UnitList* units)
{
  CALL("AIGDefinitionIntroducer::scan");

  collectTopLevelAIGsAndDefs(units);

  _refAIGs.loadFromIterator( getMappingIterator(TopLevelStack::Iterator(_toplevelAIGs), GetFirstOfPair<TopLevelPair>()) );
  _fsh.aigTransf().makeOrderedAIGGraphStack(_refAIGs);

  doFirstRefAIGPass();
  doSecondRefAIGPass();
  _fsh.aigTransf().saturateMap(_defs);
}
//
//struct AIGDefinitionIntroducer::DefIntroRewriter : public FormulaTransformer
//{
//  DefIntroRewriter(AIGDefinitionIntroducer& parent) : _parent(parent), _fsh(_parent._fsh) {}
//
//  virtual bool preApply(Formula*& f)
//  {
//    CALL("AIGDefinitionIntroducer::DefIntroRewriter::postApply");
//
//    if(f->connective()==LITERAL) { return true; }
//
//    LOG("pp_aigdef_apply_subform", "checking: "<<(*f));
//    AIGFormulaSharer::ARes ares = _fsh.apply(f);
////    f = ares.first;
//    AIGRef a = ares.second;
//    LOG("pp_aigdef_apply_subform", "  aig: "<<a.toInternalString());
//
//    bool neg = !a.polarity();
//    if(neg) {
//      a = a.neg();
//    }
//    unsigned refStackIdx = _parent._aigIndexes.get(a);
//    NodeInfo& ni = _parent._refAIGInfos[refStackIdx];
//    if(ni._hasName) {
//      //we replace the formula by definition
//      LOG("pp_aigdef_apply_subform", "found name: "<<ni._name);
//      AIGRef nameAig = ni._name;
//      if(neg) {
//	nameAig = nameAig.neg();
//      }
//      f = _fsh.aigToFormula(nameAig);
//      return false;
//    }
//    return true;
//  }
//private:
//  AIGDefinitionIntroducer& _parent;
//  AIGFormulaSharer& _fsh;
//};

bool AIGDefinitionIntroducer::apply(FormulaUnit* unit, Unit*& res)
{
  CALL("AIGDefinitionIntroducer::apply(FormulaUnit*,Unit*&)");

//  DefIntroRewriter rwr(*this);
  Formula* f0 = unit->formula();
//  Formula* f = rwr.transform(f0);

  AIGRef f0Aig = _fsh.apply(f0).second;
  AIGRef resAig;
  bool neg = !f0Aig.polarity();
  if(neg) {
    f0Aig = f0Aig.neg();
  }
  if(!_defs.find(f0Aig, resAig)) {
    return false;
  }
  ASS_NEQ(f0Aig, resAig);
  if(neg) {
    resAig = resAig.neg();
  }
  Formula* f = _fsh.aigToFormula(resAig);

  if(f->connective()==TRUE) {
    res = 0;
    LOG("pp_aigdef_apply","orig: " << (*unit) << endl << "  simplified to tautology");
    return true;
  }
//  if(f==f0) {
//    return false;
//  }
  //TODO add proper inferences
  res = new FormulaUnit(f, new Inference1(Inference::DEFINITION_FOLDING,unit), unit->inputType());
  LOG("pp_aigdef_apply","orig: " << (*unit) << endl << "intr: " << (*res));
  ASS(!res->isClause());
  res = SimplifyFalseTrue().simplify(static_cast<FormulaUnit*>(res));
  return true;
}

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

}

