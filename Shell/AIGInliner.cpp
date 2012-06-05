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

#include "Kernel/ColorHelper.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/LiteralComparators.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"

#include "Indexing/LiteralSubstitutionTree.hpp"

#include "AIGSubst.hpp"
#include "Flattening.hpp"
#include "Options.hpp"
#include "PDUtils.hpp"
#include "Rectify.hpp"
#include "SimplifyFalseTrue.hpp"

#include "AIGInliner.hpp"

namespace Shell
{

AIGInliner::EquivInfo::EquivInfo(Literal* lhs, Formula* rhs, FormulaUnit* unit)
: lhs(lhs), rhs(rhs), unit(unit)
{
  CALL("AIGInliner::EquivInfo::EquivInfo");

  posLhs = Literal::positiveLiteral(lhs);
  active = true;
}

/**
 * Compare literals for the purpose of @c tryGetEquiv()
 */
bool AIGInliner::EquivInfo::litIsLess(Literal* l1, Literal* l2)
{
  CALL("AIGInliner::EquivInfo::litIsLess");
  bool l1Protected = env.signature->getPredicate(l1->functor())->protectedSymbol();
  bool l2Protected = env.signature->getPredicate(l2->functor())->protectedSymbol();
  if(l1Protected!=l2Protected) {
    return l1Protected;
  }
  if(l1->functor()!=l2->functor()) {
    return l1->functor()<l2->functor();
  }
  return LiteralComparators::NormalizedLinearComparatorByWeight<true>().compare(l1, l2)==LESS;
}

/**
 * Attempt to get an equivalence with atom on the lhs from @c fu,
 * if unsuccessful, return 0.
 *
 * If both sides of an equivalence can become lhs, we pick the one with
 * larger predicate number. If equivalence is between atoms of the same
 * predicate, we use some other deterministic ordering to pick.
 */
AIGInliner::EquivInfo* AIGInliner::EquivInfo::tryGetEquiv(FormulaUnit* fu)
{
  CALL("AIGInliner::EquivInfo::tryGetEquiv");

  Formula* f = fu->formula();
  Formula::VarList* qvars = 0;
  if(f->connective()==FORALL) {
    qvars = f->vars();
    f = f->qarg();
  }

  if(f->connective()==LITERAL) {
    Literal* lhs = f->literal();
    if(env.signature->getPredicate(lhs->functor())->protectedSymbol()) {
      return 0;
    }
    return new EquivInfo(lhs, Formula::trueFormula(), fu);
  }
  if(f->connective()!=IFF) {
    return 0;
  }
  Formula* c1 = f->left();
  Formula* c2 = f->right();
  if(c1->connective()!=LITERAL) {
    swap(c1,c2);
  }
  else if(c2->connective()==LITERAL) {
    Literal* l1 = c1->literal();
    Literal* l2 = c2->literal();
    bool l1DH = PDUtils::isDefinitionHead(l1);
    bool l2DH = PDUtils::isDefinitionHead(l2);
    if(l1DH==l2DH) {
      if(l1->functor()==l2->functor()) {
	if(l1==l2) { return 0; }
	if(l1==Literal::complementaryLiteral(l2)) { return 0; }
      }
      bool less = litIsLess(l1, l2);
      if(less) {
	swap(c1, c2);
      }
    }
    else if(l2DH) {
      swap(c1, c2);
    }
  }

  if(c1->connective()!=LITERAL) {
    return 0;
  }
  Literal* lhs = c1->literal();
  if(env.signature->getPredicate(lhs->functor())->protectedSymbol()) {
    return 0;
  }


  Formula* rhs = c2;

  if(env.colorUsed && lhs->color()==COLOR_TRANSPARENT && rhs->getColor()!=COLOR_TRANSPARENT) {
    LOG("bug", "color introducing definition ignored: "<<(*fu));
    return 0;
  }

  Formula::VarList* lhsVars = c1->freeVariables();

  static Stack<unsigned> qVarStack;
  static Stack<unsigned> lhsVarStack;
  qVarStack.reset();
  qVarStack.loadFromIterator(Formula::VarList::Iterator(qvars));
  std::sort(qVarStack.begin(), qVarStack.end());
  lhsVarStack.reset();
  lhsVarStack.loadFromIterator(Formula::VarList::DestructiveIterator(lhsVars));
  std::sort(lhsVarStack.begin(), lhsVarStack.end());

  if(qVarStack!=lhsVarStack) {
    return 0;
  }

  return new EquivInfo(lhs, rhs, fu);
}

AIGInliner::AIGInliner()
 : _aig(_fsh.aig()), _atr(_aig), _acompr(_aig)
{
  CALL("AIGInliner::AIGInliner");

  _onlySingleAtomPreds = false;

  _lhsIdx = new LiteralSubstitutionTree();
}

AIGInliner::~AIGInliner()
{
  CALL("AIGInliner::~AIGInliner");

  delete _lhsIdx;

  while(_eqInfos.isNonEmpty()) {
    delete _eqInfos.pop();
  }
}

bool AIGInliner::addInfo(EquivInfo* inf)
{
  CALL("AIGInliner::addInfo");

  if(_lhsIdx->getUnificationCount(inf->posLhs, false)!=0) {
    //TODO: one day try to do something smarter
    delete inf;
    return false;
  }

  AIGRef rhsAig = _fsh.apply(inf->rhs).second;
  if(inf->lhs->isNegative()) {
    rhsAig = rhsAig.neg();
  }
  rhsAig = _acompr.compress(rhsAig);
  inf->activeAIGRhs = rhsAig;

  //now we know we have a definition we'll use, so we insert it into structures

  _eqInfos.push(inf);

  Literal* idxLhs = inf->posLhs;
  _lhsIdx->insert(idxLhs, 0);
  _defs.insert(idxLhs, inf);
  _unit2def.insert(inf->unit, inf);

  LOG("pp_aiginl_equiv","equivalence for inlining: "<<(*inf->posLhs)<<" <=> "<<rhsAig);
  return true;
}

void AIGInliner::addRelevant(AIGRef a)
{
  CALL("AIGInliner::addRelevant(AIGRef)");

  _relevantAigs.push(a);
#if VDEBUG
  _relevantAigsSet.insert(a);
#endif
}

void AIGInliner::addRelevant(Formula* f)
{
  CALL("AIGInliner::addRelevant(Formula*)");

  addRelevant(_fsh.apply(f).second);
}

void AIGInliner::collectDefinitionsAndRelevant(UnitList* units)
{
  CALL("AIGInliner::collectDefinitionsAndRelevant");

  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if(u->isClause()) {
      addRelevant(_fsh.getAIG(static_cast<Clause*>(u)));
      continue;
    }
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    EquivInfo* inf = EquivInfo::tryGetEquiv(fu);
    Formula* relevantForm;
    if(inf && addInfo(inf)) {
      relevantForm = inf->rhs;
    }
    else {
      relevantForm = fu->formula();
    }
    addRelevant(relevantForm);
  }
}

void AIGInliner::updateModifiedProblem(Problem& prb)
{
  CALL("AIGInliner::updateModifiedProblem");

  prb.invalidateByRemoval();
}

/**
 * Try expanding atom using definitions
 *
 * @param atom Atom to be expanded. Must be an atom aig with positive polarity.
 */
bool AIGInliner::tryExpandAtom(AIGRef atom, PremRef& res)
{
  CALL("AIGInliner::tryExpandAtom");
  ASS(atom.isAtom());
  ASS(atom.polarity());

  Literal* lit = atom.getPositiveAtom();
  SLQueryResultIterator defIt = _lhsIdx->getGeneralizations(lit, false, false);

  if(!defIt.hasNext()) {
    return false;
  }

  SLQueryResult idxRes = defIt.next();

//  if(defIt.hasNext()) {
//    defIt = _lhsIdx->getGeneralizations(lit, false, false);
//    LOGV("bug", *lit);
//    while(defIt.hasNext()) {
//      LOGV("bug", *defIt.next().literal);
//    }
//  }
  ASS(!defIt.hasNext()); //we made sure there is always only one way to inline

  Literal* defLhs = idxRes.literal;

  EquivInfo* def = _defs.get(defLhs);
  unsigned premNum = _atr.getPremiseNum(def->unit);
  res.second = PremSet::getSingleton(premNum);

  AIGRef defRhs = def->activeAIGRhs;
  if(lit==defLhs) {
    res.first = defRhs;
    return true;
  }

  typedef DHMap<unsigned,TermList> BindingMap;
  static BindingMap binding;
  binding.reset();
  MatchingUtils::MapRefBinder<BindingMap> binder(binding);

  ALWAYS(MatchingUtils::match(defLhs, lit, false, binder));

  SubstHelper::MapApplicator<BindingMap> applicator(&binding);

  res.first = AIGSubst(_aig).apply(applicator, defRhs);
  LOG("pp_aiginl_instance","instantiated AIG definition"<<endl<<
      "  src: "<<atom<<endl<<
      "  lhs: "<<(*defLhs)<<endl<<
      "  rhs: "<<defRhs<<endl<<
      "  tgt: "<<res.first<<endl
      );
  return true;
}

/**
 * Units must not contain predicate eqivalences
 */
void AIGInliner::scan(UnitList* units)
{
  CALL("AIGInliner::scan");

//  scanOccurrences(units);

  FormulaStack lhsForms;
  FormulaStack rhsForms;
  Stack<FormulaUnit*> defUnits;

  PremRefMap atomMap;

  collectDefinitionsAndRelevant(units);

  AIGInsideOutPosIterator ait;
  ait.reset();
  ait.addManyToTraversal(Stack<AIGRef>::Iterator(_relevantAigs));

  while(ait.hasNext()) {
    AIGRef a = ait.next();
    if(!a.isAtom()) {
      continue;
    }
    ASS(a.polarity());
    PremRef tgt;
    if(!tryExpandAtom(a, tgt)) {
      continue;
    }
    ALWAYS(atomMap.insert(a, tgt));
    ait.addToTraversal(tgt.first);
  }

  _inlMap.loadFromMap(atomMap);

//  TRACE("bug",
//      AIGTransformer::RefMap::Iterator mit(_inlMap);
//      while(mit.hasNext()) {
//	AIGRef src, tgt;
//	mit.next(src, tgt);
//	tout << "-inl---" << endl;
//	tout << "  src: " << src << endl;
//	tout << "  tgt: " << tgt << endl;
//      }
//  );


  _atr.saturateMap(_inlMap);

//  TRACE("bug",
//      AIGTransformer::RefMap::Iterator mit(_inlMap);
//      while(mit.hasNext()) {
//	AIGRef src, tgt;
//	mit.next(src, tgt);
//	tout << "-inl-sat--" << endl;
//	tout << "  src: " << src << endl;
//	tout << "  tgt: " << tgt << endl;
//	tout << "  srcI: " << src.toInternalString() << endl;
//	tout << "  tgtI: " << tgt.toInternalString() << endl;
//      }
//  );



  ait.reset();

  Stack<AIGRef>::Iterator baseAigIt(_relevantAigs);
  while(baseAigIt.hasNext()) {
    AIGRef baseAig = baseAigIt.next();
    AIGRef inlAig = AIGRewriter::lev0Deref(baseAig, _inlMap, 0);
//    LOGV("bug",baseAig);
//    LOGV("bug",inlAig);
//    LOGV("bug",inlAig.toInternalString());
    ait.addToTraversal(inlAig);
  }

  _acompr.populateBDDCompressingMap(ait, _simplMap);

//  LOGV("bug", _simplMap.size());
//  TRACE("bug",
//      AIGTransformer::RefMap::Iterator mit(_simplMap);
//      while(mit.hasNext()) {
//	AIGRef src, tgt;
//	mit.next(src, tgt);
//	tout << "----" << endl;
//	tout << "  src: " << src << endl;
//	tout << "  tgt: " << tgt << endl;
//	tout << "  srcI: " << src.toInternalString() << endl;
//	tout << "  tgtI: " << tgt.toInternalString() << endl;
//      }
//  );
}

AIGRef AIGInliner::apply(AIGRef a, PremSet*& prems)
{
  CALL("AIGInliner::apply(AIGRef)");

  AIGRef inl = AIGRewriter::lev0Deref(a, _inlMap, &prems);
  AIGRef res = AIGTransformer::lev0Deref(inl, _simplMap);
  COND_LOG("pp_aiginl_aig", a!=res, "inlining aig transformation:"<<endl
      <<"  src: "<<a<<endl
      <<"  inl: "<<inl<<endl
      <<"  tgt: "<<res<<endl
      <<"  tSm: "<<_acompr.compress(res)<<endl
      <<"  srcI: "<<a.toInternalString()<<endl
      <<"  inlI: "<<inl.toInternalString()<<endl
      <<"  tgtI: "<<res.toInternalString()
  );
//  COND_LOG("bug", res!=_acompr.compress(res),
//      "missed simplification in aig inlining:"<<endl
//            <<"  src: "<<a<<endl
//            <<"  inl: "<<inl<<endl
//            <<"  tgt: "<<res<<endl
//            <<"  tSm: "<<_acompr.compress(res)<<endl
//            <<"  srcI: "<<a.toInternalString()<<endl
//            <<"  inlI: "<<inl.toInternalString()<<endl
//            <<"  tgtI: "<<res.toInternalString()
//      );

  ASS_REP(_relevantAigsSet.contains(a), a);

  return res;
}

Formula* AIGInliner::apply(Formula* f, PremSet*& prems)
{
  CALL("AIGInliner::apply(Formula*)");

  AIGRef a = _fsh.apply(f).second;
  AIGRef tgt = apply(a, prems);
  if(tgt==a) {
    return f;
  }
  return _fsh.aigToFormula(tgt);
}

bool AIGInliner::apply(FormulaUnit* unit, Unit*& res)
{
  CALL("AIGInliner::apply(FormulaUnit*,FormulaUnit*&)");
  LOG_UNIT("pp_aiginl_unit_args", unit);

  Formula* f;

  PremSet* prems;

  EquivInfo* einf;
  if(_unit2def.find(unit, einf)) {
    Formula* newRhs = apply(einf->rhs, prems);
    if(newRhs==einf->rhs) {
      return false;
    }
    Formula* lhs = new AtomicFormula(einf->lhs);
    Formula::VarList* qvars = lhs->freeVariables();
    if(newRhs->connective()==TRUE) {
      f = lhs;
    }
    else if(newRhs->connective()==FALSE) {
      f = new AtomicFormula(Literal::complementaryLiteral(lhs->literal()));
    }
    else {
      f = new BinaryFormula(IFF, lhs, newRhs);
    }
    if(qvars) {
      f = new QuantifiedFormula(FORALL, qvars, f);
    }
  }
  else {
    f = apply(unit->formula(), prems);
    if(f->connective()==TRUE) {
      res = 0;
      return true;
    }
    if(f==unit->formula()) {
      return false;
    }
  }

  UnitList* premLst = 0;
  PremSet::Iterator premNumIt(*prems);
  while(premNumIt.hasNext()) {
    unsigned premNum = premNumIt.next();
    Unit* prem = _atr.getPremiseUnit(premNum);
    UnitList::push(prem, premLst);
  }
  UnitList::push(unit, premLst);

  //TODO: collect proper inferences
  Inference* inf = new InferenceMany(Inference::PREDICATE_DEFINITION_UNFOLDING, premLst);
  FormulaUnit* res0 = new FormulaUnit(f, inf, Unit::getInputType(premLst));

  res0 = Flattening::flatten(res0);
  res = Rectify::rectify(res0);

  LOG_SIMPL("pp_aiginl_unit", unit, res);

  return true;
}


}

