/**
 * @file EPRSkolem.cpp
 * Implements class EPRSkolem.
 */

#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/MultiCounter.hpp"
#include "Lib/ScopedLet.hpp"
#include "Lib/StringUtils.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaTransformer.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Flattening.hpp"
#include "PDUtils.hpp"
#include "Skolem.hpp"
#include "Statistics.hpp"
#include "VarManager.hpp"

#include "EPRSkolem.hpp"

namespace Shell
{

//////////////////////////////////
// EPRSkolem::ConstantSkolemizer
//

class EPRSkolem::ConstantSkolemizer : private PolarityAwareFormulaTransformer
{
public:
  ConstantSkolemizer(bool trace=false) : _trace(trace) {}

  FormulaUnit* transform(FormulaUnit* f);
  bool transform(UnitList*& units);

  Formula* transform(Formula* f)
  {
    _extraQuantifiers = false;
    return PolarityAwareFormulaTransformer::transform(f,1);
  }

  using PolarityAwareFormulaTransformer::apply;

  TermList apply(unsigned var)
  {
    TermList res;
    if(!_binding.find(var, res)) {
      return TermList(var,false);
    }
    return res;
  }

protected:
  Formula* applyLiteral(Formula* f);
  Formula* applyQuantified(Formula* f);
private:
  bool _trace;

  bool _extraQuantifiers;

  typedef DHMap<unsigned,TermList> BindingMap;
  BindingMap _binding;

  Stack<unsigned> _introducedSkolemFuns;
};

bool EPRSkolem::ConstantSkolemizer::transform(UnitList*& units)
{
  CALL("EPRSkolem::ConstantSkolemizer::transform(UnitList*&)");

  bool modified = false;
  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if(u->isClause()) {
      continue;
    }
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    FormulaUnit* newUnit = transform(fu);
    if(fu==newUnit) {
      continue;
    }
    uit.replace(newUnit);
    modified = true;
  }
  return modified;
}

FormulaUnit* EPRSkolem::ConstantSkolemizer::transform(FormulaUnit* fu)
{
  CALL("EPRSkolem::ConstantSkolemizer::transform(FormulaUnit*)");
  LOG_UNIT("pp_esk_cs_args", fu);

  ASS(_introducedSkolemFuns.isEmpty());
  Formula* form = fu->formula();
  Formula* newForm = transform(form);
  if(form==newForm) {
    return fu;
  }
  Inference* inf = new Inference1(Inference::SKOLEMIZE, fu);
  FormulaUnit* res = new FormulaUnit(newForm, inf, fu->inputType());
  ASS(_introducedSkolemFuns.isNonEmpty());
  while(_introducedSkolemFuns.isNonEmpty()) {
    unsigned fn = _introducedSkolemFuns.pop();
    InferenceStore::instance()->recordIntroducedSymbol(res, true, fn);
  }

  LOG("pp_esk","Constant skolemizer:\n  from: " << (*fu) << "\n  to:   " << (*res));

  return res;
}

Formula* EPRSkolem::ConstantSkolemizer::applyLiteral(Formula* f)
{
  CALL("EPRSkolem::ConstantSkolemizer::applyLiteral");

  Literal* lit = f->literal();

  Literal* newLit = SubstHelper::apply(lit, *this);
  if(lit==newLit) {
    return f;
  }

  return new AtomicFormula(newLit);
}

Formula* EPRSkolem::ConstantSkolemizer::applyQuantified(Formula* f)
{
  CALL("EPRSkolem::ConstantSkolemizer::applyQuantified");
  ASS(f->connective()==FORALL || f->connective()==EXISTS);
  ASS(f->vars());

  if(polarity()==0 || _extraQuantifiers) {
    return PolarityAwareFormulaTransformer::applyQuantified(f);
  }

  bool toBeSkolemized = (f->connective()==EXISTS) == (polarity()==1);
  if(!toBeSkolemized) {
    ScopedLet<bool> eqLet(_extraQuantifiers, true);
    return PolarityAwareFormulaTransformer::applyQuantified(f);
  }

  Formula::VarList::Iterator vit(f->vars());
  while(vit.hasNext()) {
    unsigned var = vit.next();
    unsigned skFunRangeSort = getVarSort(var);
    unsigned skFun = Skolem::addSkolemFunction(0, 0, skFunRangeSort, var);
    _introducedSkolemFuns.push(skFun);

    TermList skTerm = TermList( Term::createConstant(skFun) );
    _binding.insert(var, skTerm);
  }

  Formula* inner = apply(f->qarg());

  Formula::VarList::Iterator vit2(f->vars());
  while(vit2.hasNext()) {
    unsigned var = vit2.next();
    _binding.remove(var);
  }

  return inner;
}


//////////////////////////
// EPRSkolem::Applicator
//

class EPRSkolem::Applicator : private PolarityAwareFormulaTransformer
{
public:
  Applicator(EPRSkolem& parent, Literal* lhs, int topPolarity)
  : _skUnits(0), _lhs(lhs), _topPolarity(topPolarity), _parent(parent)
  {
    ASS(topPolarity==1 || topPolarity==-1);

    unsigned hdr = _lhs->header();
    if(_topPolarity==-1) {
      hdr ^= 1;
    }
    LiteralList* instList = _parent._insts.keyVals(hdr);
    _lhsInstances.loadFromIterator(LiteralList::Iterator(instList));
    makeUnique(_lhsInstances);

    unsigned lhsArity = _lhs->arity();
    for(unsigned i=0; i<lhsArity; i++) {
      unsigned var = _lhs->nthArgument(i)->var();
      ALWAYS(_varLhsIndexes.insert(var, i));
    }

  }

  bool hasInstances() const { return _lhsInstances.isNonEmpty(); }

  Formula* transform(Formula* f)
  {
    CALL("EPRSkolem::Applicator::transform");
    _extraQuantifiers = false;
    _universalVars.reset();

    Formula* res = PolarityAwareFormulaTransformer::transform(f, _topPolarity);
    return Flattening::flatten(res);
  }

  UnitList* _skUnits;
protected:
  virtual Formula* applyLiteral(Formula* f);
  virtual Formula* applyQuantified(Formula* f);

private:
  Literal* getSkolemLiteral(unsigned var);

  void generateSKUnit(Literal* inst, unsigned pred, unsigned var, string nameSuffix);

  void propagateInstancesToLiteral(Literal* lit, bool negated);

  Literal* _lhs;
  /** 1 means we're handling implication (lhs => f) */
  int _topPolarity;

  Stack<Literal*> _lhsInstances;

  DHMap<pair<Literal*,unsigned>,TermList> _skolemFns;

  DHMap<unsigned,unsigned> _varLhsIndexes;

  DHSet<unsigned> _universalVars;

  bool _extraQuantifiers;
  EPRSkolem& _parent;
};

/**
 * Here we don't modify the formula, just ensure we keep track of instances
 * of dependent EPR violating predicates that appear in the transformed formula
 */
Formula* EPRSkolem::Applicator::applyLiteral(Formula* f)
{
  CALL("EPRSkolem::Applicator::applyLiteral");

  Literal* l = f->literal();
  switch(polarity()) {
  case 1:
    propagateInstancesToLiteral(l, false);
    break;
  case -1:
    propagateInstancesToLiteral(l, true);
    break;
  case 0:
    propagateInstancesToLiteral(l, false);
    propagateInstancesToLiteral(l, true);
    break;
  default:
    ASSERTION_VIOLATION;
  }

  return f;
}

void EPRSkolem::Applicator::propagateInstancesToLiteral(Literal* lit, bool negated)
{
  CALL("EPRSkolem::Applicator::propagateInstancesToLiteral");
  LOG("pp_esk","Propagating instances to literal: " << (*lit));

  unsigned hdr = lit->header() ^ (negated ? 1 : 0);
  if(!_parent._inlinedHeaders.find(hdr)) {
    return;
  }

  if(lit->ground()) {
    _parent.processLiteralHeader(lit, hdr);
    return;
  }

  static Stack<TermList> args;
  LiteralStack::Iterator instIt(_lhsInstances);
  while(instIt.hasNext()) {
    Literal* inst = instIt.next();

    args.reset();

    for(TermList* lArg = lit->args(); !lArg->isEmpty(); lArg = lArg->next()) {
      if(lArg->isTerm()) {
	if(!lArg->term()->ground()) {
	  //we have a non-constant function, so the problem isn't EPR.
	  //this means we actually don't need to bother so much and we
	  //just disable the definition of lit by passing a non-ground
	  //instance
	  _parent.processLiteralHeader(lit, hdr);
	  return;
	}
	args.push(*lArg);
	continue;
      }
      unsigned lVar = lArg->var();
      unsigned lhsIdx;
      TermList argInst;
      if(_varLhsIndexes.find(lVar, lhsIdx)) {
	argInst = *inst->nthArgument(lhsIdx);
      }
      else if(_universalVars.contains(lVar)) {
	  ASS(!_skolemFns.find(make_pair(inst, lVar)));
	  //this will disable EPR skolemization for the predicate header hdr
	  _parent.processLiteralHeader(lit, hdr);
	  return;
      }
      else {
	ASS_REP2(_skolemFns.find(make_pair(inst, lVar)), inst->toString(), lVar);
	argInst = _skolemFns.get(make_pair(inst, lVar));
      }
      args.push(argInst);
    }
    ASS_EQ(args.size(), lit->arity());

    Literal* litInst = Literal::create(lit, args.begin());
    ASS(litInst->ground());
    _parent.processLiteralHeader(litInst, hdr);
  }
}

void EPRSkolem::Applicator::generateSKUnit(Literal* inst, unsigned pred, unsigned var, string nameSuffix)
{
  CALL("EPRSkolem::Applicator::generateSKUnit");
  ASS_EQ(inst->functor(), _lhs->functor());

  string argsStr;

  static Stack<TermList> args;
  args.reset();

  for(TermList* t=inst->args(); t->isNonEmpty(); t=t->next()) {
    args.push(*t);
    if(!argsStr.empty()) {
      argsStr += "_";
    }
    argsStr += t->toString();
  }

  string suffix = nameSuffix;
  if(!argsStr.empty() && argsStr.find_first_of("('")==string::npos) {
    suffix += "_" + argsStr;
  }


  unsigned skFunSort = getVarSort(var);
  unsigned skFun = Skolem::addSkolemFunction(0, 0, skFunSort, suffix.c_str());

  LOG("pp_esk","New Skolem function: " << env -> signature->functionName(skFun) << " suffix: " << suffix);


  TermList skTerm = TermList(Term::createConstant(skFun));

  LOG("pp_esk_contst","skolem const " << skTerm << " for X"<<var << " at instatiation " << (*inst));
  ALWAYS(_skolemFns.insert(make_pair(inst,var), skTerm)); //formula should be rectified and instances unique

  args.push(skTerm);
  ASS_EQ(args.size(), _lhs->arity()+1);

  Literal* skLit = Literal::create(pred, args.size(), true, false, args.begin());
  Formula* skForm = new AtomicFormula(skLit);
  Inference* inf = new Inference(Inference::SKOLEM_PREDICATE_INTRODUCTION);
  FormulaUnit* skUnit = new FormulaUnit(skForm, inf, Unit::AXIOM);

  LOG("pp_esk","New Skolem unit: " << (*skUnit));
  UnitList::push(skUnit, _skUnits);
}


Literal* EPRSkolem::Applicator::getSkolemLiteral(unsigned var)
{
  CALL("EPRSkolem::Applicator::getSkolemLiteral");
  ASS(!_lhs->containsSubterm(TermList(var,false)));

  string nameSuffix = _lhs->predicateName();
  if(VarManager::varNamePreserving()) {
    nameSuffix += "_" + VarManager::getVarName(var);
  }
  else {
    nameSuffix += "_X" + Int::toString(var);
  }
  nameSuffix = StringUtils::sanitizeSuffix(nameSuffix);
  unsigned arity = _lhs->arity()+1;

  static Stack<TermList> args;
  static Stack<unsigned> domainSorts;
  args.reset();
  domainSorts.reset();
  SubtermIterator vit(_lhs);
  while(vit.hasNext()) {
    TermList t = vit.next();
    ASS(t.isVar());
    args.push(t);
    domainSorts.push(getVarSort(t.var()));
  }
  args.push(TermList(var,false));
  domainSorts.push(getVarSort(var));
  ASS_EQ(args.size(), arity);
  ASS_EQ(domainSorts.size(), arity);

  unsigned pred = env -> signature->addFreshPredicate(arity, "sP", nameSuffix.c_str());
  Signature::Symbol* predSym = env -> signature->getPredicate(pred);
  predSym->setType(new PredicateType(arity, domainSorts.begin()));

  LiteralStack::Iterator instIt(_lhsInstances);
  while(instIt.hasNext()) {
    Literal* inst = instIt.next();
    generateSKUnit(inst, pred, var, nameSuffix);
  }


  Literal* res = Literal::create(pred, arity, true, false, args.begin());
  return res;
}

Formula* EPRSkolem::Applicator::applyQuantified(Formula* f)
{
  CALL("EPRSkolem::Applicator::applyQuantified");
  ASS(f->connective()==FORALL || f->connective()==EXISTS);
  ASS(f->vars());

  if(polarity()==0) {
    throw CannotEPRSkolemize();
  }

  bool toBeSkolemized = (f->connective()==EXISTS) == (polarity()==1);
  LOG("pp_esk_quant","Quantified subformula " << (*f) << " to be skolemized: " << toBeSkolemized);
  if(!toBeSkolemized) {
    ScopedLet<bool> eqLet(_extraQuantifiers, true);
    _universalVars.loadFromIterator(Formula::VarList::Iterator(f->vars()));
    Formula* res = PolarityAwareFormulaTransformer::applyQuantified(f);
    //In some sense it would be right to remove the f->vars() added to _universalVars
    //at this point (as we're leaving the scope of the quantifier), but we assume that
    //the formulas are rectified, therefore variable names in quantifiers are unique
    //and so it makes no harm to leave the variables in the set.
    return res;
  }

  if(_extraQuantifiers) {
    throw CannotEPRSkolemize();
  }

  Formula::VarList::Iterator vit(f->vars());
  Stack<Literal*> skLits;
  skLits.reset();
  while(vit.hasNext()) {
    unsigned var = vit.next();
    Literal* skLit = getSkolemLiteral(var);
    skLits.push(skLit);
  }

  Formula* inner = apply(f->qarg());

  Connective resCon = (f->connective()==FORALL) ? EXISTS : FORALL;
  Stack<Literal*>::BottomFirstIterator skLitIt(skLits);
  while(skLitIt.hasNext()) {
    Literal* skLit = skLitIt.next();
    if(resCon==FORALL) {
      inner = new BinaryFormula(IMP, new AtomicFormula(skLit), inner);
    }
    else {
      FormulaList* conjArgs = 0;
      FormulaList::push(new AtomicFormula(skLit), conjArgs);
      FormulaList::push(inner, conjArgs);
      inner = new JunctionFormula(AND, conjArgs);
    }
  }

  return new QuantifiedFormula(resCon, f->vars(), inner);
}

void EPRSkolem::processLiteralHeader(Literal* lit, unsigned header)
{
  CALL("EPRSkolem::processLiteralHeader");

  if(!_inlinedHeaders.find(header)) {
    return;
  }
  LOG("pp_esk_inst","added instance " << (*lit) << " as " <<((header&1) ? "positive" : "negative"));
  _insts.pushToKey(header, lit);
  if(!lit->ground()) {
    _inlinedHeaders.remove(header);
    LOG("pp_esk","Disabled header " << headerToString(header));
  }
}

void EPRSkolem::processProblemLiteral(Literal* lit, int polarity)
{
  CALL("EPRSkolem::processProblemLiteral");

  if(lit->isNegative()) {
    polarity = -polarity;
  }

  unsigned negHdr = lit->functor()*2;
  unsigned posHdr = negHdr + 1;
  switch(polarity) {
  case -1:
    processLiteralHeader(lit, negHdr);
    break;
  case 1:
    processLiteralHeader(lit, posHdr);
    break;
  case 0:
    processLiteralHeader(lit, posHdr);
    processLiteralHeader(lit, negHdr);
    break;
  default:
    ASSERTION_VIOLATION;
  }
}

void EPRSkolem::processProblemClause(Clause* cl)
{
  CALL("EPRSkolem::processProblemClause");

  Clause::Iterator cit(*cl);
  while(cit.hasNext()) {
    Literal* l = cit.next();
    processProblemLiteral(l,1);
  }
}

void EPRSkolem::processProblemFormula(FormulaUnit* fu)
{
  CALL("EPRSkolem::processProblemFormula");

  SubformulaIterator sfit(fu->formula());
  while(sfit.hasNext()) {
    int polarity;
    Formula* sf = sfit.next(polarity);
    if(sf->connective()!=LITERAL) {
      continue;
    }
    processProblemLiteral(sf->literal(), polarity);
  }
}

void EPRSkolem::enableLiteralHeader(unsigned header)
{
  _inlinedHeaders.insert(header);
  LOG("pp_esk","Enabled header " << headerToString(header));
}

void EPRSkolem::processActiveDefinitions(UnitList* units)
{
  CALL("EPRSkolem::processActiveDefinitions");

  Stack<unsigned>::Iterator apit(_activePreds);
  while(apit.hasNext()) {
    unsigned pred = apit.next();
    int pol = _nonEprDefPolarities[pred];
    if(_nonEprReversedPolarity[pred]) {
      pol *= -1;
    }
    unsigned negHdr = pred*2;
    unsigned posHdr = negHdr + 1;
    switch(pol) {
    case -1:
      enableLiteralHeader(negHdr);
      break;
    case 1:
      enableLiteralHeader(posHdr);
      break;
    case 0:
      enableLiteralHeader(negHdr);
      enableLiteralHeader(posHdr);
      break;
    default:
      ASSERTION_VIOLATION;
    }
  }

  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* unit = uit.next();
    if(_activeUnits.find(unit)) {
      continue;
    }
    if(unit->isClause()) {
      processProblemClause(static_cast<Clause*>(unit));
    }
    else {
      processProblemFormula(static_cast<FormulaUnit*>(unit));
    }
  }

  Stack<unsigned>::Iterator apit2(_activePreds);
  while(apit2.hasNext()) {
    unsigned pred = apit2.next();
    FormulaUnit* def = _nonEprDefs[pred];
    LOG("pp_esk","Processing definition of " << env -> signature->predicateName(pred)<<": "
	   << (*def));
    processDefinition(def);
  }
}

FormulaUnit* EPRSkolem::definitionToImplication(FormulaUnit* premise, Literal* lhs,
    Formula* rhs, int topPolarity)
{
  CALL("EPRSkolem::definitionToImplication");

  Formula* lhsForm = new AtomicFormula(lhs);

  Formula* body;
  if(topPolarity==1) {
    body = new BinaryFormula(IMP, lhsForm, rhs);
  }
  else {
    ASS_EQ(topPolarity,-1);
    body = new BinaryFormula(IMP, rhs, lhsForm);
  }
  Formula::VarList* freeVars = body->freeVariables();
  if(freeVars) {
    body = new QuantifiedFormula(FORALL, freeVars, body);
  }
  Inference* inf = new Inference1(Inference::PREDICATE_SKOLEMIZE, premise);
  return new FormulaUnit(body, inf, premise->inputType());
}

bool EPRSkolem::applyToDefinitionHalf(FormulaUnit* fu, Literal* lhs, Formula* rhs,
    int topPolarity, UnitList*& res)
{
  CALL("EPRSkolem::applyToDefinitionHalf");

  LOG("pp_esk","Applying to " << ((topPolarity==1) ? "=>" : "<=") << " of "<< (*fu));

  Applicator apl(*this, lhs, topPolarity);
  Formula* newRhs = apl.transform(rhs);
  LOG("pp_esk","Transformed rhs: " << (*newRhs));


  if(apl.hasInstances()) {
    FormulaUnit* resDef = definitionToImplication(fu, lhs, newRhs, topPolarity);
    res = UnitList::concat(res, apl._skUnits);
    apl._skUnits = 0;
    UnitList::push(resDef, res);
    LOG("pp_esk","New half-definition: " << (*resDef));
  }
  else {
    ASS_EQ(apl._skUnits, 0);
    LOG("pp_esk","Half-definition not introduced because there are no instances.");
  }
  return true;
}

void EPRSkolem::processDefinition(FormulaUnit* unit)
{
  CALL("EPRSkolem::processDefinition");

  LOG("pp_esk","Processing definition: " << (*unit));

  Literal* lhs;
  Formula* rhs;
  PDUtils::splitDefinition(unit, lhs, rhs);

  unsigned pred = lhs->functor();
  unsigned negHdr = pred<<1;
  unsigned posHdr = negHdr+1;

  bool inlineNeg = _inlinedHeaders.find(negHdr);
  bool inlinePos = _inlinedHeaders.find(posHdr);
  if(!inlineNeg && !inlinePos) {
    LOG("pp_esk","Skipping definition because both polarities are disabled: " << (*unit));
    processProblemFormula(unit);
    return;
  }

  unsigned negPolarity = lhs->isPositive() ? -1 : 1;
  unsigned posPolarity = -negPolarity;

  UnitList* res = 0;
  try{
    if(inlineNeg && !applyToDefinitionHalf(unit, lhs, rhs, negPolarity, res)) {
      inlineNeg = false;
    }

    if(inlinePos && !applyToDefinitionHalf(unit, lhs, rhs, posPolarity, res)) {
      inlinePos = false;
    }
  }
  catch (CannotEPRSkolemize) {
    res->destroy();
    processProblemFormula(unit);
    LOG("pp_esk","Cannot skolemize " << (*unit));
    return;
  }

  if(!inlinePos && !inlineNeg) {
    res->destroy();
    return;
  }

  if(!inlineNeg) {
    FormulaUnit* impl = definitionToImplication(unit, lhs, rhs, negPolarity);
    UnitList::push(impl, res);
    processProblemFormula(impl);
  }
  if(!inlinePos) {
    FormulaUnit* impl = definitionToImplication(unit, lhs, rhs, posPolarity);
    UnitList::push(impl, res);
    processProblemFormula(impl);
  }

  ALWAYS(_replacements.insert(unit, res));
}

FormulaUnit* EPRSkolem::constantSkolemize(FormulaUnit* unit)
{
  CALL("EPRSkolem::constantSkolemize");

  ConstantSkolemizer skol;
  return skol.transform(unit);
}

void EPRSkolem::apply(Problem& prb)
{
  CALL("EPRSkolem::apply");

  if(apply(prb.units())) {
    prb.invalidateProperty();
  }
}

bool EPRSkolem::apply(UnitList*& units)
{
  CALL("EPRSkolem::apply(UnitList*&)");

  CONDITIONAL_SCOPED_TRACE_TAG(_trace, "pp_esk");

  LOG("pp_esk","EPR skolemization start");
  LOG("pp_esk","Constant skolemization");

  bool modified = false;

  {
    ConstantSkolemizer skol(_trace);
    bool csModified = skol.transform(units);
    modified |= csModified;
  }

  LOG("pp_esk","Predicate equivalence removal");

  {
    //remove predicate equivalences
    PDInliner pdi(false);
    bool eqInlinerModified = pdi.apply(units, true);
    modified |= eqInlinerModified;
  }

  LOG("pp_esk","Definition replacement");

  scan(units);

  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    UnitList* newUnits = 0;
    if(!apply(u, newUnits)) {
      continue;
    }
    uit.insert(newUnits);
    uit.del();
    modified = true;
  }
  LOG("pp_esk","EPR skolemization done");

  return modified;
}


bool EPRSkolem::apply(Unit* unit, UnitList*& acc)
{
  CALL("EPRSkolem::apply(Unit*,UnitList*&)");

  UnitList* res;
  if(!_replacements.find(unit, res)) {
    return false;
  }

  acc = UnitList::concat(res,acc);
  return true;
}

string EPRSkolem::headerToString(unsigned header)
{
  CALL("EPRSkolem::headerToString");

  return ((header&1) ? "" : "~") + env -> signature->predicateName(header>>1);
}


}
