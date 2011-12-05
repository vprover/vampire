/**
 * @file PDInliner.cpp
 * Implements class PDInliner.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Timer.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Flattening.hpp"
#include "PDUtils.hpp"
#include "Rectify.hpp"
#include "SimplifyFalseTrue.hpp"
#include "Statistics.hpp"
#include "VarManager.hpp"

#include "PDInliner.hpp"

#undef LOGGING
#define LOGGING 0

namespace Shell
{

struct PDInliner::Applicator
{
  Applicator(PDef& parent, Literal* lit);

  TermList apply(unsigned var)
  {
    CALL("PDInliner::Applicator::apply");

    TermList res;
    if(_map.find(var, res)) {
      return res;
    }
    //Undefined variables should be only variables quantified inside the body
    //of the definition.

    if(_used.insert(var)) {
      //the variable is not used, so we can keep it unchanged
      res = TermList(var, false);
      ALWAYS(_map.insert(var, res));
      return res;
    }

    unsigned newVar;
    //we need to come up with new variable for the quantifier
    if(VarManager::varNamePreserving()) {
      newVar = VarManager::getVarAlias(var);
    }
    else {
      newVar = var+1;
      while(_used.find(newVar)) {
	newVar++;
      }
    }

    ALWAYS(_used.insert(newVar));
    res = TermList(newVar, false);
    ALWAYS(_map.insert(var, res));
    return res;
  }

  DHSet<unsigned> _used;
  DHMap<unsigned,TermList> _map;
};


/**
 * Class representing a single predicate definition
 *
 * For in functions that take polarity as argument, the value can be -1, 0, 1.
 * Zero means "double" polarity - this occurrs e.g. inside equivalences.
 */
struct PDInliner::PDef
{
  PDef(PDInliner* parent, unsigned pred) : _parent(parent), _pred(pred), _asymDef(false) {}

  static FormulaUnit* fixFormula(FormulaUnit* fu) {
    fu = Rectify::rectify(fu);
    fu = SimplifyFalseTrue::simplify(fu);
    fu = Flattening::flatten(fu);
    return fu;
  }

  /**
   * Perform inlining and return the result. If the resulting clause is a tautology,
   * return zero.
   */
  Unit* apply(Clause* cl)
  {
    CALL("PDInliner::PDef::apply(Clause*)");

    LOG("pp_inl_substep","Inlining "<<toString()<<" into "<<(*cl));

    static LiteralStack lits;
    lits.reset();
    static Stack<Formula*> forms;
    forms.reset();

    bool modified = false;

    unsigned clen = cl->length();
    for(unsigned i=0; i<clen; i++) {
      Literal* lit = (*cl)[i];
      if(lit->functor()!=_pred || identity(1, lit)) {
	lits.push(lit);
	continue;
      }
      if(constantBody(1, lit)) {
	if(constantApply(1, lit)) {
	  return 0; //tautology
	}
	//false literal -- we skip it
	modified = true;
      }
      else if(atomicBody(1, lit)) {
	Literal* newLit = atomicApply(1, lit);
	if(newLit!=lit) {
	  modified = true;
	}
	lits.push(newLit);
      }
      else {
	modified = true;
	forms.push(apply(1, lit));
      }
    }

    if(!modified) {
      return cl;
    }

    env.statistics->inlinedPredicateDefinitions++;

    Unit::InputType inp;
    Inference* inf;
    if(_defUnit) {
      inp = Unit::getInputType(cl->inputType(), _defUnit->inputType());
      inf = new Inference2(Inference::PREDICATE_DEFINITION_UNFOLDING, cl, _defUnit);
    }
    else {
      inp = cl->inputType();
      inf = new Inference1(Inference::PREDICATE_DEFINITION_UNFOLDING, cl);
    }
    if(forms.isEmpty()) {
      Clause* res = Clause::fromIterator(LiteralStack::Iterator(lits), inp, inf);
      LOG("pp_inl_step","Inlining "<<toString()<<" into "<<(*cl)<<" gave "<<(*res));
      return res;
    }
    FormulaUnit* res;
    if(lits.isEmpty() && forms.size()==1) {
      res = new FormulaUnit(forms.top(), inf, inp);
    }
    else {
      //build a disjunction of all we have (both formulas and literals)
      FormulaList* disj = 0;
      FormulaList::pushFromIterator(Stack<Formula*>::Iterator(forms), disj);
      LiteralStack::Iterator litIt(lits);
      while(litIt.hasNext()) {
	FormulaList::push(new AtomicFormula(litIt.next()), disj);
      }
      Formula* form = new JunctionFormula(OR, disj);
      res = new FormulaUnit(form, inf, inp);
    }
    res = fixFormula(res);

    LOG("pp_inl_step","Inlining "<<toString()<<" into "<<(*cl)<<" gave "<<(*res));

    return res;
  }

  FormulaUnit* apply(FormulaUnit* unit)
  {
    CALL("PDInliner::PDef::apply(FormulaUnit*)");

    LOG("pp_inl_substep","Inlining "<<toString()<<" into "<<(*unit));

    Formula* form = apply(1,unit->formula());
    if(form==unit->formula()) {
      return unit;
    }

    env.statistics->inlinedPredicateDefinitions++;

    Unit::InputType inp;
    Inference* inf;
    if(_defUnit) {
      inp = Unit::getInputType(unit->inputType(), _defUnit->inputType());
      inf = new Inference2(Inference::PREDICATE_DEFINITION_UNFOLDING, unit, _defUnit);
    }
    else {
      inp = unit->inputType();
      inf = new Inference1(Inference::PREDICATE_DEFINITION_UNFOLDING, unit);
    }

    FormulaUnit* res = new FormulaUnit(form, inf, inp);
    res = fixFormula(res);

    LOG("pp_inl_step","Inlining "<<toString()<<" into "<<(*unit)<<" gave "<<(*res));

    return res;
  }

  Formula* apply(int polarity, Formula* form);

  Unit* apply(Unit* unit)
  {
    CALL("PDInliner::PDef::apply(Unit*)");
    if(unit->isClause()) {
     return apply(static_cast<Clause*>(unit));
    }
    else {
     return apply(static_cast<FormulaUnit*>(unit));
    }
  }

  bool identity(int polarity, Literal* l) { return getBody(polarity, l)==0; }
  bool atomicBody(int polarity, Literal* l)
  { return !identity(polarity, l) && getBody(polarity, l)->connective() == LITERAL; }
  bool constantBody(int polarity, Literal* l)
  {
    if(identity(polarity, l)) {
      return false;
    }
    Connective con = getBody(polarity, l)->connective();
    return con==TRUE || con==FALSE;
  }


  Literal* atomicApply(int polarity, Literal* l)
  {
    CALL("PDInliner::PDef::atomicApply");
    ASS(atomicBody(polarity,l));

    Applicator apl(*this, l);
    Literal* body = getBody(polarity, l)->literal();
    Literal* res = SubstHelper::apply(body, apl);

    if(l->isPositive() != _lhs->isPositive()) {
      res = Literal::complementaryLiteral(res);
    }
    LOG("pp_inl_substep", "Lit inlining: "<<(*l)<<" --> "<<(*res));
    return res;
  }

  /**
   * Return true or false for either true or false constant
   */
  bool constantApply(int polarity, Literal* l)
  {
    CALL("PDInliner::PDef::constantApply");
    ASS(constantBody(polarity,l));

    bool negate = l->isPositive()!=_lhs->isPositive();
    bool res = negate ^ (getBody(polarity,l)->connective()==TRUE);
    LOG("pp_inl_substep", "Lit inlining: "<<(*l)<<" --> "<<(res ? "$true" : "$false"));
    return res;
  }

  Formula* apply(int polarity, Literal* l)
  {
    CALL("PDInliner::PDef::apply(int,Literal*)");
    ASS(!identity(polarity, l));

    if(atomicBody(polarity, l)) {
      return new AtomicFormula(atomicApply(polarity, l));
    }

    Applicator apl(*this, l);
    Formula* body = getBody(polarity,l);
    Formula* res = SubstHelper::apply(body, apl);

    if(l->isPositive() != _lhs->isPositive()) {
      res = new NegatedFormula(res);
    }
    LOG("pp_inl_substep", "Lit inlining: "<<(*l)<<" --> "<<(*res));
    return res;
  }

  /**
   * Inline redicate definition into this definition.
   */
  void inlineDef(PDef* def)
  {
    CALL("PDInliner::PDef::inlineDef");

    LOG("pp_inl_step","Inlining def "<<def->toString()<<" into "<<toString());

    if(_asymDef) {
      ASS_NEQ(def->_pred, _lhs->functor());
      if(_posBody) { _posBody = apply(1,_posBody); }
      if(_negBody) { _negBody = apply(1,_negBody); }
      if(_dblBody) { _dblBody = apply(1,_dblBody); }
      if(_defUnit) { _defUnit = def->apply(_defUnit); }
    }
    else {
      FormulaUnit* newUnit = def->apply(_defUnit);
      assignUnit(newUnit);
    }
    LOG("pp_inl_step","Result of def to def inlining: "<<toString());

    //remove the inlined predicate from dependencies of the current predicate.

    //Dependencies are stored in two places:
    //PDInliner::PDef::_dependencies and PDInliner::_dependent
    //There are two situations where we call this function:
    //Inlining old definition into a new one and inlining a new
    //definition into an old one.
    //We need to actually remove dependencies only from
    //PDInliner::PDef::_dependencies when inlining new definition
    //into old one. In other cases the dependencies either aren't added yet,
    //or will be removed all at one in the PDInliner::tryGetDef() function.
    _dependencies.remove(def->_pred);
    LOG("pp_inl_dep","removed dep: "<<env.signature->predicateName(def->_pred)<<" from "<<env.signature->predicateName(_pred));

    //add the predicates added by inlining into dependencies
    Set<unsigned>::Iterator depIt(def->_dependencies);
    while(depIt.hasNext()) {
      unsigned dep = depIt.next();
      LOG("pp_inl_dep","added dep: "<<env.signature->predicateName(dep)<<" to "<<env.signature->predicateName(_pred));
      registerDependentPred(dep);
    }
    LOG("pp_inl_dep","dep update finished");
  }

  void registerDependentPred(unsigned depPred)
  {
    CALL("PDInliner::PDef::registerDependentPred");
    ASS(!_parent->_defs[depPred]); //we cannot depend on a defined predicate

    _parent->_dependent[depPred].insert(_pred);
    _dependencies.insert(depPred);
    LOG("pp_inl_dep","added dep: "<<env.signature->predicateName(depPred)<<" to definition of "<<env.signature->predicateName(_pred));
  }

  void assignUnit(FormulaUnit* unit)
  {
    CALL("PDInliner::PDef::assignUnit");

    _asymDef = false;

    LOG("pp_inl_def","Definition from unit: "<<unit->toString());
    _defUnit = unit;
    Formula* f = unit->formula();
    if(f->connective()==FORALL) {
      f = f->qarg();
    }
    ASS_EQ(f->connective(),IFF);
    if(f->left()->connective()==LITERAL && f->left()->literal()->functor()==_pred) {
      makeDef(f->left()->literal(), f->right());
    }
    else {
      ASS_EQ(f->right()->connective(),LITERAL);
      ASS_EQ(f->right()->literal()->functor(),_pred);
      makeDef(f->right()->literal(), f->left());
    }

    unsigned pred1, pred2;
    _predicateEquivalence = PDUtils::isPredicateEquivalence(unit, pred1, pred2);
    if(_predicateEquivalence) {
      if(pred1==_pred) {
	_tgtPredicate = pred2;
      }
      else {
	ASS_EQ(pred1,_pred);
	_tgtPredicate = pred1;
      }
    }
  }

  /**
   * Make the object into an asymetric definition
   *
   * If some body argument is zero, the lhs is not transformed for that polarity.
   */
  void assignAsym(Literal* lhs, Formula* posBody, Formula* negBody, Formula* dblBody, FormulaUnit* premise)
  {
    CALL("PDInliner::PDef::assignAsym");
    ASS_EQ(lhs->functor(),_pred);

    _asymDef = true;
    _defUnit = premise;
    _lhs = lhs;

    _posBody = posBody;
    _negBody = negBody;
    _dblBody = dblBody;

    LOG("pp_inl_def","Asymetric definition: " << toString());

    _predicateEquivalence = false;
  }

  bool predicateEquivalence()
  {
    CALL("PDInliner::PDef::predicateEquivalence");
    return _predicateEquivalence;
  }
  /**
   * If @c predicateEquivalence() returns true, this returns the target
   * predicate of this definition.
   */
  unsigned tagretPredicate()
  {
    CALL("PDInliner::PDef::tagretPredicate");
    ASS(predicateEquivalence());
    return _tgtPredicate;
  }

  /**
   * Return string representation of the definition.
   *
   * For debugging and logging purposes.
   */
  string toString() const
  {
    CALL("toString");
    if(_asymDef) {
      string posStr = _posBody ? _posBody->toString() : "(none)";
      string negStr = _negBody ? _negBody->toString() : "(none)";
      string dblStr = _dblBody ? _dblBody->toString() : "(none)";
      return "[Asym def " + _lhs->toString() + " --> (+) " + posStr
	  + ", (-) " + negStr + ", (0) " + dblStr + " ]";
    }
    else {
      return "[Def " + _defUnit->toString()+" ]";
    }
  }
private:
  void makeDef(Literal* lhs, Formula* body)
  {
    CALL("PDInliner::PDef::makeDef");

    _lhs = lhs;
    _body = body;
  }

  Formula* getBody(int polarity, Literal* l) {
    return (l->isPositive()==_lhs->isPositive()) ? getBody(polarity) : getBody(-polarity);
  }
  Formula* getBody(int polarity) {
    if(_asymDef) {
      switch(polarity) {
      case 1: return _posBody;
      case -1: return _negBody;
      case 0: return _dblBody;
      default: ASSERTION_VIOLATION; break;
      }
    }
    else {
      return _body;
    }
  }

public:
  PDInliner* _parent;
  unsigned _pred;
  FormulaUnit* _defUnit;
  Literal* _lhs;
  Formula* _body;
  Set<unsigned> _dependencies;
  bool _predicateEquivalence;
  /** Valid iff _isPredEquivalence==true */
  unsigned _tgtPredicate;

  bool _asymDef;
  Formula* _posBody;
  Formula* _negBody;
  /** If @c _asymDef is true, contains replacement for occurrences inside equivalences or XORs */
  Formula* _dblBody;
};

PDInliner::Applicator::Applicator(PDef& parent, Literal* lit)
{
  CALL("PDInliner::Applicator::Applicator");
  ASS_EQ(parent._pred, lit->functor());

  Literal* lhs = parent._lhs;
  TermList* dArg = lhs->args();
  TermList* instArg = lit->args();
  while(!dArg->isEmpty()) {
    ASS(dArg->isOrdinaryVar());
    unsigned v = dArg->var();
    ALWAYS(_map.insert(v, *instArg));
    dArg = dArg->next();
    instArg = instArg->next();
  }
  ASS(instArg->isEmpty());

  //collect used variables, so that we can rename them if they appear in
  //quantifiers
  VariableIterator vit(lit);
  while(vit.hasNext()) {
    unsigned usedVar = vit.next().var();
    _used.insert(usedVar);
  }
}

Formula* PDInliner::PDef::apply(int polarity, Formula* form)
{
  CALL("PDInliner::PDef::apply(int,Formula*)");

  LOG("pp_inl_substep","Apply to subformula "<<form->toString()<<"with polarity "<<polarity);

  Connective con = form->connective();
  switch (con) {
  case LITERAL:
  {
    Literal* l=form->literal();
    if(l->functor()!=_pred || identity(polarity, l)) {
      return form;
    }
    if(atomicBody(polarity, l)) {
      Literal* newLit = atomicApply(polarity, l);
      if(newLit==l) {
	return form;
      }
      return new AtomicFormula(newLit);
    }
    return apply(polarity, l);
  }

  case AND:
  case OR: {
    FormulaList* resArgs = 0;
    bool modified = false;
    FormulaList::Iterator fs(form->args());
    while (fs.hasNext()) {
      Formula* arg = fs.next();
      Formula* newArg = apply(polarity, arg);
      if(arg!=newArg) {
	modified = true;
      }
      FormulaList::push(newArg, resArgs);
    }
    if(!modified) {
      resArgs->destroy();
      return form;
    }
    return new JunctionFormula(con, resArgs);
  }

  case IMP: {
    Formula* newLeft = apply(-polarity, form->left());
    Formula* newRight = apply(polarity, form->right());
    if(newLeft==form->left() && newRight==form->right()) {
      return form;
    }
    return new BinaryFormula(IMP, newLeft, newRight);
  }

  case NOT: {
    Formula* newArg = apply(-polarity, form->uarg());
    if(newArg==form->uarg()) {
      return form;
    }
    return new NegatedFormula(newArg);
  }

  case IFF:
  case XOR:{
    Formula* newLeft = apply(0, form->left());
    Formula* newRight = apply(0, form->right());
    if(newLeft==form->left() && newRight==form->right()) {
      return form;
    }
    return new BinaryFormula(con, newLeft, newRight);
  }

  case FORALL:
  case EXISTS:{
    Formula* newArg = apply(polarity, form->qarg());
    if(newArg==form->qarg()) {
      return form;
    }
    Formula::VarList* vars = form->vars()->copy();
    return new QuantifiedFormula(con, vars, newArg);
  }

  case TRUE:
  case FALSE:
    return form;

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
    return 0;
#endif
  }
}

PDInliner::PDInliner(bool axiomsOnly, bool trace, bool nonGrowing)
 : _axiomsOnly(axiomsOnly), _nonGrowing(nonGrowing), _trace(trace)
{
  CALL("PDInliner::PDInliner");

  _dependent.ensure(env.signature->predicates());
}

PDInliner::~PDInliner()
{
  CALL("PDInliner::~PDInliner");

  unsigned preds = env.signature->predicates();
  for(unsigned i=0; i<preds; i++) {
    if(_defs[i]) {
      delete _defs[i];
    }
  }
}

void PDInliner::apply(Problem& prb)
{
  CALL("PDInliner::apply");

  if(apply(prb.units())) {
    prb.invalidateProperty();
  }
}


bool PDInliner::apply(UnitList*& units, bool inlineOnlyEquivalences)
{
  CALL("PDInliner::apply");
  CONDITIONAL_SCOPED_TRACE_TAG(_trace,"pp_inl");

  bool modified = scanAndRemoveDefinitions(units, inlineOnlyEquivalences);

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

Unit* PDInliner::apply(Unit* u)
{
  CALL("PDInliner::apply(Unit*)");
  CONDITIONAL_SCOPED_TRACE_TAG(_trace,"pp_inl");

  Stack<unsigned> preds;
  u->collectPredicates(preds);

  //make the list of predicates unique
  makeUnique(preds);

  Unit* res = u;

  int steps=0;
  //apply definitions of predicates that appear in the unit
  while(res && preds.isNonEmpty()) {
    unsigned pred = preds.pop();
    if(!_defs[pred]) {
      //we don't have a definition for this predicate
      continue;
    }
    ASS_NEQ(pred, 0); //equality is never defined

    //if the unit becomes a tautology, it can be assigned zero here
    res = _defs[pred]->apply(res);
    steps++;
  }
  RSTAT_MCTR_INC("inl steps", steps);
  RSTAT_MST_INC("inl grow", u->toString().size(), res ? res->toString().size() : 0);
  return res;
}

FormulaUnit* PDInliner::apply(FormulaUnit* u)
{
  CALL("PDInliner::apply(FormulaUnit*)");

  Unit* res = apply(static_cast<Unit*>(u));
  ASS(!res->isClause());
  return static_cast<FormulaUnit*>(res);
}

/**
 * Update the _predOccCounts member variable by predicate occurrences in @c u.
 */
void PDInliner::updatePredOccCounts(Unit* u)
{
  CALL("PDInliner::updatePredOccCounts");
  ASS(_nonGrowing); //we update _predOccCounts only if _nonGrowing is true

  static Stack<unsigned> predOccurences;
  ASS(predOccurences.isEmpty());
  u->collectPredicates(predOccurences);
  while(predOccurences.isNonEmpty()) {
    _predOccCounts.inc(predOccurences.pop());
  }
}

bool PDInliner::scanAndRemoveDefinitions(UnitList*& units, bool equivalencesOnly)
{
  CALL("PDInliner::scanAndRemoveDefinitions(UnitList*)");
  CONDITIONAL_SCOPED_TRACE_TAG(_trace,"pp_inl");

  bool modified = false;

  if(_nonGrowing) {
    UnitList::Iterator it(units);
    while(it.hasNext()) {
      Unit* u = it.next();
      updatePredOccCounts(u);
    }
  }

  {
    UnitList::DelIterator it(units);
    while(it.hasNext()) {
      Unit* u = it.next();
      if(u->isClause()) {
	continue;
      }
      if(tryGetPredicateEquivalence(static_cast<FormulaUnit*>(u))) {
	modified = true;
	it.del();
      }
    }
  }

  if(equivalencesOnly) {
    return modified;
  }

  UnitList::DelIterator it(units);
  while(it.hasNext()) {
    Unit* u = it.next();
    if(u->isClause()) {
      continue;
    }
    if(tryGetDef(static_cast<FormulaUnit*>(u))) {
      modified = true;
      it.del();
    }
  }
  return modified;
}

bool PDInliner::isEligible(FormulaUnit* u)
{
  CALL("PDInliner::isEligible");

  return !_axiomsOnly || u->inputType()==Unit::AXIOM;
}

bool PDInliner::tryGetPredicateEquivalence(FormulaUnit* unit)
{
  CALL("PDInliner::tryGetPredicateEquivalence");
  CONDITIONAL_SCOPED_TRACE_TAG(_trace,"pp_inl");

  if(!isEligible(unit)) {
    return false;
  }

  unsigned pred1, pred2;
  if(!PDUtils::isPredicateEquivalence(unit, pred1, pred2)) {
    return false;
  }

  if(tryGetDef(unit)) {
    return true;
  }
  LOG("pp_inl_scan","Formula " << (*unit) << " needs further inlining to become definition");
  ASS(_defs[pred1] || _defs[pred2]);
  //we first get all predicate equivalences and other definitions only after that
  ASS(!_defs[pred1] || _defs[pred1]->predicateEquivalence());
  ASS(!_defs[pred2] || _defs[pred2]->predicateEquivalence());

  unsigned tgtPred1 = _defs[pred1] ? _defs[pred1]->tagretPredicate() : pred1;
  unsigned tgtPred2 = _defs[pred2] ? _defs[pred2]->tagretPredicate() : pred2;

  if(tgtPred1==tgtPred2) {
    //this equivalence is redundant
    return false;
  }
  if(_defs[pred1]) {
    unit = _defs[pred1]->apply(unit);
  }
  else {
    unit = _defs[pred2]->apply(unit);
  }
  ALWAYS(tryGetDef(unit));
  return true;
}

bool PDInliner::tryGetDef(FormulaUnit* unit)
{
  CALL("PDInliner::scan(FormulaUnit*)");
  CONDITIONAL_SCOPED_TRACE_TAG(_trace,"pp_inl");

  if(!isEligible(unit)) {
    return false;
  }

  Formula* f = unit->formula();
  if(f->connective()==FORALL) {
    f = f->qarg();
  }
  if(f->connective()!=IFF) {
    return false;
  }
  if(f->left()->connective()==LITERAL) {
    if(tryGetDef(unit, f->left()->literal(), f->right())) {
      return true;
    }
  }
  if(f->right()->connective()==LITERAL) {
    return tryGetDef(unit, f->right()->literal(), f->left());
  }
  return false;
}

/**
 * Return true if lhs<=>rhs is a definition whose inlining will not
 * lead to growth in the size of the problem.
 *
 * This function makes use of the value of _predOccCounts variable.
 *
 * Definition is non-growing if it's rhs is a literal that doesn't
 * contain non-constant functions, or if the lhs predicate occurrs at
 * most once elsewhere in the problem.
 *
 * An important property is that predicate equivalences are non-growing
 * (we rely on the fact that all predicate equivalences are inlined).
 */
bool PDInliner::isNonGrowingDef(Literal* lhs, Formula* rhs)
{
  CALL("PDInliner::isNonGrowingDef");

  if(rhs->connective()==LITERAL && rhs->literal()->isShallow()) {
    return true;
  }
  unsigned lhsPred = lhs->functor();
  unsigned occCnt = _predOccCounts.get(lhsPred);
  ASS_GE(occCnt,1); //there must be at least one occurrence -- in the definition itself
  return occCnt<=2;
}

bool PDInliner::tryGetDef(FormulaUnit* unit, Literal* lhs, Formula* rhs)
{
  CALL("PDInliner::tryGetDef");
  CONDITIONAL_SCOPED_TRACE_TAG(_trace,"pp_inl");

  if(lhs->isEquality()) {
    return false;
  }

  if(_nonGrowing && !isNonGrowingDef(lhs, rhs)) {
    return false;
  }

  bool headInline = false;
  unsigned origPred = lhs->functor();
  unsigned defPred = origPred;
  if(_defs[defPred]) {
    //there already is one predicate definition
    if(_defs[defPred]->predicateEquivalence()) {
      //it is equivalence between predicates, so we will inline into the head
      defPred = _defs[defPred]->tagretPredicate();
      headInline = true;
    }
    else {
      return false;
    }
  }

  MultiCounter counter;
  for (const TermList* ts = lhs->args(); ts->isNonEmpty(); ts=ts->next()) {
    if (! ts->isVar()) {
      return false;
    }
    int w = ts->var();
    if (counter.get(w) != 0) { // more than one occurrence
      return false;
    }
    counter.inc(w);
  }

  static Stack<unsigned> dependencies;
  dependencies.reset();

  SubformulaIterator sfit(rhs);
  while(sfit.hasNext()) {
    Formula* sf=sfit.next();
    if(sf->connective()!=LITERAL) {
      continue;
    }
    Literal* lit=sf->literal();
    unsigned litPred = lit->functor();
    if(litPred==defPred) {
      return false;
    }

    if(_dependent[defPred].contains(litPred)) {
      //Check for cyclic dependencies.
      //This shalow check works only because we eagerly inline all discovered
      //definitions into other definitions
      return false;
    }

    if(!lit->isEquality()) {
      dependencies.push(litPred);
    }
  }

  {
    Formula::VarList* freeVars = rhs->freeVariables();
    bool extraFreeVars = false;
    while(freeVars) {
      unsigned v = Formula::VarList::pop(freeVars);
      if(!counter.get(v)) {
	extraFreeVars = true;
      }
    }
    if(extraFreeVars) {
      return false;
    }
  }

  //here we make the list of dependencies unique
  VirtualIterator<unsigned> uniqueDepIt = pvi(
      getUniquePersistentIterator(Stack<unsigned>::Iterator(dependencies)) );
  dependencies.reset();
  dependencies.loadFromIterator(uniqueDepIt);

  if(headInline) {
    unit = _defs[origPred]->apply(unit);
  }

  PDef* def = new PDef(this, defPred);
  def->assignUnit(unit);
  _defs[defPred] = def;

  //inline dependencies into the new definitions
  Stack<unsigned>::Iterator depIt(dependencies);
  while(depIt.hasNext()) {
    unsigned dependency = depIt.next();
    if(_defs[dependency]) {
      def->inlineDef(_defs[dependency]);
    }
    else {
      def->registerDependentPred(dependency);
    }
  }

  //inline the new definition into definitions that depend on it
  Set<unsigned>::Iterator dependentIt(_dependent[defPred]);
  while(dependentIt.hasNext()) {
    unsigned dependent = dependentIt.next();
    ASS(_defs[dependent]);
    _defs[dependent]->inlineDef(def);
  }

  _dependent[defPred].reset();
  return true;
}

/**
 * Add asymetric definition of @c lhs or return false if predicate
 * of @c lhs is already defined.
 *
 * If some body formula is zero, the definitioin acts as identity for
 * that polarity.
 */
bool PDInliner::addAsymetricDefinition(Literal* lhs, Formula* posBody, Formula* negBody, Formula* dblBody,
    FormulaUnit* premise)
{
  CALL("PDInliner::addAsymetricDefinition");
  CONDITIONAL_SCOPED_TRACE_TAG(_trace,"pp_inl");

  unsigned pred = lhs->functor();
  if(_defs[pred]) {
    return false; //predicate already defined
  }
  _defs[pred] = new PDef(this, pred);
  _defs[pred]->assignAsym(lhs, posBody, negBody, dblBody, premise);

  return true;
}



}
