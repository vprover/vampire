/**
 * @file PDInliner.cpp
 * Implements class PDInliner.
 */

#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/MultiCounter.hpp"
#include "Lib/Timer.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Flattening.hpp"
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
  PDef(PDInliner* parent, unsigned pred) : _parent(parent), _pred(pred) {}

  static FormulaUnit* fixFormula(FormulaUnit* fu) {
    Unit* u = fu;
    u = Rectify::rectify(u);
    u = SimplifyFalseTrue::simplify(u);
    u = Flattening::flatten(u);
    ASS(!u->isClause());
    return static_cast<FormulaUnit*>(u);
  }

  /**
   * Perform inlining and return the result. If the resulting clause is a tautology,
   * return zero.
   */
  Unit* apply(Clause* cl)
  {
    CALL("PDInliner::PDef::apply(Clause*)");

    static LiteralStack lits;
    lits.reset();
    static Stack<Formula*> forms;
    forms.reset();

    bool modified = false;

    unsigned clen = cl->length();
    for(unsigned i=0; i<clen; i++) {
      Literal* lit = (*cl)[i];
      if(lit->functor()!=_pred) {
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

    Unit::InputType inp = Unit::getInputType(cl->inputType(), _defUnit->inputType());
    Inference* inf = new Inference2(Inference::PREDICATE_DEFINITION_UNFOLDING, cl, _defUnit);
    if(forms.isEmpty()) {
      return Clause::fromIterator(LiteralStack::Iterator(lits), inp, inf);
    }
    if(lits.isEmpty() && forms.size()==1) {
      return new FormulaUnit(forms.top(), inf, inp);
    }

    //build a disjunction of all we have (both formulas and literals)
    FormulaList* disj = 0;
    FormulaList::pushFromIterator(Stack<Formula*>::Iterator(forms), disj);
    LiteralStack::Iterator litIt(lits);
    while(litIt.hasNext()) {
      FormulaList::push(new AtomicFormula(litIt.next()), disj);
    }
    Formula* form = new JunctionFormula(OR, disj);
    FormulaUnit* res = new FormulaUnit(form, inf, inp);
    return fixFormula(res);
  }

  FormulaUnit* apply(FormulaUnit* unit)
  {
    CALL("PDInliner::PDef::apply(FormulaUnit*)");

    Formula* form = apply(1,unit->formula());
    if(form==unit->formula()) {
      return unit;
    }

    env.statistics->inlinedPredicateDefinitions++;

    Unit::InputType inp = Unit::getInputType(unit->inputType(), _defUnit->inputType());
    Inference* inf = new Inference2(Inference::PREDICATE_DEFINITION_UNFOLDING, unit, _defUnit);

    FormulaUnit* res = new FormulaUnit(form, inf, inp);
    return fixFormula(res);
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

  bool atomicBody(int polarity, Literal* l) { return getBody(polarity)->connective() == LITERAL; }
  bool constantBody(int polarity, Literal* l) {
    Connective con = getBody(polarity)->connective();
    return con==TRUE || con==FALSE;
  }


  Literal* atomicApply(int polarity, Literal* l)
  {
    CALL("PDInliner::PDef::atomicApply");
    ASS(atomicBody(polarity,l));

    Applicator apl(*this, l);
    Literal* body = getBody(polarity)->literal();
    Literal* res = SubstHelper::apply(body, apl);

    if(l->isPositive() != _lhs->isPositive()) {
      res = Literal::oppositeLiteral(res);
    }
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
    return negate ^ (getBody(polarity)->connective()==TRUE);
  }

  Formula* apply(int polarity, Literal* l)
  {
    CALL("PDInliner::PDef::apply(int,Literal*)");

    if(atomicBody(polarity, l)) {
      return new AtomicFormula(atomicApply(polarity, l));
    }

    Applicator apl(*this, l);
    Formula* body = getBody(polarity);
    Formula* res = SubstHelper::apply(body, apl);

    if(l->isPositive() != _lhs->isPositive()) {
      res = new NegatedFormula(res);
    }
    return res;
  }

  /**
   * Inline redicate definition into this definition.
   */
  void inlineDef(PDef* def)
  {
    CALL("PDInliner::PDef::inlineDef");

    LOG("Inlining "<<def->_defUnit->toString()<<" into "<<_defUnit->toString());

    FormulaUnit* newUnit = def->apply(_defUnit);
    assignUnit(newUnit);

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

    //add the predicates added by inlining into dependencies
    Set<unsigned>::Iterator depIt(def->_dependencies);
    while(depIt.hasNext()) {
      unsigned dep = depIt.next();
      LOG(" dep: "<<env.signature->predicateName(dep));
      registerDependentPred(dep);
    }
  }

  void registerDependentPred(unsigned depPred)
  {
    CALL("PDInliner::PDef::registerDependentPred");
    ASS(!_parent->_defs[depPred]); //we cannot depend on a defined predicate

    _parent->_dependent[depPred].insert(_pred);
    _dependencies.insert(depPred);
  }

  void assignUnit(FormulaUnit* unit)
  {
    CALL("PDInliner::PDef::assignUnit");

    LOG("AU:  "<<unit->toString());
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
    _predicateEquivalence = isPredicateEquivalence(unit, pred1, pred2);
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
    return _body;
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

  Connective con = form->connective();
  switch (con) {
  case LITERAL:
  {
    Literal* l=form->literal();
    if(l->functor()!=_pred) {
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
    Formula* newArg = apply(-polarity, form->qarg());
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

PDInliner::PDInliner(bool axiomsOnly)
 : _axiomsOnly(axiomsOnly)
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


void PDInliner::apply(UnitList*& units)
{
  CALL("PDInliner::apply");

  scanAndRemoveDefinitions(units);

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
  }
}

Unit* PDInliner::apply(Unit* u)
{
  CALL("PDInliner::apply");

  Stack<unsigned> preds;
  u->collectPredicates(preds);

  //make the list of predicates unique
  VirtualIterator<unsigned> uniquePredIt = pvi(
      getUniquePersistentIterator(Stack<unsigned>::Iterator(preds)) );
  preds.reset();
  preds.loadFromIterator(uniquePredIt);

  Unit* res = u;

  //apply definitions of predicates that appear in the unit
  while(res && preds.isNonEmpty()) {
    unsigned pred = preds.pop();
    if(!_defs[pred]) {
      //we don't have a definition for this predicate
      continue;
    }
    ASS_NEQ(pred, 0); //equality is never defined

    //if the unit becomes a tautology, u can be assigned zero here
    res = _defs[pred]->apply(res);
  }
  return res;
}

void PDInliner::scanAndRemoveDefinitions(UnitList*& units)
{
  CALL("PDInliner::scanAndRemoveDefinitions(UnitList*)");

  {
    UnitList::DelIterator it(units);
    while(it.hasNext()) {
      Unit* u = it.next();
      if(u->isClause()) {
	continue;
      }
      if(tryGetPredicateEquivalence(static_cast<FormulaUnit*>(u))) {
	it.del();
      }
    }
  }

  {
    UnitList::DelIterator it(units);
    while(it.hasNext()) {
      Unit* u = it.next();
      if(u->isClause()) {
	continue;
      }
      if(tryGetDef(static_cast<FormulaUnit*>(u))) {
	it.del();
      }
    }
  }
}

bool PDInliner::isEligible(FormulaUnit* u)
{
  CALL("PDInliner::isEligible");

  return !_axiomsOnly || u->inputType()==Unit::AXIOM;
}

bool PDInliner::tryGetPredicateEquivalence(FormulaUnit* unit)
{
  CALL("PDInliner::tryGetPredicateEquivalence");

  if(!isEligible(unit)) {
    return false;
  }

  unsigned pred1, pred2;
  if(!isPredicateEquivalence(unit, pred1, pred2)) {
    return false;
  }

  if(tryGetDef(unit)) {
    return true;
  }
  ASS(_defs[pred1]);
  ASS(_defs[pred2]);
  //we first get all predicate equivalences and other definitions only after that
  ASS(_defs[pred1]->predicateEquivalence());
  ASS(_defs[pred2]->predicateEquivalence());

  if(_defs[pred1]->tagretPredicate()==_defs[pred2]->tagretPredicate()) {
    //this equivalence is redundant
    return false;
  }
  unit = _defs[pred1]->apply(unit);
  ALWAYS(tryGetDef(unit));
  return true;
}

bool PDInliner::tryGetDef(FormulaUnit* unit)
{
  CALL("PDInliner::scan(FormulaUnit*)");

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

bool PDInliner::isPredicateEquivalence(FormulaUnit* unit, unsigned& pred1, unsigned& pred2)
{
  CALL("PDInliner::isPredicateEquivalence");

  Formula* f = unit->formula();
  if(f->connective()==FORALL) {
    f = f->qarg();
  }
  if(f->connective()!=IFF) {
    return false;
  }
  if(f->left()->connective()!=LITERAL || f->right()->connective()!=LITERAL) {
    return false;
  }
  Literal* l1 = f->left()->literal();
  Literal* l2 = f->right()->literal();

  if(l1->arity()!=l2->arity() || !isDefinitionHead(l1) || !isDefinitionHead(l2)) {
    return false;
  }
  if(!l1->containsAllVariablesOf(l2)) {
    return false;
  }
  pred1 = l1->functor();
  pred2 = l2->functor();
  return true;
}

/**
 * Return true if literal can act as a definition head (i.e. is not equality,
 * has only variable subterms, and these subterms are all distinct)
 */
bool PDInliner::isDefinitionHead(Literal* l)
{
  CALL("PDInliner::isDefinitionHead");

  if(l->isEquality()) {
    return false;
  }
  unsigned ar = l->arity();
  if(l->weight()!=ar+1 || l->getDistinctVars()!=ar) {
    return false;
  }
  return true;
}

bool PDInliner::tryGetDef(FormulaUnit* unit, Literal* lhs, Formula* rhs)
{
  CALL("PDInliner::tryGetDef");

  if(lhs->isEquality()) {
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

  LOGV(unit->toString());

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


}
