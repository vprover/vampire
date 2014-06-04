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

#define DEBUG_FORMULA_FIX 1

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

struct PDInliner::DefDep
{
  DefDep(PDInliner& parent, unsigned pred, DepSet* dependencies, FormulaUnit* def)
      : _parent(parent), _pred(pred), _def(def)
  {
    CALL("PDInliner::DefDep::DefDep");
    ASS_NEQ(pred, 0);

    initDependencies(dependencies);
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] DefDep created" << std::endl;
      env.out() << "[PP]   predicate: "<<env.signature->predicateName(pred)
              <<"  num: "<<pred << std::endl;
      env.out() << "[PP]   immediate dependencies: "<<*dependencies << std::endl;
      env.out() << "[PP]   formula: "<<*def << std::endl;
      env.out() << "[PP]   full dependencies: "<<*_dependencies << std::endl;
      env.endOutput();
    }
  }

  /**
   * Notify the definition object of a new definition of a
   * predicate appearing (possibly transitively) in its body.
   */
  void expandDependency(unsigned depPred)
  {
    CALL("PDInliner::DefDep::expandDependency");
    ASS(_dependencies->member(depPred));
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] expanding dependencies of "<<_pred
              <<" by "<<depPred << std::endl;      
      env.endOutput();
    }    

    DefDep* dObj = _parent._deps[depPred];
    ASS(dObj);
    DepSet* newDepSet = _dependencies->getUnion(dObj->_dependencies);
    DepSet* addedDep = newDepSet->subtract(_dependencies);
    DepSet::Iterator fdit(*addedDep);
    while(fdit.hasNext()) {
      unsigned d = fdit.next();
      _parent._dependent[d].push(_pred);
    }
    _dependencies = newDepSet;

  }

  DepSet* dependencies() const { return _dependencies; }
  FormulaUnit* defUnit() const { return _def; }
private:
  void initDependencies(DepSet* dependencies)
  {
    DepSet* fullDep = dependencies;
    DepSet::Iterator dit(*dependencies);
    while(dit.hasNext()) {
      unsigned d = dit.next();
      DefDep* dObj = _parent._deps[d];
      if(!dObj) {
	continue;
      }
      fullDep = fullDep->getUnion(dObj->_dependencies);
    }
    _dependencies = fullDep;

    DepSet::Iterator fdit(*fullDep);
    while(fdit.hasNext()) {
      unsigned d = fdit.next();
      _parent._dependent[d].push(_pred);
    }
   }


  PDInliner& _parent;
  unsigned _pred;
  FormulaUnit* _def;

  DepSet* _dependencies;
};

/**
 * Class representing a single predicate definition
 *
 * For in functions that take polarity as argument, the value can be -1, 0, 1.
 * Zero means "double" polarity - this occurrs e.g. inside equivalences.
 */
struct PDInliner::PDef
{
  PDef(PDInliner* parent, unsigned pred)
      : _parent(parent), _pred(pred), _asymDef(false)
  {}

public:
  Formula* applyAtomicForm(unsigned polarity, Formula* form, InliningState& state)
  {
    CALL("PDInliner::PDef::applyAtomicForm");
    ASS_EQ(form->connective(), LITERAL);

    Literal* l=form->literal();
    ASS_EQ(l->functor(), _pred);

    if(identity(polarity, l)) {
      return form;
    }
    if(atomicBody(polarity, l)) {
      Literal* newLit = atomicApply(polarity, l);
      if(newLit==l) {
	return form;
      }
      if(_defUnit) {
	state.premises.push(_defUnit);
      }
      return new AtomicFormula(newLit);
    }
    if(_defUnit) {
      state.premises.push(_defUnit);
    }
    Formula* res = apply(polarity, l);
    if(res->connective()==TRUE || res->connective()==FALSE) {
      state.needsConstantSimplification = true;
    }
    else {
      state.needsRectify |= _fixNeedsRect;
    }
    return res;
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
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] Lit inlining: "<<(*l)<<" --> "<<(*res) << std::endl;
      env.endOutput();
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
    bool res = negate ^ (getBody(polarity,l)->connective()==TRUE);
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] Lit inlining: "<<(*l)<<" --> "<<(res ? "$true" : "$false") << std::endl;
      env.endOutput();
    }
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
      res = Flattening::getFlattennedNegation(res);
    }
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "Lit inlining: "<<(*l)<<" --> "<<(*res) << std::endl;
      env.endOutput();
    }
    return res;
  }


  void assignUnit(FormulaUnit* unit)
  {
    CALL("PDInliner::PDef::assignUnit");

    _asymDef = false;

    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] inl: Definition from unit: "<<unit->toString() << std::endl;
      env.endOutput();
    }
    _defUnit = unit;
    Formula* f = unit->formula();
    if(f->connective()==FORALL) {
      f = f->qarg();
    }

    if(f->connective()==IFF) {
      if(f->left()->connective()==LITERAL && f->left()->literal()->functor()==_pred) {
	makeDef(f->left()->literal(), f->right());
      }
      else {
	ASS_EQ(f->right()->connective(),LITERAL);
	ASS_EQ(f->right()->literal()->functor(),_pred);
	makeDef(f->right()->literal(), f->left());
      }
    }
    else {
      ASS_EQ(f->connective(), LITERAL);
      ASS_EQ(f->literal()->functor(), _pred);
      makeDef(f->literal(), Formula::trueFormula());
    }
  }

  /**
   * Make the object into an asymmetric definition
   *
   * If some body argument is zero, the lhs is not transformed for that polarity.
   */
  void assignAsym(Literal* lhs, Formula* posBody, Formula* negBody, Formula* dblBody, FormulaUnit* premise)
  {
    CALL("PDInliner::PDef::assignAsym");
    ASS_EQ(lhs->functor(),_pred);

    _asymDef = true;

    //if shown needed by practice, we may add more precise fixes
    _fixNeedsRect = true;
    _fixNeedsSimpl = true;

    _defUnit = premise;
    _lhs = lhs;

    _posBody = posBody;
    _negBody = negBody;
    _dblBody = dblBody;

    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] inl: Asymmetric definition: " << toString() << std::endl;
      env.endOutput();
    }
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
    ASS(!_asymDef);

    _lhs = lhs;
    _body = body;

    if(_body->connective()==TRUE || _body->connective()==FALSE) {
      _fixNeedsRect = false;
      _fixNeedsSimpl = true;
    }
    else if(_body->connective()==LITERAL) {
      _fixNeedsRect = false;
      _fixNeedsSimpl = false;
    }
    else {
      bool hasQuant = false;
      SubformulaIterator sfit(_body);
      while(sfit.hasNext()) {
	Formula* sf = sfit.next();
	if(sf->connective()==FORALL || sf->connective()==EXISTS) {
	  hasQuant = true;
	  break;
	}
	//unshared literals can introduce variables inside through special terms, but these
	//should have been eliminated by now
	ASS(sf->connective()!=LITERAL || sf->literal()->shared());
      }

      _fixNeedsRect = hasQuant;
      _fixNeedsSimpl = false;
    }
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

  bool _asymDef;
  Formula* _posBody;
  Formula* _negBody;
  /** If @c _asymDef is true, contains replacement for occurrences inside equivalences or XORs */
  Formula* _dblBody;

  bool _fixNeedsRect;
  bool _fixNeedsSimpl;
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


PDInliner::PDInliner(bool axiomsOnly, bool nonGrowing)
 : _axiomsOnly(axiomsOnly), _nonGrowing(nonGrowing)
{
  CALL("PDInliner::PDInliner");

  _dependent.ensure(env.signature->predicates());
}

PDInliner::~PDInliner()
{
  CALL("PDInliner::~PDInliner");

  unsigned preds = env.signature->predicates();
  for(unsigned i=0; i<preds; i++) {
    ASS_EQ(_deps[i]==0, _defs[i]==0)
    if(_defs[i]) {
      delete _defs[i];
    }
    if(_deps[i]) {
      delete _deps[i];
    }
  }
}

Formula* PDInliner::apply(int polarity, Formula* form, InliningState& state)
{
  CALL("PDInliner::apply/3");

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] Apply all definitions to subformula "<<form->toString()
            <<" with polarity "<<polarity << std::endl;
    env.endOutput();
  }

  Connective con = form->connective();
  switch (con) {
  case LITERAL:
  {
    Literal* l=form->literal();
    unsigned pred = l->functor();
    if(!_defs[pred]) {
      return form;
    }
    Formula* res = _defs[pred]->applyAtomicForm(polarity, form, state);
    return res;
  }

  case AND:
  case OR: {
    FormulaList* resArgs = 0;
    bool modified = false;
    FormulaList::Iterator fs(form->args());
    while (fs.hasNext()) {
      Formula* arg = fs.next();
      ASS_NEQ(arg->connective(), con);
      Formula* newArg = apply(polarity, arg, state);
      if(arg!=newArg) {
	modified = true;
      }
      if(newArg->connective()==con) {
	FormulaList::pushFromIterator(FormulaList::Iterator(newArg->args()), resArgs);
      }
      else {
	FormulaList::push(newArg, resArgs);
      }
    }
    if(!modified) {
      resArgs->destroy();
      return form;
    }
    return new JunctionFormula(con, resArgs);
  }

  case IMP: {
    Formula* newLeft = apply(-polarity, form->left(), state);
    Formula* newRight = apply(polarity, form->right(), state);
    if(newLeft==form->left() && newRight==form->right()) {
      return form;
    }
    return new BinaryFormula(IMP, newLeft, newRight);
  }

  case NOT: {
    Formula* newArg = apply(-polarity, form->uarg(), state);
    //We assume the input formulas to be flattened and in such formulas
    //literals cannot be arguments to negations (as he negation will be
    //pushed into literals). Also, inlining cannot make a non-literal
    //become a literal.
    ASS_NEQ(newArg->connective(),LITERAL);
    if(newArg==form->uarg()) {
      return form;
    }
    if(newArg->connective()==NOT) {
      return newArg->uarg();
    }
    return new NegatedFormula(newArg);
  }

  case IFF:
  case XOR:{
    Formula* newLeft = apply(0, form->left(), state);
    Formula* newRight = apply(0, form->right(), state);
    if(newLeft==form->left() && newRight==form->right()) {
      return form;
    }
    return new BinaryFormula(con, newLeft, newRight);
  }

  case FORALL:
  case EXISTS:{
    Formula* newArg = apply(polarity, form->qarg(), state);
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

  bool modified = scanAndRemoveDefinitions(units, inlineOnlyEquivalences);

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] scan finished, now processing problem units" << std::endl;
    env.endOutput();
  }
  
  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    Unit* newUnit = apply(u);
    if(!newUnit->isClause() && static_cast<FormulaUnit*>(newUnit)->formula()->connective()==TRUE) {
      newUnit = 0;
    }
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

  if(u->isClause()) {
    return apply(static_cast<Clause*>(u));
  }
  else {
    return apply(static_cast<FormulaUnit*>(u));
  }
}

void PDInliner::getInferenceAndInputType(Unit* transformedUnit, InliningState& state, Inference*& inf, Unit::InputType& inp)
{
  CALL("PDInliner::getInferenceAndInputType");

  switch(state.premises.size()) {
  case 0:
    inp = transformedUnit->inputType();
    inf = new Inference1(Inference::PREDICATE_DEFINITION_UNFOLDING, transformedUnit);
    break;
  case 1:
  {
    Unit* prem = state.premises.top();
    inp = Unit::getInputType(transformedUnit->inputType(), prem->inputType());
    inf = new Inference2(Inference::PREDICATE_DEFINITION_UNFOLDING, transformedUnit, prem);
    break;
  }
  default:
  {
    UnitList* prems = 0;
    UnitList::pushFromIterator(getUniquePersistentIterator(UnitStack::Iterator(state.premises)), prems);
    UnitList::push(transformedUnit, prems);
    inp = Unit::getInputType(prems);
    inf = new InferenceMany(Inference::PREDICATE_DEFINITION_UNFOLDING, prems);
  }
  }
}

FormulaUnit* PDInliner::apply(FormulaUnit* unit)
{
  CALL("PDInliner::apply(FormulaUnit*)");

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] Inlining into "<<(*unit) << std::endl;
    env.endOutput();
  }
  
  static InliningState inlState;
  inlState.reset();

  Formula* form = apply(1, unit->formula(), inlState);
  if(form==unit->formula()) {
    return unit;
  }

  Unit::InputType inp;
  Inference* inf;
  getInferenceAndInputType(unit, inlState, inf, inp);

  FormulaUnit* res = new FormulaUnit(form, inf, inp);

  if(inlState.needsRectify) {
    res = Rectify::rectify(res);
  }
  if(inlState.needsConstantSimplification) {
    res = SimplifyFalseTrue::simplify(res);
    res = Flattening::flatten(res);
  }

#if DEBUG_FORMULA_FIX
  if(!inlState.needsRectify) {
    FormulaUnit* fu2 = Rectify::rectify(res);
    if(res!=fu2) {
	LOG("bug", "insufficient rectify check");
	LOG_UNIT("bug", res);
	LOG_UNIT("bug", fu2);
	ASSERTION_VIOLATION;
    }
  }
  if(!inlState.needsConstantSimplification) {
    FormulaUnit* fu2 = SimplifyFalseTrue::simplify(res);
    if(res!=fu2) {
	LOG("bug", "insufficient SimplifyFalseTrue check");
	LOG_UNIT("bug", res);
	LOG_UNIT("bug", fu2);
	ASSERTION_VIOLATION;
    }
  }
  FormulaUnit* fu2 = Flattening::flatten(res);
  if(res!=fu2) {
    LOG("bug", "insufficient built-in flattening");
    LOG_UNIT("bug", res);
    LOG_UNIT("bug", fu2);
    ASSERTION_VIOLATION;
  }
#endif

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] inl: Inlining into "<<(*unit)<<" gave "<<(*res) << std::endl;
    env.endOutput();
  }
  RSTAT_MCTR_INC("inl premises", inlState.premises.size()-1);

  return res;
}

/**
 * Perform inlining and return the result. If the resulting clause is a tautology,
 * return zero.
 */
Unit* PDInliner::apply(Clause* cl)
{
  CALL("PDInliner::apply");
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] Inlining into "<<(*cl) << std::endl;
    env.endOutput();
  }

  static InliningState inlState;
  inlState.reset();

  static LiteralStack lits;
  lits.reset();
  static Stack<Formula*> forms;
  forms.reset();

  bool modified = false;

  unsigned clen = cl->length();
  for(unsigned i=0; i<clen; i++) {
    Literal* lit = (*cl)[i];
    unsigned pred = lit->functor();
    PDef* defObj = _defs[pred];
    if(!defObj || defObj->identity(1, lit)) {
      lits.push(lit);
      continue;
    }
    if(defObj->_defUnit) {
      inlState.premises.push(defObj->_defUnit);
    }
    if(defObj->constantBody(1, lit)) {
      if(defObj->constantApply(1, lit)) {
	return 0; //tautology
      }
      //false literal -- we skip it
      modified = true;
    }
    else if(defObj->atomicBody(1, lit)) {
      Literal* newLit = defObj->atomicApply(1, lit);
      if(newLit!=lit) {
	modified = true;
      }
      lits.push(newLit);
    }
    else {
      modified = true;
      forms.push(defObj->apply(1, lit));
    }
  }

  if(!modified) {
    return cl;
  }

  Unit::InputType inp;
  Inference* inf;
  getInferenceAndInputType(cl, inlState, inf, inp);
  if(forms.isEmpty()) {
    Clause* res = Clause::fromIterator(LiteralStack::Iterator(lits), inp, inf);
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] inl: Inlining into "<<(*cl)<<" gave "<<(*res) << std::endl;
      env.endOutput();
    }
    return res;
  }
  FormulaUnit* res;
  if(lits.isEmpty() && forms.size()==1) {
    res = new FormulaUnit(forms.top(), inf, inp);
    res = Rectify::rectify(res);
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
    res = Rectify::rectify(res);
    res = Flattening::flatten(res);
  }
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] inl: Inlining into "<<(*cl)<<" gave "<<(*res) << std::endl;
    env.endOutput();
  }
  return res;
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
    prepareScannedDefs();
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
  prepareScannedDefs();
  return modified;
}

void PDInliner::prepareScannedDefs()
{
  CALL("PDInliner::prepareScannedDefs");

  unsigned predCnt = _dependent.size();

  Stack<unsigned> readyDefs;
  DArray<unsigned> unprocDepCnt;
#if VDEBUG
  unprocDepCnt.init(predCnt, 0);
#else
  unprocDepCnt.ensure(predCnt);
#endif

  unsigned waitingDefCnt = 0;

  for(unsigned i = 1; i<predCnt; i++) {
    DefDep* obj = _deps[i];
    if(!obj) {
      continue;
    }
    unsigned depCnt = 0;
    DepSet::Iterator dsit(*obj->dependencies());
    while(dsit.hasNext()) {
      unsigned depIdx = dsit.next();
      if(_deps[depIdx]) {
	depCnt++;
      }
    }
    if(depCnt==0) {
      readyDefs.push(i);
    }
    else {
      waitingDefCnt++;
      unprocDepCnt[i] = depCnt;
    }
  }

  while(readyDefs.isNonEmpty()) {
    unsigned dIdx = readyDefs.pop();
    DefDep* obj = _deps[dIdx];
    FormulaUnit* defUnit = obj->defUnit();
    FormulaUnit* applUnit = apply(defUnit);

    PDef* defObj = new PDef(this, dIdx);
    defObj->assignUnit(applUnit);
    _defs[dIdx] = defObj;

    Stack<unsigned>::ConstIterator dependentIt(_dependent[dIdx]);
    while(dependentIt.hasNext()) {
      unsigned dependentIdx = dependentIt.next();
      ASS(_deps[dependentIdx]); //only defined predicates can be dependent
      ASS_G(unprocDepCnt[dependentIdx], 0);
      unprocDepCnt[dependentIdx]--;
      if(unprocDepCnt[dependentIdx]==0) {
	readyDefs.push(dependentIdx);
	waitingDefCnt--;
      }
    }
  }
  ASS_EQ(waitingDefCnt,0);
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

  Formula* f1;
  Formula* f2;
  if(!PDUtils::isPredicateEquivalence(unit, f1, f2)) {
    return false;
  }

  Literal* l1 = f1->literal();
  Literal* l2 = f2->literal();

  if(tryGetDef(unit, l1, f2)) {
    return true;
  }
  if(tryGetDef(unit, l2, f1)) {
    return true;
  }
  return false;
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
  if(f->connective()==LITERAL && PDUtils::isDefinitionHead(f->literal())) {
    if(tryGetDef(unit, f->literal(), Formula::trueFormula())) {
      return true;
    }
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
  if(rhs->connective()==TRUE || rhs->connective()==FALSE) {
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

  if(!PDUtils::hasDefinitionShape(lhs, rhs)) {
    return false;
  }
  //Now we know that lhs has a predicate that can be defined (not a protected one)
  //and its arguments are distinct variables. Also that all unbound variables of
  //rhs occur in lhs and that the predicate of lhs doesn't occur in rhs.

  if(_nonGrowing && !isNonGrowingDef(lhs, rhs)) {
    return false;
  }

  unsigned defPred = lhs->functor();
  if(_deps[defPred]) {
    return false;
  }

  static Stack<unsigned> dependencies;
  dependencies.reset();
  rhs->collectPredicates(dependencies);
  makeUnique(dependencies);

  {
    Stack<unsigned>::Iterator depIt(dependencies);
    while(depIt.hasNext()) {
      unsigned depPred = depIt.next();
      if(depPred==0) {
	//we're not interested in equality
	depIt.del();
	continue;
      }
      if(!_deps[depPred]) {
	continue;
      }
      if(_deps[depPred]->dependencies()->member(defPred)) {
	return false;
      }
    }
  }

  DepSet* depSet = DepSet::getFromArray(dependencies.begin(), dependencies.size());

  DefDep* depRecord = new DefDep(*this, defPred, depSet, unit);

  _deps[defPred] = depRecord;

  Stack<unsigned>::Iterator dependentIt(_dependent[defPred]);
  while(dependentIt.hasNext()) {
    unsigned dep = dependentIt.next();
    ASS(_deps[dep]);
    _deps[dep]->expandDependency(defPred);
  }
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

  unsigned pred = lhs->functor();
  if(_defs[pred]) {
    return false; //predicate already defined
  }
  _defs[pred] = new PDef(this, pred);
  _defs[pred]->assignAsym(lhs, posBody, negBody, dblBody, premise);

  env.statistics->inlinedPredicateDefinitions++;
  return true;
}



}
