/**
 * @file PDInliner.cpp
 * Implements class PDInliner.
 */

#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/MultiCounter.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "PDInliner.hpp"

namespace Shell
{

struct PDInliner::Applicator
{
  Applicator(PDef& parent, Literal* lit);

  TermList apply(unsigned var) const
  {
    CALL("PDInliner::Applicator::apply");
    return _map.get(var);
  }

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
    return new FormulaUnit(form, inf, inp);
  }

  /**
   * If the current definition can be inlined, perform inlining and return
   * the result. Otherwise return zero.
   */
  FormulaUnit* apply(FormulaUnit*)
  {
    CALL("PDInliner::PDef::apply(FormulaUnit*)");

    NOT_IMPLEMENTED;
  }

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
      registerDependentPred(depIt.next());
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
}



PDInliner::PDInliner()
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

  scan(units);

  NOT_IMPLEMENTED;
}


void PDInliner::scan(UnitList* units)
{
  CALL("PDInliner::scan(UnitList*)");

  UnitList::Iterator it(units);
  while(it.hasNext()) {
    Unit* u = it.next();
    if(u->isClause()) {
      continue;
    }
    scan(static_cast<FormulaUnit*>(u));
  }
}

void PDInliner::scan(FormulaUnit* unit)
{
  CALL("PDInliner::scan(FormulaUnit*)");

  Formula* f = unit->formula();
  if(f->connective()==FORALL) {
    f = f->qarg();
  }
  if(f->connective()!=IFF) {
    return;
  }
  if(f->left()->connective()==LITERAL) {
    if(tryGetDef(unit, f->left()->literal(), f->right())) {
      return;
    }
  }
  if(f->right()->connective()==LITERAL) {
    tryGetDef(unit, f->right()->literal(), f->left());
  }
}

bool PDInliner::tryGetDef(Unit* unit, Literal* lhs, Formula* rhs)
{
  CALL("PDInliner::tryGetDef");

  if(lhs->isEquality()) {
    return false;
  }

  unsigned defPred = lhs->functor();
  if(_defs[defPred]) {
    //there already is one predicate definition
    return false;
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

    if(_dependent[litPred].contains(defPred)) {
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

  PDef* def = new PDef(this, defPred);
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


}
