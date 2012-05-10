/**
 * @file EqualityPropagator.cpp
 * Implements class EqualityPropagator.
 */

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/MultiCounter.hpp"

#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Flattening.hpp"
#include "SimplifyFalseTrue.hpp"
#include "Statistics.hpp"

#include "EqualityPropagator.hpp"

namespace Shell
{

//////////////////////////////////////////////////
// EqualityPropagator::SingletonVariableRemover
//

class EqualityPropagator::SingletonVariableRemover
{
public:
  Formula* removeSingletonVars(Formula* f);

private:

  /**
   * If _quantifier is true, the entry stays for a variable quantified at
   * given point of the formula. Otherwise this entry signifies how has
   * the polarity of the formula changed at certain point of the formula
   * (the _polarity entry can be either -1 for negated polarity or 0 for
   * double polarity).
   */
  struct VarStackEntry {
    VarStackEntry(int polarity) : _quantifier(false), _polarity(polarity) {}
    VarStackEntry(bool existential, unsigned var) : _quantifier(true), _existential(existential), _var(var) {}

    VarStackEntry& operator=(const VarStackEntry& o)
    {
      _quantifier = o.quantifier();
      if(_quantifier) {
	_existential = o.existential();
	_var = o.var();
      }
      else {
	_polarity = o.polarity();
      }
      return *this;
    }

    VarStackEntry(const VarStackEntry& o) { *this = o; }

    bool quantifier() const { return _quantifier; }
    int polarity() const {
      CALL("EqualityPropagator::SingletonVariableRemover::VarStackEntry::polarity");
      ASS(!_quantifier);
      return _polarity;
    }
    bool existential() const {
      CALL("EqualityPropagator::SingletonVariableRemover::VarStackEntry::existential");
      ASS(_quantifier);
      return _existential;
    }
    unsigned var() const {
      CALL("EqualityPropagator::SingletonVariableRemover::VarStackEntry::var");
      ASS(_quantifier);
      return _var;
    }
  private:
    bool _quantifier;
    union {
      int _polarity; //if _quantifier false
      struct {	     //if _quantifier true
	bool _existential;
	unsigned _var;
      };
    };
  };

  void reset()
  {
    _varStack.reset();
    _singletonVars.reset();
    _removedVars.reset();
  }

  void collectSingletonVars(Formula* f);

  Formula* apply(Formula* form);
  Formula* apply(QuantifiedFormula* form);

  bool isRemovableEquality(Literal* l, bool& resultConstant);
  bool isRemovableVar(bool eqPolarity, unsigned v1, bool hasSecondVar, unsigned v2, bool& resultConstant);

  /**
   * Contains entries about the recursive descent into the formula.
   */
  Stack<VarStackEntry> _varStack;

  DHSet<unsigned> _singletonVars;
  DHSet<unsigned> _removedVars;
};

/**
 *
 * second variable might not be a singleton
 */
bool EqualityPropagator::SingletonVariableRemover::isRemovableVar(bool eqPolarity, unsigned v1,
    bool hasSecondVar, unsigned v2, bool& resultConstant)
{
  CALL("EqualityPropagator::SingletonVariableRemover::isRemovableVar");
  ASS(_singletonVars.find(v1));

  int pol = eqPolarity ? 1 : -1;
  Stack<VarStackEntry>::TopFirstIterator vsit(_varStack);
  while(vsit.hasNext()) {
    VarStackEntry vse = vsit.next();
    if(!vse.quantifier()) {
      pol*=vse.polarity();
      if(pol==0) {
	return false;
      }
      continue;
    }
    unsigned qvar = vse.var();
    if(qvar!=v1 && (!hasSecondVar || qvar!=v2)) {
      continue;
    }
    if(qvar==v2 && !_singletonVars.find(v2)) {
      return false;
    }
    if(vse.existential()!=(pol==1)) {
      return false;
    }
    resultConstant = eqPolarity;
    return true;
  }
  ASSERTION_VIOLATION; //each var must appear in the stack
}

bool EqualityPropagator::SingletonVariableRemover::isRemovableEquality(Literal* l, bool& resultConstant)
{
  CALL("EqualityPropagator::SingletonVariableRemover::isRemovableEquality");

  if(!l->isEquality()) {
    return false;
  }
  bool polarity = l->isPositive();
  TermList arg1 = *l->nthArgument(0);
  TermList arg2 = *l->nthArgument(1);

  if(!arg1.isVar() || !_singletonVars.find(arg1.var())) {
    swap(arg1,arg2);
  }
  if(!arg1.isVar() || !_singletonVars.find(arg1.var())) {
    return false;
  }

  bool hasTwoVars = arg2.isVar();

  if(!isRemovableVar(polarity, arg1.var(), hasTwoVars, hasTwoVars ? arg2.var() : 0, resultConstant)) {
    return false;
  }
  _removedVars.insert(arg1.var());
  if(arg2.isVar() && _singletonVars.find(arg2.var())) {
    _removedVars.insert(arg2.var());
  }
  return true;
}

Formula* EqualityPropagator::SingletonVariableRemover::apply(Formula* form)
{
  CALL("EqualityPropagator::SingletonVariableRemover::apply");

  Connective con = form->connective();
  switch (con) {
  case LITERAL:
  {
    Literal* l=form->literal();
    bool res;
    if(!isRemovableEquality(l, res)) {
      return form;
    }
    return new Formula(res);
  }

  case AND:
  case OR: {
    FormulaList* resArgs = 0;
    bool modified = false;
    FormulaList::Iterator fs(form->args());
    while (fs.hasNext()) {
      Formula* arg = fs.next();
      Formula* newArg = apply(arg);
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
    _varStack.push(VarStackEntry(-1));
    Formula* newLeft = apply(form->left());
    _varStack.pop();
    Formula* newRight = apply(form->right());
    if(newLeft==form->left() && newRight==form->right()) {
      return form;
    }
    return new BinaryFormula(IMP, newLeft, newRight);
  }

  case NOT: {
    _varStack.push(VarStackEntry(-1));
    Formula* newArg = apply(form->uarg());
    _varStack.pop();
    if(newArg==form->uarg()) {
      return form;
    }
    return new NegatedFormula(newArg);
  }

  case IFF:
  case XOR:{
    _varStack.push(VarStackEntry(0));
    Formula* newLeft = apply(form->left());
    Formula* newRight = apply(form->right());
    _varStack.pop();
    if(newLeft==form->left() && newRight==form->right()) {
      return form;
    }
    return new BinaryFormula(con, newLeft, newRight);
  }

  case FORALL:
  case EXISTS:
    return apply(static_cast<QuantifiedFormula*>(form));

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
    return 0;
#endif
  }
}

Formula* EqualityPropagator::SingletonVariableRemover::apply(QuantifiedFormula* form)
{
  CALL("EqualityPropagator::SingletonVariableRemover::apply(QuantifiedFormula*)");

  Connective con = form->connective();
  bool existential = con==EXISTS;

  size_t initDepth = _varStack.size();

  Formula::VarList* vars = form->vars();
  Formula::VarList::Iterator vit1(vars);
  while(vit1.hasNext()) {
    unsigned v = vit1.next();
    _varStack.push(VarStackEntry(existential, v));
  }

  Formula* newArg = apply(form->qarg());

  _varStack.truncate(initDepth);

  if(newArg==form->qarg()) {
    return form;
  }
  Formula::VarList* newVars = 0;
  Formula::VarList::Iterator vit2(vars);
  while(vit2.hasNext()) {
    unsigned v = vit2.next();
    if(!_removedVars.find(v)) {
      Formula::VarList::push(v, newVars);
    }
  }
  //for estetic reasons we want to keep the quantified
  //variables in the same order as in the original formula
  newVars = newVars->reverse();
  if(newVars) {

    return new QuantifiedFormula(con, newVars, newArg);
  }
  else {
    return newArg;
  }
}


void EqualityPropagator::SingletonVariableRemover::collectSingletonVars(Formula* f)
{
  CALL("EqualityPropagator::SingletonVariableRemover::collectSingletonVars");

  MultiCounter varCounter;
  SubformulaIterator sfit(f);
  while(sfit.hasNext()) {
    Formula* sf = sfit.next();
    if(sf->connective()!=LITERAL) {
      continue;
    }
    Literal* l = sf->literal();
    VariableIterator vit(l);
    while(vit.hasNext()) {
      varCounter.inc(vit.next().var());
    }
  }
  int lastCtr = varCounter.lastCounter();
  for(int i=0; i<=lastCtr; i++) {
    if(varCounter.get(i)==1) {
      _singletonVars.insert(i);
    }
  }
}

Formula* EqualityPropagator::SingletonVariableRemover::removeSingletonVars(Formula* f)
{
  CALL("EqualityPropagator::SingletonVariableRemover::removeSingletonVars");

  if(f->connective()==TRUE || f->connective()==FALSE) {
    return f;
  }

  reset();
  collectSingletonVars(f);
  Formula* res = apply(f);
  ASS(_varStack.isEmpty());
  if(res!=f) {
    res = SimplifyFalseTrue::simplify(res);
  }
  return res;
}

//////////////////////////
// EqualityPropagator
//

void EqualityPropagator::apply(Problem& prb)
{
  CALL("EqualityPropagator::apply(Problem&)");

  if(apply(prb.units())) {
    prb.invalidateByRemoval();
  }
}

bool EqualityPropagator::apply(UnitList*& units)
{
  CALL("EqualityPropagator::apply(UnilList*&)");

  bool modified = false;

  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Unit* u=uit.next();
    Unit* u2=apply(u);
    if(u!=u2) {
      ASS(u2);
      uit.replace(u2);
      modified = true;
    }
  }
  return modified;
}

Unit* EqualityPropagator::apply(Unit* u)
{
  CALL("EqualityPropagator::apply(Unit*)");

  if(u->isClause()) {
    return u;//for clauses the equality resolution with deletion rule does the same
  }
  return apply(static_cast<FormulaUnit*>(u));
}

FormulaUnit* EqualityPropagator::apply(FormulaUnit* u)
{
  CALL("EqualityPropagator::apply(FormulaUnit*)");
  CONDITIONAL_SCOPED_TRACE_TAG(_trace, "pp_ep")

  ASS(!u->isClause());
  LOG_UNIT("pp_ep_args",u);

  Formula* form = u->formula();
  Formula* newForm = applyTopLevel(form);

  if(form!=newForm) {
    env.statistics->propagatedEqualities++;
    LOG("pp_ep", "Equality propagator transformed\n  "<<(*form)<<" into\n  "<<(*newForm));
  }

  static SingletonVariableRemover svr;
  Formula* svrForm = svr.removeSingletonVars(newForm);

  if(newForm!=svrForm) {
    env.statistics->removedSingletonVariables++;
    LOG("pp_ep", "Singleton varible remover transformed\n  "<<(*newForm)<<" into\n  "<<(*svrForm));
  }

  if(form==svrForm) {
    return u;
  }
  Inference* inf = new Inference1(Inference::EQUALITY_PROPAGATION, u);
  FormulaUnit* newU = new FormulaUnit(svrForm, inf, u->inputType());

  return Flattening::flatten(newU);
}

Formula* EqualityPropagator::applyTopLevel(Formula* form)
{
  CALL("EqualityPropagator::applyTopLevel");

  ASS(_vars.isEmpty());
  ASS(_varDepths.isEmpty());
  ASS(_boundVars.isEmpty());
  ASS(_varBindings.isEmpty());

  if(form->connective()==TRUE || form->connective()==FALSE) {
    return form;
  }

  Formula* newForm = apply(form);
  return newForm;
}

Formula* EqualityPropagator::apply(Formula* form)
{
  CALL("EqualityPropagator::apply(Formula*)");

  Connective con = form->connective();
  switch (con) {
  case LITERAL:
  {
    Literal* l = form->literal();
    Literal* newLit = apply(l);
    if(newLit==l) {
      return form;
    }
    return new AtomicFormula(newLit);
  }

  case AND:
  case OR:
    return apply(static_cast<JunctionFormula*>(form));

  case IMP: {
    unsigned initBindCnt = _boundVars.size();
    Formula* newLeft = apply(form->left());
    collectResolvableBindings(newLeft, true);

    Formula* newRight = apply(form->right());

    undoBindings(initBindCnt);

    if(newLeft==form->left() && newRight==form->right()) {
      return form;
    }
    return new BinaryFormula(IMP, newLeft, newRight);
  }

  case NOT: {
    Formula* newArg = apply(form->uarg());
    if(newArg==form->uarg()) {
      return form;
    }
    return new NegatedFormula(newArg);
  }

  case IFF:
  case XOR:{
    Formula* newLeft = apply(form->left());
    Formula* newRight = apply(form->right());
    if(newLeft==form->left() && newRight==form->right()) {
      return form;
    }
    return new BinaryFormula(con, newLeft, newRight);
  }

  case FORALL:
  case EXISTS:
    return apply(static_cast<QuantifiedFormula*>(form));

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
    return 0;
#endif
  }
}

TermList EqualityPropagator::apply(unsigned var)
{
  CALL("EqualityPropagator::apply(unsigned)");

  TermList res;
  if(!_varBindings.find(var, res)) {
    res = TermList(var, false);
  }
  return res;
}

Literal* EqualityPropagator::apply(Literal* l)
{
  CALL("EqualityPropagator::apply(Literal*)");

  return SubstHelper::apply(l, *this);
}

/**
 * Collect bindings from formula @c form.
 *
 * The bindings have been collected from a formula must not
 * be applied to the formula itself.
 */
void EqualityPropagator::collectResolvableBindings(Formula* form, bool negated)
{
  CALL("EqualityPropagator::collectResolvableBindings");

  while(form->connective()==NOT) {
    negated = !negated;
    form = form->uarg();
  }

  if( (negated && form->connective()==AND) || (!negated && form->connective()==OR) ) {
    FormulaList::Iterator fit(form->args());
    while(fit.hasNext()) {
      collectResolvableBindings(fit.next(), negated);
    }
    return;
  }

  if(form->connective()!=LITERAL) {
    return;
  }
  Literal* l = form->literal();
  if(!l->isEquality() || l->isPositive()!=negated) {
    return;
  }
  TermList arg1 = *l->nthArgument(0);
  TermList arg2 = *l->nthArgument(1);
  if(!arg1.isVar()) {
    swap(arg1,arg2);
  }
  if(!arg1.isVar() || arg1==arg2) {
    return;
  }
  if(arg2.isVar() && _varDepths.get(arg1.var())<_varDepths.get(arg2.var())) {
    swap(arg1,arg2);
  }
  if(arg2.isTerm() && arg2.term()->weight()>1) {
    return; //we want to avoid exponential explosion
  }
  unsigned bv = arg1.var();
  if(_varBindings.insert(bv, arg2)) {
    _boundVars.push(bv);
  }
}

void EqualityPropagator::undoBindings(unsigned remaining)
{
  CALL("EqualityPropagator::undoBindings");

  while(_boundVars.size()>remaining) {
    unsigned v = _boundVars.pop();
    _varBindings.remove(v);
  }
  ASS_EQ(_boundVars.size(),remaining);
}

Formula* EqualityPropagator::apply(JunctionFormula* form)
{
  CALL("EqualityPropagator::apply(JunctionFormula*)");

  unsigned initBindingCnt = _boundVars.size();

  bool negated = form->connective()==AND;

  Stack<Formula*> postponed;
  postponed.reset();

  bool modified = false;
  FormulaList* resArgs = 0;
  FormulaList::Iterator fs(form->args());
  while (fs.hasNext()) {
    Formula* arg = fs.next();

    Formula* newArg = apply(arg);
    if(arg!=newArg) {
      modified = true;
    }

    unsigned bc0 = _boundVars.size();
    collectResolvableBindings(newArg, negated);
    if(bc0==_boundVars.size()) {
      //we didn't extract any equalities on variables from this
      //part, so we may process it once again, when we got all
      //the equalities from other arguments
      postponed.push(newArg);
    }
    else {
      FormulaList::push(newArg, resArgs);
    }
  }

  if(initBindingCnt==_boundVars.size()) {
    ASS_EQ(resArgs,0);
    if(!modified) {
      return form;
    }
    //we didn't add any bindings, so the initial apply() call is enough
    FormulaList::pushFromIterator(Stack<Formula*>::Iterator(postponed), resArgs);
  }
  else {
    while(postponed.isNonEmpty()) {
      Formula* arg = postponed.pop();
      Formula* newArg = apply(arg);
      if(arg!=newArg) {
        modified = true;
      }
      FormulaList::push(newArg, resArgs);
    }
  }

  undoBindings(initBindingCnt);

  if(!modified) {
    resArgs->destroy();
    return form;
  }
  ASS_EQ(resArgs->length(), form->args()->length());
  return new JunctionFormula(form->connective(), resArgs);
}

Formula* EqualityPropagator::apply(QuantifiedFormula* form)
{
  CALL("EqualityPropagator::apply(QuantifiedFormula*)");

  unsigned initDepth = _vars.size();
  Formula::VarList* vars = form->vars();
  Formula::VarList::Iterator vit(vars);
  while(vit.hasNext()) {
    unsigned v = vit.next();
    ALWAYS(_varDepths.insert(v, _vars.size())); //we assume rectified formulas
    _vars.push(v);
  }

  Formula* newArg = apply(form->qarg());

  while(_vars.size()>initDepth) {
    unsigned v = _vars.pop();
    _varDepths.remove(v);
  }
  ASS_EQ(_vars.size(),initDepth);

  if(newArg==form->qarg()) {
    return form;
  }
  Formula::VarList* newVars = vars->copy();
  return new QuantifiedFormula(form->connective(), newVars, newArg);
}

}
