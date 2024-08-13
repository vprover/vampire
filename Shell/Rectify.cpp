/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Rectify.cpp
 * Implements (static) class Rectify for the rectification inference rule.
 * @since 21/12/2003 Manchester
 * @since 23/01/2004 Manchester, changed to use non-static objects
 */

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Recycled.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Indexing/TermSharing.hpp"

#include "Rectify.hpp"

using namespace std;
using namespace Lib;
using namespace Shell;

bool Rectify::Renaming::tryGetBoundAndMarkUsed (int var,int& boundTo) const
{
  if ((unsigned)var >= _capacity) {
    return false;
  }
  VarUsageTrackingList* vs = _array[var];
  if (VarUsageTrackingList::isEmpty(vs)) {
    return false;
  }
  boundTo = vs->head().first;
  vs->headPtr()->second = true;
  return true;
} // Rectify::bound

Rectify::VarWithUsageInfo Rectify::Renaming::getBoundAndUsage(int var) const
{
  ASS_L((unsigned)var,_capacity);

  VarUsageTrackingList* vs = _array[var];
  ASS(VarUsageTrackingList::isNonEmpty(vs));
  return vs->head();
}

/**
 * Rectify the formula from this unit. If the input type of this unit
 * contains free variables, then ask Signature::sig to create an answer
 * atom.
 *
 * @since 23/01/2004 Manchester, changed to use non-static objects
 * @since 06/06/2007 Manchester, changed to use new datastructures
 */
FormulaUnit* Rectify::rectify (FormulaUnit* unit0, bool removeUnusedVars)
{
  ASS(!unit0->isClause());

  FormulaUnit* unit = unit0;

  Formula* f = unit->formula();
  Rectify rect;
  rect._removeUnusedVars = removeUnusedVars;
  Formula* g = rect.rectify(f);

  VList* vars = rect._free;

  if (f != g) {
    unit = new FormulaUnit(g,FormulaTransformation(InferenceRule::RECTIFY,unit));
  }

  if (VList::isNonEmpty(vars)) {
    //TODO do we know the sorts of vars?
    unit = new FormulaUnit(new QuantifiedFormula(FORALL,vars,0,g),FormulaTransformation(InferenceRule::CLOSURE,unit));
  }
  return unit;
} // Rectify::rectify (Unit& unit)

/**
 * Rectify formulas in @c units
 */
void Rectify::rectify(UnitList*& units)
{
  UnitList::DelIterator us(units);
  while (us.hasNext()) {
    Unit* u = us.next();
    if(u->isClause()) {
      continue;
    }
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    FormulaUnit* v = rectify(fu);
    if (v != fu) {
	us.replace(v);
    }
  }
}

/**
 * Destroy all renaming lists.
 * @since 07/06/2007 Manchester
 */
Rectify::Renaming::~Renaming ()
{
  for (int i = _capacity-1;i >= 0;i--) {
    VarUsageTrackingList::destroy(_array[i]);
    _array[i] = 0;
  }
} // Renaming::~Renaming



/**
 * Rectify a special term
 */
Term* Rectify::rectifySpecialTerm(Term* t)
{
  Term::SpecialTermData* sd = t->getSpecialData();
  switch(t->specialFunctor()) {
  case SpecialFunctor::ITE:
  {
    ASS_EQ(t->arity(),2);
    Formula* c = rectify(sd->getCondition());
    TermList th = rectify(*t->nthArgument(0));
    TermList el = rectify(*t->nthArgument(1));
    TermList sort = rectify(sd->getSort());
    if(c==sd->getCondition() && th==*t->nthArgument(0) && el==*t->nthArgument(1) && sort==sd->getSort()) {
	return t;
    }
    return Term::createITE(c, th, el, sort);
  }
  case SpecialFunctor::LET:
  {
    ASS_EQ(t->arity(),1);

    bindVars(sd->getVariables());
    TermList binding = rectify(sd->getBinding());
    /**
     * We don't need to remove unused variables from the body of a functions,
     * otherwise the rectified list of variables might not fix the arity of the
     * let functor. So, temporarily disable _removeUnusedVars;
     */
    bool removeUnusedVars = _removeUnusedVars;
    _removeUnusedVars = false;
    VList* variables = rectifyBoundVars(sd->getVariables());
    _removeUnusedVars = removeUnusedVars; // restore the status quo
    unbindVars(sd->getVariables());

    ASS_EQ(VList::length(variables),VList::length(sd->getVariables()));

    TermList contents = rectify(*t->nthArgument(0));
    TermList sort = rectify(sd->getSort());
    if (sd->getVariables() == variables && binding == sd->getBinding() && 
        contents == *t->nthArgument(0) && sort == sd->getSort()) {
      return t;
    }
    return Term::createLet(sd->getFunctor(), variables, binding, contents, sort);
  }
  case SpecialFunctor::LET_TUPLE:
  {
    ASS_EQ(t->arity(),1);

    TermList binding = rectify(sd->getBinding());
    TermList contents = rectify(*t->nthArgument(0));
    TermList sort = rectify(sd->getSort());

    if (binding == sd->getBinding() && contents == *t->nthArgument(0) && sort == sd->getSort()) {
      return t;
    }
    return Term::createTupleLet(sd->getFunctor(), sd->getTupleSymbols(), binding, contents, sort);
  } 
  case SpecialFunctor::FORMULA:
  {
    ASS_EQ(t->arity(),0);
    Formula* orig = rectify(sd->getFormula());
    if(orig==sd->getFormula()) {
      return t;
    }
    return Term::createFormula(orig);
  }
  case SpecialFunctor::LAMBDA:
  {
    ASS_EQ(t->arity(),0);
    bindVars(sd->getLambdaVars());
    bool modified = false;
    TermList lambdaTerm = rectify(sd->getLambdaExp());
    TermList lambdaTermS = rectify(sd->getLambdaExpSort());
    if(lambdaTerm != sd->getLambdaExp() || lambdaTermS != sd->getLambdaExpSort())
    { modified = true; }
    /**
     * We don't want to remove unused variables from the variable list,
     * ^[X].exp is not equivalent to exp.
     */
    bool removeUnusedVars = _removeUnusedVars;
    _removeUnusedVars = false;
    VList* vs = rectifyBoundVars(sd->getLambdaVars());
    SList* sorts = sd->getLambdaVarSorts();
    SList* rectifiedSorts = SList::empty();
    SList::Iterator slit(sorts);
    while(slit.hasNext()){
      TermList sort = slit.next();
      TermList rectifiedSort = rectify(sort);    
      if(sort != rectifiedSort){
        modified = true;
      }
      rectifiedSorts = SList::addLast(rectifiedSorts, rectifiedSort); // careful: quadratic complexity
    }
    _removeUnusedVars = removeUnusedVars; // restore the status quo
    unbindVars(sd->getLambdaVars());
    if (vs == sd->getLambdaVars() && !modified) {
      return t;
    }
    return Term::createLambda(lambdaTerm, vs, rectifiedSorts, lambdaTermS);   
  }
  case SpecialFunctor::TUPLE:
  {
    ASS_EQ(t->arity(),0);
    Term* rectifiedTupleTerm = rectify(sd->getTupleTerm());
    if (rectifiedTupleTerm == sd->getTupleTerm()) {
      return t;
    }
    return Term::createTuple(rectifiedTupleTerm);
  }
  case SpecialFunctor::MATCH: {
    DArray<TermList> terms(t->arity());
    bool unchanged = true;
    for (unsigned i = 0; i < t->arity(); i++) {
      terms[i] = rectify(*t->nthArgument(i));
      unchanged = unchanged && (terms[i] == *t->nthArgument(i));
    }
    auto sort = rectify(sd->getSort());
    auto matchedSort = rectify(sd->getMatchedSort());

    if (unchanged && sort == sd->getSort() && matchedSort == sd->getMatchedSort()) {
      return t;
    }
    return Term::createMatch(sort, matchedSort, t->arity(), terms.begin());
  }
  }
  ASSERTION_VIOLATION;
}

/**
 * Rectify a compound term.
 * @since 01/11/2005 Bellevue
 * @since 04/06/2007 Frankfurt Airport, changed to new datastructures
 */
Term* Rectify::rectify (Term* t)
{
  if (t->shared() && t->ground()) {
    return t;
  }

  if(t->isSpecial()) {
    return rectifySpecialTerm(t);
  }

  Recycled<Stack<TermList>> args;
  for (auto a : anyArgIter(t)) {
    args->push(rectify(a));
  }
  if (t->isSort()) {
    return AtomicSort::create(static_cast<AtomicSort*>(t), args->begin());
  } else if (t->isLiteral()) {
    return Literal::create(static_cast<Literal*>(t), args->begin());
  } else {
    return Term::create(t, args->begin());
  }
} // Rectify::rectify (Term*)

SList* Rectify::rectifySortList(SList* from, bool& modified)
{
  modified = false;
  SList* to = SList::empty();
  SList::Iterator slit(from);
  while(slit.hasNext()){
    TermList sort = slit.next();
    TermList rectifiedSort = rectify(sort);    
    if(sort != rectifiedSort){
      modified = true;
    }
    SList::addLast(to, rectifiedSort); // careful: quadratic complexity
  }
  return to;
}

Literal* Rectify::rectifyShared(Literal* lit)
{
  ASS(lit->shared());

  return SubstHelper::apply(lit, *this);
}

/**
 * Rectify a literal.
 * @since 24/03/2008 Torrevieja
 */
Literal* Rectify::rectify (Literal* l)
{
  if (l->shared()) {
    if(l->ground()) {
      return l;
    }
  }


  if (l->isTwoVarEquality()) {
    constexpr unsigned arity = 3;
    TermList args[arity];
    bool changed = Rectify::rectify(
        /* from */ [&](auto i) { return i == 0 ? SortHelper::getEqualityArgumentSort(l)
                                               : *l->nthArgument(i - 1); },
        /* to */ [&](auto i) -> TermList& { return args[i]; },
        /* cnt */ arity);
    return changed ? Literal::createEquality(l->polarity(), args[1], args[2], args[0]) : l;
  } else {
    Recycled<DArray<TermList>> args;
    args->ensure(l->arity());
    bool changed = Rectify::rectify(
        /* from */ [&](auto i) { return *l->nthArgument(i); },
        /* to */ [&](auto i) -> TermList& { return (*args)[i]; },
        /* cnt */ l->arity());
    return !changed ? l : Literal::create(l->functor(), l->arity(), l->polarity(), l->commutative(), 
                       args->begin());
  }
} // Rectify::rectify (Literal*)

/** 
 * Rectifies a list of `TermList`s. Both From and To are meant to be closures that can be called with an index and return a TermList.
 * Rectification procededs as follows:
 * ```
 * to(0) = rectify from(0)
 * to(1) = rectify from(1)
 * ...
 * to(cnt - 1) = rectify from(cnt - 1)
 * ```
 * This generalization is needed for properly rectfiying equalities, which don't have the equality sort stored as a usual term argument.
 * The "default use" of this function would be
 * ```
 * Literal* input = ...;
 * bool changed = Rectify::rectify(
 *      [&](auto i) { return *input->nthArgument(i); },
 *      [&](auto i) -> TermList& { return (*output)[i]; },
 *      input->arity());
 * ```
 * Returns true if the list has changed.
 */
template<class From, class To>
bool Rectify::rectify(From from, To to, unsigned cnt)
{
  bool changed = false;
  for (auto i : range(0, cnt)) {
    if (from(i).isVar()) {
      int v = from(i).var();
      int newV = rectifyVar(v);
      to(i) = TermList::var(newV);
      if (v != newV) { // rename variable to itself
        changed = true;
      }
    }
    else { // from is not a variable
      Term* f = from(i).term();
      Term* t = rectify(f);
      to(i) = TermList(t);
      if (f != t) {
        changed = true;
      }
    }
  }
  return changed;
} // Rectify::rectify (TermList*,...)

/**
 * Rectify variable @b v and return the result
 */
unsigned Rectify::rectifyVar(unsigned v)
{
  int newV;
  if (! _renaming.tryGetBoundAndMarkUsed(v,newV)) {
    newV = _renaming.bind(v);
    VList::push(newV,_free);
  }
  return newV;
}


/**
 * Rectify term @b t
 */
TermList Rectify::rectify(TermList t)
{
  if(t.isTerm()) {
    return TermList(rectify(t.term()));
  }
  ASS(t.isOrdinaryVar());
  return TermList(rectifyVar(t.var()), false);
}

/**
 * Rectify a formula.
 *
 * @param f the formula
 *
 * @since 27/06/2002 Manchester
 * @since 30/08/2002 Torrevieja, changed
 * @since 16/01/2004 Manchester, changed to use bound variables
 * @since 23/01/2004 Manchester, changed to use non-static objects
 * @since 11/12/2004 Manchester, true and false added
 * @since 04/07/2007 Frankfurt Airport, changed to new data structures
 */
Formula* Rectify::rectify (Formula* f)
{
  switch (f->connective()) {
  case LITERAL: 
  {
    Literal* lit = rectify(f->literal());
    return lit == f->literal() ? f : new AtomicFormula(lit);
  }

  case AND: 
  case OR: 
  {
    FormulaList* newArgs = rectify(f->args());
    if (newArgs == f->args()) {
      return f;
    }
    return new JunctionFormula(f->connective(), newArgs);
  }

  case IMP: 
  case IFF: 
  case XOR:
  {
    Formula* l = rectify(f->left());
    Formula* r = rectify(f->right());
    if (l == f->left() && r == f->right()) {
      return f;
    }
    return new BinaryFormula(f->connective(), l, r);
  }

  case NOT:
  {
    Formula* arg = rectify(f->uarg());
    if (f->uarg() == arg) {
      return f;
    }
    return new NegatedFormula(arg);
  }

  case FORALL: 
  case EXISTS:
  {
    bindVars(f->vars());
    Formula* arg = rectify(f->qarg());
    VList* vs = rectifyBoundVars(f->vars());
    unbindVars(f->vars());
    if (vs == f->vars() && arg == f->qarg()) {
      return f;
    }
    if(VList::isEmpty(vs)) {
      return arg;
    }
    //TODO should update the sorts from f->sorts() wrt to updated vs
    //     or is the rectification just renaming, if so f->sorts can 
    //     just be reused
    return new QuantifiedFormula(f->connective(),vs,0,arg);
  }

  case TRUE:
  case FALSE:
    return f;

  case BOOL_TERM:
     return new BoolTermFormula(rectify(f->getBooleanTerm()));

  case NAME:
  case NOCONN:
    ASSERTION_VIOLATION;
  }

  ASSERTION_VIOLATION;
} // Rectify::rectify (Formula*)

/**
 * Undo the last binding for variable var.
 * @since 07/06/2007 Manchester
 */
void Rectify::Renaming::undoBinding (unsigned var)
{
  ASS(var < _capacity);

  VarUsageTrackingList::pop(_array[var]);
} // Rectify::Renaming::undoBinding

/**
 * Bind var to a new variable and return the new variable.
 * @since 07/06/2007 Manchester
 */
unsigned Rectify::Renaming::bind (unsigned var)
{
  unsigned result = _nextVar++;

  VarUsageTrackingList::push(make_pair(result,false), get(var));

  return result;
} // Rectify::Renaming::bind


/**
 * Add fresh bindings to a list of variables
 */
void Rectify::bindVars(VList* vs)
{
  VList::Iterator vit(vs);
  while(vit.hasNext()) {
    unsigned v = vit.next();
    _renaming.bind(v);
  }
}

/**
 * Undo bindings to variables of a list
 */
void Rectify::unbindVars(VList* vs)
{
  VList::Iterator vit(vs);
  while(vit.hasNext()) {
    unsigned v = vit.next();
    _renaming.undoBinding(v);
  }
}

/**
 * Rectify a list of variables.
 *
 * @param vs the list to rectify
 */
VList* Rectify::rectifyBoundVars (VList* vs)
{
  if (VList::isEmpty(vs)) {
    return vs;
  }

  Stack<VList*> args;
  while (VList::isNonEmpty(vs)) {
    args.push(vs);
    vs = vs->tail();
  }

  VList* res = VList::empty();

  DHSet<int> seen;
  while (args.isNonEmpty()) {
    vs = args.pop();

    VList* vtail = vs->tail();
    VList* ws = res; // = rectifyBoundVars(vtail);

    int v = vs->head();

    // each variable mentioned only once per quantifier!
    if (!seen.insert(v)) {
      continue;
    }

    int w;
    VarWithUsageInfo wWithUsg = _renaming.getBoundAndUsage(v);
    if (wWithUsg.second || !_removeUnusedVars) {
      w = wWithUsg.first;

      if (v == w && vtail == ws) {
        res = vs;
      } else {
        res = VList::cons(w,ws);
      }
    }
    // else nothing, because "else" means dropping the variable from the list and returning ws, but res == ws already ...
  }

  return res;
} // Rectify::rectify(const VarList& ...)


/**
 * Rectify a list of formulas.
 * @since 08/06/2007 Manchester
 */
FormulaList* Rectify::rectify (FormulaList* fs)
{
  Recycled<Stack<FormulaList*>> els;

  FormulaList* el = fs;
  while(el) {
    els->push(el);
    el = el->tail();
  }

  FormulaList* res = 0;

  bool modified = false;
  while(els->isNonEmpty()) {
    FormulaList* el = els->pop();
    Formula* f = el->head();
    Formula* g = rectify(f);
    if(!modified && f!=g) {
      modified = true;
    }
    if(modified) {
      FormulaList::push(g, res);
    }
    else {
      res = el;
    }
  }

  return res;
} // Rectify::rectify(FormulaList*)

/**
 * Fill all values by zeros.
 * @since 13/01/2008 Manchester
 */
void Rectify::Renaming::fillInterval (size_t start,size_t end)
{
  for (unsigned i = start;i < end;i++) {
    _array[i] = 0;
  }
} // fillInterval
