/**
 * @file Rectify.cpp
 * Implements (static) class Rectify for the rectification inference rule.
 * @since 21/12/2003 Manchester
 * @since 23/01/2004 Manchester, changed to use non-static objects
 */

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Recycler.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Indexing/TermSharing.hpp"

#include "VarManager.hpp"

#include "Rectify.hpp"

using namespace Shell;

bool Rectify::Renaming::bound (int var,int& boundTo) const
{
  CALL("Rectify::Renaming::bound");

  if ((unsigned)var >= _capacity) {
    return false;
  }
  VarList* vs = _array[var];
  if (vs->isEmpty()) {
    return false;
  }
  boundTo = vs->head();
  return true;
} // Rectify::bound

/**
 * Rectify the formula from this unit. If the input type of this unit
 * contains free variables, then ask Signature::sig to create an answer
 * atom.
 * 
 * @since 23/01/2004 Manchester, changed to use non-static objects
 * @since 06/06/2007 Manchester, changed to use new datastructures
 */
Unit* Rectify::rectify (Unit* unit)
{
  CALL("Rectify::rectify (Unit*...)");
  ASS(!unit->isClause());

  Formula* f = static_cast<FormulaUnit*>(unit)->formula();
  Rectify rect;
  Formula* g = rect.rectify(f);

  VarList* vars = rect._free;

  if (f != g) {
    unit = new FormulaUnit(g,
			   new Inference1(Inference::RECTIFY,unit),
			   unit->inputType());
  }

  if (vars->isNonEmpty()) {
    unit = new FormulaUnit(new QuantifiedFormula(FORALL,vars,g),
			   new Inference1(Inference::CLOSURE,unit),
			   unit->inputType());
  }
  return unit;
} // Rectify::rectify (Unit& unit)

/**
 * Destroy all renaming lists.
 * @since 07/06/2007 Manchester
 */
Rectify::Renaming::~Renaming ()
{
  CALL("Rectify::Renaming::~Renaming");

  for (int i = _capacity-1;i >= 0;i--) {
    _array[i]->destroy();
    _array[i] = 0;
  }

  if(_used) {
    Recycler::release(_used);
  }
} // Renaming::~Renaming

/**
 * Rectify a compound term.
 * @since 01/11/2005 Bellevue
 * @since 04/06/2007 Frankfurt Airport, changed to new datastructures
 */
Term* Rectify::rectify (Term* t)
{
  CALL("Rectify::rectify(Term*)");

  if (t->shared() && t->ground()) {
    return t;
  }

  if(t->isSpecial()) {
    Term::SpecialTermData* sd = t->getSpecialData();
    switch(t->functor()) {
    case Term::SF_TERM_ITE:
    {
      ASS_EQ(t->arity(),2);
      Formula* c = rectify(sd->getCondition());
      TermList th = rectify(*t->nthArgument(0));
      TermList el = rectify(*t->nthArgument(1));
      if(c==sd->getCondition() && th==*t->nthArgument(0) && el==*t->nthArgument(1)) {
	return t;
      }
      return Term::createTermITE(c, th, el);
    }
    case Term::SF_LET_FORMULA_IN_TERM:
    {
      ASS_EQ(t->arity(),1);
      Literal* orig = sd->getLhsLiteral();
      Formula* tgt = sd->getRhsFormula();
      rectifyFormulaLet(orig, tgt);
      TermList body = rectify(*t->nthArgument(0));
      if(orig==sd->getLhsLiteral() && tgt==sd->getRhsFormula() && body==*t->nthArgument(0)) {
        return t;
      }
      return Term::createFormulaLet(orig, tgt, body);
    }
    case Term::SF_LET_TERM_IN_TERM:
    {
      ASS_EQ(t->arity(),1);
      TermList orig = sd->getLhsTerm();
      TermList tgt = sd->getRhsTerm();
      rectifyTermLet(orig, tgt);
      TermList body = rectify(*t->nthArgument(0));
      if(orig==sd->getLhsTerm() && tgt==sd->getRhsTerm() && body==*t->nthArgument(0)) {
        return t;
      }
      return Term::createTermLet(orig, tgt, body);
    }
    default:
      ASSERTION_VIOLATION;
    }
    NOT_IMPLEMENTED;
  }

  Term* s = new(t->arity()) Term(*t);
  if (rectify(t->args(),s->args())) {
    if(TermList::allShared(s->args())) {
      return env.sharing->insert(s);
    }
    else {
      return s;
    }
  }
  // term not changed
  s->destroy();
  return t;
} // Rectify::rectify (Term*)

/**
 * Rectify a literal.
 * @since 24/03/2008 Torrevieja
 */
Literal* Rectify::rectify (Literal* l)
{
  CALL("Rectify::rectify(Literal*)");

  if (l->shared() && l->ground()) {
    return l;
  }

  Literal* m = new(l->arity()) Literal(*l);
  if (rectify(l->args(),m->args())) {
    if(TermList::allShared(m->args())) {
      return env.sharing->insert(m);
    }
    else {
      return m;
    }
  }
  // literal not changed
  m->destroy();
  return l;
} // Rectify::rectify (Literal*)

/**
 * Rectify a list of terms @b from to the list of terms @b to.
 * Return true if the list has changed.
 * @since 24/03/2008 Torrevieja
 */
bool Rectify::rectify(TermList* from,TermList* to)
{
  CALL("Rectify::rectify(TermList* ...)");

  bool changed = false;
  while (! from->isEmpty()) {
    if (from->isVar()) {
      int v = from->var();
      int newV = rectifyVar(v);
      to->makeVar(newV);
      if (v != newV) { // rename variable to itself
	changed = true;
      }
    }
    else { // from is not a variable
      Term* f = from->term();
      Term* t = rectify(f);
      to->setTerm(t);
      if (f != t) {
	changed = true;
      }
    }
    from = from->next();
    ASS(! to->isEmpty());
    to = to->next();
  }
  ASS(to->isEmpty());
  return changed;
} // Rectify::rectify (TermList*,...)

/**
 * Rectify variable @b v and return the result
 */
unsigned Rectify::rectifyVar(unsigned v)
{
  CALL("Rectify::rectifyVar");

  int newV;
  if (! _renaming.bound(v,newV)) {
    newV = _renaming.bind(v);
    _free = new VarList(newV,_free);
  }
  return newV;
}


/**
 * Rectify term @b t
 */
TermList Rectify::rectify(TermList t)
{
  CALL("Rectify::rectify");

  if(t.isTerm()) {
    return TermList(rectify(t.term()));
  }
  ASS(t.isOrdinaryVar());
  return TermList(rectifyVar(t.var()), false);
}

void Rectify::rectifyTermLet(TermList& lhs, TermList& rhs)
{
  CALL("Rectify::rectifyTermLet");

  //the variables of the lhs will be bound in the rhs, so we
  //need to rectify them
  VarList* vs = 0;
  VariableIterator vit(lhs);
  VarList::pushFromIterator(getMappingIterator(
	getUniquePersistentIteratorFromPtr(&vit), OrdVarNumberExtractorFn()), vs);
  //we don't need the resultof variable rectification, we just needed to do the binding
  VarList* vs1 = rectify(vs);
  lhs = rectify(lhs);
  rhs = rectify(rhs);
  ASS_EQ(vs->length(), vs1->length()); //the equal length is needed by our list-destroying code
  while(vs) {
    //the lists vs and vs1 start sharing the same links at some point, so
    //it gets a little tricky to free all elements
    if(vs1 && vs!=vs1) {
      VarList::pop(vs1);
    }
    else {
      vs1 = 0;
    }
    _renaming.undoBinding(VarList::pop(vs));
  }
}

void Rectify::rectifyFormulaLet(Literal*& lhs, Formula*& rhs)
{
  CALL("Rectify::rectifyFormulaLet");

  //the variables of the lhs will be bound in the rhs, so we
  //need to rectify them
  VarList* vs = 0;
  VariableIterator vit(lhs);
  VarList::pushFromIterator(getMappingIterator(
	getUniquePersistentIteratorFromPtr(&vit), OrdVarNumberExtractorFn()), vs);
  //we don't need the resultof variable rectification, we just needed to do the binding
  VarList* vs1 = rectify(vs);
  lhs = rectify(lhs);
  rhs = rectify(rhs);
  ASS_EQ(vs->length(), vs1->length()); //the equal length is needed by our list-destroying code
  while(vs) {
    //the lists vs and vs1 start sharing the same links at some point, so
    //it gets a little tricky to free all elements
    if(vs1 && vs!=vs1) {
      VarList::pop(vs1);
    }
    else {
      vs1 = 0;
    }
    _renaming.undoBinding(VarList::pop(vs));
  }
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
  CALL("Rectify::rectify (Formula*)");

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
    VarList* vs = rectify(f->vars());
    Formula* arg = rectify(f->qarg());
    VarList::Iterator ws(f->vars());
    while (ws.hasNext()) {
      _renaming.undoBinding(ws.next());
    }
    if (vs == f->vars() && arg == f->qarg()) {
      return f;
    }
    return new QuantifiedFormula(f->connective(),vs,arg);
  }

  case ITE:
  {
    Formula* c = rectify(f->condArg());
    Formula* t = rectify(f->thenArg());
    Formula* e = rectify(f->elseArg());
    if (c == f->condArg() && t == f->thenArg() && e == f->elseArg()) {
      return f;
    }
    return new IteFormula(f->connective(), c, t, e);
  }

  case TERM_LET:
  {
    TermList o = f->termLetLhs();
    TermList t = f->termLetRhs();
    rectifyTermLet(o, t);
    Formula* b = rectify(f->letBody());
    if(o==f->termLetLhs() && t==f->termLetRhs() && b==f->letBody()) {
      return f;
    }
    return new TermLetFormula(o, t, b);
  }

  case FORMULA_LET:
  {
    Literal* o = f->formulaLetLhs();
    Formula* t = f->formulaLetRhs();
    rectifyFormulaLet(o, t);
    Formula* b = rectify(f->letBody());
    if(o==f->formulaLetLhs() && t==f->formulaLetRhs() && b==f->letBody()) {
      return f;
    }
    return new FormulaLetFormula(o, t, b);
  }

  case TRUE:
  case FALSE:
    return f;

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
} // Rectify::rectify (Formula*)

/**
 * Undo the last binding for variable var.
 * @since 07/06/2007 Manchester
 */
void Rectify::Renaming::undoBinding (int var)
{
  CALL("Rectify::Renaming::undoBinding");

  ASS(var < (int)_capacity);
  ASS(var >= 0);

  VarList* lst = _array[var];
  ASS(lst);
  _array[var] = lst->tail();

  delete lst;
} // Rectify::Renaming::undoBinding

/**
 * Bind var to a new variable and return the new variable.
 * @since 07/06/2007 Manchester
 */
int Rectify::Renaming::bind (int var)
{
  CALL("Rectify::Renaming::bind");

  int result;

  if(VarManager::varNamePreserving()) {
    if(!_used) {
      Recycler::get(_used);
      _used->reset();
    }
    if(_used->insert(var)) {
      result=var;
    }
    else {
      result=VarManager::getVarAlias(var);
    }
  }
  else {
    result = _nextVar++;
  }
  VarList* lstu = get(var);
  (*this)[var] = new VarList(result,lstu);

  return result;
} // Rectify::Renaming::bind

/**
 * Rectify a list of variables.
 *
 * @param vs the list to rectify
 *
 * @since 05/09/2002 Trento, changed from a function on formulas
 * @since 02/01/2004 Manchester, slightly changed again
 * @since 16/01/2004 Manchester, changed to use bound variables
 * @since 23/01/2004 Manchester, changed to use non-static objects
 * @since 08/06/2007 Manchester, changed to use new data structures
 */
Rectify::VarList* Rectify::rectify (VarList* vs)
{
  CALL ("Rectify::rectify (VarList*)");

  if (vs->isEmpty()) {
    return vs;
  }
  int v = vs->head();
  int w = _renaming.bind(v);
  VarList* vtail = vs->tail();
  VarList* ws = rectify(vtail);
  if (v == w && vtail == ws) {
    return vs;
  }
  return new VarList(w,ws);
} // Rectify::rectify(const VarList& ...)


/**
 * Rectify a list of formulas.
 * @since 08/06/2007 Manchester
 */
FormulaList* Rectify::rectify (FormulaList* fs)
{
  CALL ("Rectify::rectify (FormulaList*)");

  if (fs->isEmpty()) {
    return fs;
  }
  Formula* f = fs->head();
  FormulaList* tail = fs->tail();
  Formula* g = rectify(f);
  FormulaList* gs = rectify(tail);

  if (f == g && tail == gs) {
    return fs;
  }
  return new FormulaList(g,gs);
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
