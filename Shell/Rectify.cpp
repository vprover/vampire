/**
 * @file Rectify.cpp
 * Implements (static) class Rectify for the rectification inference rule.
 * @since 21/12/2003 Manchester
 * @since 23/01/2004 Manchester, changed to use non-static objects
 */

#include "Lib/Environment.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"

#include "Indexing/TermSharing.hpp"

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
} // Renaming::~Renaming

/**
 * Rectify a compound term.
 * @since 01/11/2005 Bellevue
 * @since 04/06/2007 Frankfurt Airport, changed to new datastructures
 */
Term* Rectify::rectify (Term* t)
{
  CALL("Rectify::rectify(Term*)");

  if (t->ground()) {
    return t;
  }

  Term* s = new(t->arity()) Term(*t);
  if (rectify(t->args(),s->args())) {
    return env.sharing->insert(s);
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

  if (l->ground()) {
    return l;
  }

  Literal* m = new(l->arity()) Literal(*l);
  if (rectify(l->args(),m->args())) {
    return env.sharing->insert(m);
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
      int newV;
      if (! _renaming.bound(v,newV)) {
	newV = _renaming.bind(v);
	_free = new VarList(newV,_free);
      }
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

  int result = _nextVar++;
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
