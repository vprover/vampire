/**
 * @file SymCounter.cpp
 * Implements class SymCounter counting occurrences of function
 * and predicate symbols.
 *
 * @since 01/05/2002, Manchester
 */

#include "Lib/Allocator.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Unit.hpp"

#include "SymCounter.hpp"

using namespace Kernel;
using namespace Shell;

/**
 * Initialise SymCounter.
 * @since 09/06/2007 Manchester
 */
SymCounter::SymCounter (Signature& sig)
  :
  _noOfPreds(sig.predicates()),
  _noOfFuns (sig.functions())
{
  CALL("SymCounter::SymCounter");

  if (_noOfPreds) {
    void* mem = ALLOC_KNOWN(_noOfPreds*sizeof(Pred),"SymCounter::Pred[]");
    _preds = array_new<Pred>(mem, _noOfPreds);
  }

  if (_noOfFuns) {
    void* mem = ALLOC_KNOWN(_noOfFuns*sizeof(Fun),"SymCounter::Fun[]");
    _funs = array_new<Fun>(mem, _noOfFuns);
  }
} // SymCounter::SymCounter


/**
 * Destroy a symbol counter
 * @since 01/05/2002, Manchester
 */
SymCounter::~SymCounter ()
{
  CALL("SymCounter::~SymCounter");

  if (_noOfPreds) {
    array_delete(_preds,_noOfPreds);
    DEALLOC_KNOWN(_preds,_noOfPreds*sizeof(Pred),"SymCounter::Pred[]");
  }
  if (_noOfFuns) {
    array_delete(_funs,_noOfFuns);
    DEALLOC_KNOWN(_funs,_noOfFuns*sizeof(Fun),"SymCounter::Fun[]");
  }
} // SymCounter::~SymCounter


/**
 * Count symbols in a problem.
 * c must be 1 or -1, 1 means add number of occurrences for each symbol, -1 means subtract
 * @since 01/05/2002, Manchester
 */
void SymCounter::count (const UnitList* units,int c)
{
  CALL("SymCounter::count (const UnitList*)");

  UnitList::Iterator us(units);
  while (us.hasNext()) {
    const Unit* unit = us.next();
    if (unit->isClause()) {
      count(static_cast<const Clause*>(unit),c);
    }
    else {
      count (static_cast<const FormulaUnit*>(unit)->formula(),true,c);
    }
  }
} // SymCounter::count (UnitList*,int c)

/**
 * Count symbols in a clause.
 * @since 01/05/2002, Manchester
 * @since 11/09/2002 Manchester, changed
 */
void SymCounter::count (const Clause* clause,int add)
{
  CALL("SymCounter::count(const Clause*)");

  for (int n = clause->length()-1;n >= 0;n--) {
    count((*clause)[n],true,add);
  }
} // SymCounter::count (Clause* u,int c)

void SymCounter::count(const Formula* f, int add)
{
  count(f, 1, add);
}

/**
 * Count symbols in a formula.
 * @since 01/05/2002, Manchester
 */
void SymCounter::count (const Formula* f,int polarity,int add)
{
  CALL("SymCounter::count(const Formula*)");

  switch (f->connective()) {
    case LITERAL:
      count (f->literal(), polarity, add);
      return;

    case AND:
    case OR: {
      FormulaList::Iterator fs(f->args());
      while (fs.hasNext()) {
        count (fs.next(),polarity,add);
      }
      return;
    }

    case IMP:
      count (f->left(), -polarity, add);
      count (f->right(), polarity, add);
      return;

    case NOT:
      count (f->uarg(), -polarity, add);
      return;

    case IFF:
    case XOR:
      count (f->left(), 0, add);
      count (f->right(), 0, add);
      return;

    case FORALL:
    case EXISTS:
      count (f->qarg(), polarity, add);
      return;

    case ITE:
      count (f->condArg(), 0, add);
      count (f->thenArg(), polarity, add);
      count (f->elseArg(), polarity, add);
      return;

  case TRUE:
  case FALSE:
    return;

#if VDEBUG
    default:
      ASSERTION_VIOLATION;
      return;
#endif
  }
} // SymCounter::count (Formula* f,...)


/**
 * Count symbols in a literal.
 * @since 01/05/2002, Manchester
 */
void SymCounter::count(const Literal* l,int polarity,int add)
{
  CALL("SymCounter::count(const Literal*)");

  int pred = l->functor();
  ASS(_noOfPreds > pred);

  _preds[pred].add(l->isPositive() ? polarity : -polarity,add);
  count(l->args(),add);
} // SymCounter::count (Literal* l ...)

/**
 * Count symbols in a term.
 * @since 01/05/2002, Manchester
 */
void SymCounter::count(const TermList* ts,int add)
{
  CALL("SymCounter::count");

  while (ts->isNonEmpty()) {
    if (! ts->isVar()) {
      const Term* t = ts->term();
      int fun = t->functor();
      ASS(_noOfFuns > fun);

      _funs[fun].add(add);
      count(t->args(),add);
    }
    ts = ts->next();
  }
} // SymCounter::count(const Term* f, ...)


/**
 * Count occurrences for a symbol.
 * @since 01/05/2002, Manchester
 */
void SymCounter::Pred::add(int polarity, int add)
{
  CALL("SymCounter::add");

  switch (polarity) {
    case -1:
      _nocc += add;
      return;

    case 0:
      _docc += add;
      return;

    case 1:
      _pocc += add;
      return;

#if VDEBUG
    default:
      ASSERTION_VIOLATION;
      return;
#endif
  }
} // SymCounter::Pred::add


