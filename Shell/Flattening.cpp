/**
 * @file Flattening.cpp
 * Implementing the flattening inference rule.
 * @since 24/12/2003 Manchester
 * @since 30/10/2005 Bellevue, information about positions removed
 */

#include "Debug/Tracer.hpp"

#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Unit.hpp"

#include "Flattening.hpp"

using namespace Kernel;
using namespace Shell;

/**
 * Flatten the unit.
 *
 * @since 24/12/2003 Manchester
 * @since 23/01/2004 Manchester, changed to include info about positions
 * @since 08/06/2007 Manchester changed to new data structures
 * @warning the unit must contain a formula
 */
Unit* Flattening::flatten (Unit* unit)
{
  CALL("Flattening::flatten (Unit*)");
  ASS(! unit->isClause());

  Formula* f = static_cast<FormulaUnit*>(unit)->formula();
  Formula* g = flatten(f);
  if (f == g) { // not changed
    return unit;
  }

  return new FormulaUnit(g,
			 new Inference1(Inference::FLATTEN,unit),
			 unit->inputType());
} // Flattening::flatten


/**
 * Flatten subformula at position pos.
 *
 * @since 30/08/2002 Torrevieja, return type changed to void
 * @since 23/01/2004 Manchester, changed to include info about positions
 * @since 11/12/2004 Manchester, true and false added
 * @since 08/06/2007 Manchester changed to new data structures
 */
Formula* Flattening::flatten (Formula* f)
{
  CALL("Flattening::flatten(Formula*)");

  Connective con = f->connective();
  switch (con) {
  case LITERAL:
  case TRUE:
  case FALSE:
    return f;

  case AND:
  case OR: 
    {
      FormulaList* args = flatten(f->args(),con);
      if (args == f->args()) { 
	return f;
      }
      return new JunctionFormula(con,args);
    }

  case IMP:
  case IFF:
  case XOR: 
    {
      Formula* left = flatten(f->left());
      Formula* right = flatten(f->right());
      if (left == f->left() && right == f->right()) {
	return f;
      }
      return new BinaryFormula(con,left,right);
    }
    
  case NOT: 
    {
      Formula* arg = flatten(f->uarg());
      if (arg == f->uarg()) {
	return f;
      }
      return new NegatedFormula(arg);
    }
    
  case FORALL:
  case EXISTS: 
    {
      Formula* arg = flatten(f->qarg());
      if (arg->connective() != con) {
	if (arg == f->qarg()) {
	  return f;
	}
	return new QuantifiedFormula(con,f->vars(),arg);
      }

      // arg is a quantified formula with the same quantifier
      return new QuantifiedFormula(con,
				   f->vars()->append(arg->vars()),
				   arg->qarg());
    }

  case ITE:
    {
      Formula* c = flatten(f->condArg());
      Formula* t = flatten(f->thenArg());
      Formula* e = flatten(f->elseArg());
      if (c == f->condArg() && t == f->thenArg() && e == f->elseArg()) {
	return f;
      }
      return new IteFormula(con,c,t,e);
    }

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }

} // Flattening::flatten ()


/** 
 * Flatten the list of formulas (connected by c).
 *
 * @returns true if there was flattening on the topmost level.
 * @since 27/06/2002 Manchester
 * @since 30/08/2002 Torrevieja, return type changed to void
 * @since 23/01/2004 Manchester, changed to include info about positions
 * @since 08/06/2007 Manchester changed to new data structures
 */
FormulaList* Flattening::flatten (FormulaList* fs, 
				  Connective con)
{
  CALL("Flattening::flatten (FormulaList*...)");
  ASS(con == OR || con == AND);

  if (fs->isEmpty()) {
    return fs;
  }
  Formula* head = flatten(fs->head());
  FormulaList* tail = flatten(fs->tail(),con);

  if (head->connective() == con) {
    return head->args()->append(tail);
  }

  if (head == fs->head() && tail == fs->tail()) {
    return fs;
  }
  return new FormulaList(head,tail);
} // Flattening::flatten


