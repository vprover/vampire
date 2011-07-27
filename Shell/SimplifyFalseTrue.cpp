/**
 * @file SimplifyFalseTrue.cpp
 * Implements class SimplifyFalseTrue implementing simplification
 * of formulas containing true or false.
 *
 * @since 11/12/2004 Manchester
 */

#include "Debug/Tracer.hpp"

#include "Lib/DArray.hpp"

#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Unit.hpp"

#include "SimplifyFalseTrue.hpp"

using namespace Kernel;
using namespace Shell;
using namespace Lib;

/**
 * Simplify the unit.
 *
 * @since 11/12/2004 Manchester
 * @since 14/04/2005 Manchester, return value changed to boolean.
 * @return the simplified unit, coincides with the input unit if not changed
 * @warning the unit must contain a formula
 * @since 09/06/2007 Manchester, changed to new datastructures
 */
FormulaUnit* SimplifyFalseTrue::simplify (FormulaUnit* unit)
{
  CALL("SimplifyFalseTrue::simplify(Unit*)");
  ASS(! unit->isClause());

  Formula* f = unit->formula();
  Formula* g = simplify(f);
  if (f == g) { // not simplified
    return unit;
  }

  return new FormulaUnit(g,
			 new Inference1(Inference::REDUCE_FALSE_TRUE,unit),
			 unit->inputType());
} // SimplifyFalseTrue::simplify


/**
 * Simplify subformula.
 *
 * @since 30/08/2002 Torrevieja, return type changed to void
 * @since 23/01/2004 Manchester, changed to include info about positions
 * @since 11/12/2004 Manchester, true and false added
 * @since 09/06/2007 Manchester, changed to new datastructures
 * @since 27/03/2008 Torrevieja, AND/OR case changed considerably
 */
Formula* SimplifyFalseTrue::simplify (Formula* f)
{
  CALL("SimplifyFalseTrue::simplify(Formula*)");

  Connective con = f->connective();
  switch (con) {
  case LITERAL:
  case TRUE:
  case FALSE:
    return f;

  case AND:
  case OR: 
    {
      int length = 0;  // the length of the result
      bool changed = false;
      FormulaList* fs = f->args();
      DArray<Formula*> gs(fs->length());

      FormulaList::Iterator it(fs);
      while (it.hasNext()) {
	Formula* h = it.next();
	Formula* g = simplify(h);
	switch (g->connective()) {
	case TRUE:
	  if (con == OR) {
	    return g;
	  }
	  if (con == AND) {
	    changed = true;
	    break;
	  }
	  gs[length++] = g;
	  if (h != g) {
	    changed = true;
	  }
	  break;

	case FALSE:
	  if (con == AND) {
	    return g;
	  }
	  if (con == OR) {
	    changed = true;
	    break;
	  }
	  gs[length++] = g;
	  if (h != g) {
	    changed = true;
	  }
	  break;

	default:
	  gs[length++] = g;
	  if (h != g) {
	    changed = true;
	  }
	  break;
	}
      }
      if (! changed) {
	return f;
      }
      switch (length) {
      case 0:
	return new Formula(con == OR ? false : true);
      case 1:
	return gs[0];
      default:
	FormulaList* res = FormulaList::empty();
	for (int l = length-1;l >= 0;l--) {
	  FormulaList::push(gs[l],res);
	}
	return new JunctionFormula(con,res);
      }
    }

  case IMP:
    {
      Formula* right = simplify(f->right());
      if (right->connective() == TRUE) {
	return right;
      }
      Formula* left = simplify(f->left());

      switch (left->connective()) {
      case TRUE: // T -> R
	return right;
      case FALSE: // F -> R
	return new Formula(true);
      default: // L -> R;
	break;
      }

      if (right->connective() == FALSE) {
	return new NegatedFormula(left);
      }
      if (left == f->left() && right == f->right()) {
	return f;
      }
      return new BinaryFormula(con,left,right);
    }

  case IFF:
  case XOR: 
    {
      Formula* left = simplify(f->left());
      Formula* right = simplify(f->right());

      Connective lc = left->connective();
      Connective rc = right->connective();

      switch (lc) {
      case FALSE: // F * _
	switch (rc) {
	case FALSE: // F * F
	  return con == XOR
	         ? right
	         : new Formula(true);
	case TRUE: // F * T
	  return con == XOR
	         ? right
     	         : left;
	default: // F * R
	  return con == XOR
	         ? right
 	         : new NegatedFormula(right);
	}
      case TRUE: // T * _
	switch (rc) {
	case FALSE: // T * F
	  return con == XOR
	         ? left
	         : right;
	case TRUE: // T * T
	  return con == XOR
 	         ? new Formula(false)
     	         : left;
	default: // T * R
	  return con == XOR
 	         ? new NegatedFormula(right)
     	         : right;
	}
      default: // L * _
	switch (rc) {
	case FALSE: // L * F
	  return con == XOR
	         ? left
 	         : new NegatedFormula(left);
	case TRUE:  // L * T
	  return con == XOR
 	         ? new NegatedFormula(left)
     	         : left;
	default:    // L * R
	  if (left == f->left() && right == f->right()) {
	    return f;
	  }
	  return new BinaryFormula(con,left,right);
	}
      }
    }
    
  case NOT: 
    {
      Formula* arg = simplify(f->uarg());
      switch (arg->connective()) {
      case FALSE:
	return new Formula(true);
      case TRUE:
	return new Formula(false);
      default:
	return arg == f->uarg() ? f : new NegatedFormula(arg);
      }
    }
    
  case FORALL:
  case EXISTS: 
    {
      Formula* arg = simplify(f->qarg());
      switch (arg->connective()) {
      case FALSE:
      case TRUE:
	return arg;
      default:
	return arg == f->qarg()
               ? f
               : new QuantifiedFormula(con,f->vars(),arg);
      }
    }

  case ITE:
    {
      Formula* c = simplify(f->condArg());
      switch (f->connective()) {
      case TRUE:
	return simplify(f->thenArg());
      case FALSE:
	return simplify(f->elseArg());
      default:
	break;
      }
      Formula* t = simplify(f->thenArg());
      Formula* e = simplify(f->elseArg());

      switch (t->connective()) {
      case TRUE:
	switch (e->connective()) {
	case TRUE:
	  return new Formula(true);
	case FALSE:
	  return c;
	default:
	  return new BinaryFormula(IMP, new NegatedFormula(c), e);
	}
      case FALSE:
	switch (e->connective()) {
	case TRUE:
	  return new NegatedFormula(c);
	case FALSE:
	  return new Formula(false);
	default: {
	  FormulaList* args = 0;
	  FormulaList::push(new NegatedFormula(c), args);
	  FormulaList::push(e, args);
	  return new JunctionFormula(AND, args);
	}
	}
      default:
	switch (e->connective()) {
	case TRUE:
	  return new BinaryFormula(IMP, c, t);
	case FALSE: {
	  FormulaList* args = 0;
	  FormulaList::push(c, args);
	  FormulaList::push(t, args);
	  return new JunctionFormula(AND, args);
	}
	default:
	  break;
	}
      }

      if (c == f->condArg() && t == f->thenArg() && e == f->elseArg()) {
	return f;
      }
      return new IteFormula(c,t,e);
    }

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
} // SimplifyFalseTrue::simplify ()


