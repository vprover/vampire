/**
 * @file Flattening.cpp
 * Implementing the flattening inference rule.
 * @since 24/12/2003 Manchester
 * @since 30/10/2005 Bellevue, information about positions removed
 */

#include "Debug/RuntimeStatistics.hpp"
#include "Debug/Tracer.hpp"

#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Unit.hpp"

#include "Flattening.hpp"

namespace Shell
{

/**
 * Flatten the unit.
 *
 * @since 24/12/2003 Manchester
 * @since 23/01/2004 Manchester, changed to include info about positions
 * @since 08/06/2007 Manchester changed to new data structures
 * @warning the unit must contain a formula
 */
FormulaUnit* Flattening::flatten (FormulaUnit* unit)
{
  CALL("Flattening::flatten (Unit*)");
  ASS(! unit->isClause());

  Formula* f = unit->formula();
  Formula* g = flatten(f);
  if (f == g) { // not changed
    return unit;
  }

  FormulaUnit* res = new FormulaUnit(g,
			 new Inference1(Inference::FLATTEN,unit),
			 unit->inputType());
  if(unit->included()) {
    res->markIncluded();
  }
  return res;
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

      if(arg->connective()==NOT) {
	//two negations cancel each other out
	return arg->uarg();
      }
      if(arg->connective()==LITERAL) {
	return new AtomicFormula(Literal::complementaryLiteral(arg->literal()));
      }
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
      return new IteFormula(c,t,e);
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


bool TopLevelFlatten::apply(Problem& prb)
{
  CALL("TopLevelFlatten::apply(Problem&)");

  if(apply(prb.units())) {
    prb.invalidateProperty();
    return true;
  }
  else {
    return false;
  }
}

bool TopLevelFlatten::apply(UnitList*& units)
{
  CALL("TopLevelFlatten::apply(UnitList*&)");

  Stack<FormulaUnit*> flAcc;

  bool modified = false;
  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if(u->isClause()) {
      continue;
    }
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    flAcc.reset();
    if(!apply(fu, flAcc)) {
      continue;
    }
    modified = true;
    ASS_GE(flAcc.size(),2);
    while(flAcc.isNonEmpty()) {
      uit.insert(flAcc.pop());
    }
    uit.del();
  }
  return modified;
}

/**
 * If a top-level conjunction can be expanded into multiple formulas,
 * add the formulas on @c acc and return true. Otherwise return false.
 *
 * @param fu input, must be flattenned.
 */
bool TopLevelFlatten::apply(FormulaUnit* fu, Stack<FormulaUnit*>& acc)
{
  CALL("TopLevelFlatten::apply(FormulaUnit*,Stack<FormulaUnit*>&)");

  Formula* f = fu->formula();

  Formula::VarList* vars;
  if(f->connective()==FORALL) {
    vars = f->vars();
    f = f->qarg();
  }
  else {
    vars = 0;
  }
  if(f->connective()!=AND) {
    return false;
  }
  RSTAT_CTR_INC("top level flattened formulas")
  FormulaList::Iterator fit(f->args());
  while(fit.hasNext()) {
    Formula* sf = fit.next();
    bool needsFlattening = sf->connective()==FORALL;
    if(vars) {
      sf = new QuantifiedFormula(FORALL, vars, sf);
    }
    Inference* inf = new Inference1(Inference::FLATTEN, fu);
    FormulaUnit* sfu = new FormulaUnit(sf, inf, fu->inputType());
    if(fu->included()) {
      sfu->markIncluded();
    }
    if(needsFlattening) {
      sfu = Flattening::flatten(sfu);
    }
    acc.push(sfu);
    RSTAT_CTR_INC("top level flattenning results")
  }
  return true;
}



}
