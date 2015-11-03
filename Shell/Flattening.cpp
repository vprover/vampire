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

#include "Lib/Environment.hpp"
#include "Shell/Options.hpp"

#include "Flattening.hpp"

namespace Shell
{

/**
 * Assuming formula @c f is flatenned, return its negation which is also flatenned.
 */
Formula* Flattening::getFlattennedNegation(Formula* f)
{
  CALL("Flattening::getFlattennedNegation");

  switch(f->connective()) {
  case NOT:
    return f->uarg();
  case TRUE:
    return Formula::falseFormula();
  case FALSE:
    return Formula::trueFormula();
  default:
    return new NegatedFormula(f);
  }

}

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

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] flatten in: " << unit->toString() << std::endl;
    env.endOutput();
  }
  Formula* f = unit->formula();
  Formula* g = flatten(f);
  if (f == g) { // not changed
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] flatten out: " << unit->toString() << std::endl;
      env.endOutput();
    }
    return unit;
  }

  FormulaUnit* res = new FormulaUnit(g,
			 new Inference1(Inference::FLATTEN,unit),
			 unit->inputType());
  if(unit->included()) {
    res->markIncluded();
  }
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] flatten out: " << res->toString() << std::endl;
    env.endOutput();
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
  case BOOL_TERM:
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
	return new QuantifiedFormula(con,f->vars(),f->sorts(),arg);
      }

      // arg is a quantified formula with the same quantifier
      // the sort list is either empty (if one of the parts have empty sorts) or the concatentation
      Formula::SortList* sl = 0;
      if(f->sorts() && arg->sorts()){
        sl = f->sorts()->append(arg->sorts());
      }
      return new QuantifiedFormula(con,
				   f->vars()->append(arg->vars()),
                                   sl, 
				   arg->qarg());
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

#if 1
  if(!fs) {
    return 0;
  }

  FormulaList* fs0 = fs;

  bool modified = false;
  Stack<Formula*> res(8);
  Stack<FormulaList*> toDo(8);
  for(;;) {
    if(fs->head()->connective()==con) {
      modified = true;
      if(fs->tail()) {
	toDo.push(fs->tail());
      }
      fs = fs->head()->args();
      continue;
    }
    Formula* hdRes = flatten(fs->head());
    if(hdRes!=fs->head()) {
      modified = true;
    }
    res.push(hdRes);
    fs = fs->tail();
    if(!fs) {
      if(toDo.isEmpty()) {
	break;
      }
      fs = toDo.pop();
    }
  }
  if(!modified) {
    return fs0;
  }
  FormulaList* resLst = 0;
  FormulaList::pushFromIterator(Stack<Formula*>::TopFirstIterator(res), resLst);
  return resLst;
#else
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
#endif
} // Flattening::flatten


}
