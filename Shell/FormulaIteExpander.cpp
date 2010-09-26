/**
 * @file FormulaIteExpander.cpp
 * Implements class FormulaIteExpander.
 */

#include <algorithm>

#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Unit.hpp"

#include "FormulaIteExpander.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

void FormulaIteExpander::apply(UnitList*& units)
{
  CALL("FormulaIteExpander::apply(UnitList*&)");
  ASS(!_defs);

  UnitList::DelIterator us(units);
  while(us.hasNext()) {
    Unit* u = us.next();
    if(u->isClause()) {
      continue;
    }
    Unit* v = apply(u);
    if(v != u) {
	us.replace(v);
    }
  }
  us.insert(_defs);
  _defs=0;
}

/**
 * Return result of if-then-else expansion in @b unit. Into @b defs assign
 * list of introduced definitions.
 */
Unit* FormulaIteExpander::apply(Unit* unit, UnitList*& defs)
{
  CALL("FormulaIteExpander::apply(Unit*,UnitList*&)");
  ASS(!_defs);

  if(unit->isClause()) {
    return unit;
  }

  Unit* res=apply(unit);

  defs=_defs;
  _defs=0;
  return res;
}

Unit* FormulaIteExpander::apply(Unit* unit)
{
  CALL("FormulaIteExpander::apply(Unit*)");
  ASS(! unit->isClause());

  Formula* f = static_cast<FormulaUnit*>(unit)->formula();
  Formula* g = apply(f);
  if (f == g) { // not changed
    return unit;
  }

  return new FormulaUnit(g,
			 new Inference1(Inference::FORMULA_ITE_EXPANSION,unit),
			 unit->inputType());
}


Formula* FormulaIteExpander::apply(Formula* f)
{
  CALL("FormulaIteExpander::apply(Formula*)");

  Connective con = f->connective();
  switch (con) {
  case LITERAL:
  case TRUE:
  case FALSE:
    return f;

  case AND:
  case OR:
    {
      FormulaList* args = apply(f->args());
      if (args == f->args()) {
	return f;
      }
      return new JunctionFormula(con,args);
    }

  case IMP:
  case IFF:
  case XOR:
    {
      Formula* left = apply(f->left());
      Formula* right = apply(f->right());
      if (left == f->left() && right == f->right()) {
	return f;
      }
      return new BinaryFormula(con,left,right);
    }

  case NOT:
    {
      Formula* arg = apply(f->uarg());
      if (arg == f->uarg()) {
	return f;
      }
      return new NegatedFormula(arg);
    }

  case FORALL:
  case EXISTS:
    {
      Formula* arg = apply(f->qarg());
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
      Formula* c = apply(f->condarg());
      Formula* t = apply(f->thenarg());
      Formula* e = apply(f->elsearg());

      while(c->connective()==NOT) {
	c = c->uarg();
        std::swap(t,e);
      }

      if(c->connective()!=LITERAL) {
	c = introduceDefinition(c);
      }
      ASS(c->connective()==LITERAL)

      return makeBinaryJunction(OR, makeBinaryJunction(AND,c,t),
	  makeBinaryJunction(AND,new NegatedFormula(c), e));
    }

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }

}

FormulaList* FormulaIteExpander::apply(FormulaList* fs)
{
  CALL("FormulaIteExpander::apply(FormulaList*)");

  if (fs->isEmpty()) {
    return fs;
  }
  Formula* head = apply(fs->head());
  FormulaList* tail = apply(fs->tail());

  if (head == fs->head() && tail == fs->tail()) {
    return fs;
  }
  return new FormulaList(head,tail);
}

/**
 * For @b con being either @b OR or @b AND, return a formula @b f1 @b con @b f2
 */
Formula* FormulaIteExpander::makeBinaryJunction(Connective con, Formula* f1, Formula* f2)
{
  CALL("FormulaIteExpander::makeBinaryJunction");
  ASS(con == OR || con == AND);

  FormulaList* args = 0;
  FormulaList::push(f1, args);
  FormulaList::push(f2, args);
  return new JunctionFormula(con, args);
}

/**
 * For formula F with free variables X0..XN introduce name p(X0..XN)
 * by a formula ![X0..XN]: (p(X0..XN) <=> F). This formula is put into the
 * @b _defs list, and an atomic formula p(X0..XN) is returned.
 */
Formula* FormulaIteExpander::introduceDefinition(Formula* f)
{
  CALL("FormulaIteExpander::introduceDefinition");

  Formula::VarList* fv=f->freeVariables();
  unsigned fvLen=fv->length();
  unsigned dpred=env.signature->addNamePredicate(fvLen);

  static Stack<TermList> args;
  Formula::VarList::Iterator fvit(fv);
  while(fvit.hasNext()) {
    unsigned var=fvit.next();
    args.push(TermList(var, false));
  }
  Literal* dlit=Literal::create(dpred, fvLen, true, false, args.begin());
  Formula* datom=new AtomicFormula(dlit);

  Formula* def=new BinaryFormula(IFF, datom, f);
  if(fv) {
    def=new QuantifiedFormula(FORALL, fv, def);
  }
  Unit* dunit=new FormulaUnit(def, new Inference(Inference::PREDICATE_DEFINITION), Unit::AXIOM);
  UnitList::push(dunit, _defs);

  return datom;
}


}
