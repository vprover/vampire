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
#include "Shell/Statistics.hpp"

#include "Flattening.hpp"

namespace Shell
{

/**
 * Assuming formula @c f is flattened, return its negation which is also flattened.
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

  Formula* f = unit->formula();
  Formula* g = flatten(f);
  if (f == g) { // not changed
    return unit;
  }

  FormulaUnit* res = new FormulaUnit(g,
      FormulaTransformation(InferenceRule::FLATTEN,unit));
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] flatten in: " << unit->toString() << std::endl;
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
 * @since 18/12/2015 Gothenburg, changes to support FOOL
 */
Formula* Flattening::innerFlatten (Formula* f)
{
  CALL("Flattening::innerFlatten(Formula*)");

  Connective con = f->connective();
  switch (con) {
  case TRUE:
  case FALSE:
    return f;

  case LITERAL:
    {
      Literal* lit = f->literal();

      if (env.options->newCNF() && !env.property->higherOrder() &&
          !env.property->hasPolymorphicSym()) {
        // Convert equality between boolean FOOL terms to equivalence
        if (lit->isEquality()) {
          TermList lhs = *lit->nthArgument(0);
          TermList rhs = *lit->nthArgument(1);

          bool lhsBoolean = lhs.isTerm() && lhs.term()->isBoolean();
          bool rhsBoolean = rhs.isTerm() && rhs.term()->isBoolean();
          bool varEquality = lit->isTwoVarEquality() && lit->twoVarEqSort() == AtomicSort::boolSort();

          if (lhsBoolean || rhsBoolean || varEquality) {
            Formula* lhsFormula = BoolTermFormula::create(lhs);
            Formula* rhsFormula = BoolTermFormula::create(rhs);
            return flatten(new BinaryFormula(lit->polarity() ? IFF : XOR, lhsFormula, rhsFormula));
          }
        }
      }

      Literal* flattenedLit = flatten(lit);
      if (lit == flattenedLit) {
        return f;
      } else {
        return new AtomicFormula(flattenedLit);
      }
    }

  case BOOL_TERM:
    {
      TermList ts = f->getBooleanTerm();
      TermList flattenedTs = flatten(ts);
      if (ts == flattenedTs) {
        return f;
      } else {
        return new BoolTermFormula(flattenedTs);
      }
    }

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
      SList* sl = SList::empty();
      if(f->sorts() && arg->sorts()){
        sl = SList::append(f->sorts(), arg->sorts());
      }
      return new QuantifiedFormula(con,
				   VList::append(f->vars(), arg->vars()),
                                   sl, 
				   arg->qarg());
    }

  case NAME:
  case NOCONN:
    ASSERTION_VIOLATION;
  }

  ASSERTION_VIOLATION;
} // Flattening::flatten ()

Literal* Flattening::flatten(Literal* l)
{
  CALL("Flattening::flatten(Literal*)");

  if (l->shared()) {
    return l;
  }

  bool flattened = false;
  Stack<TermList> args;
  Term::Iterator terms(l);
  while (terms.hasNext()) {
    TermList argument = terms.next();
    TermList flattenedArgument = flatten(argument);
    if (argument != flattenedArgument) {
      flattened = true;
    }
    args.push(flattenedArgument);
  }

  if (!flattened) {
    return l;
  }

  return Literal::create(l, args.begin());
} // NNF::ennf(Literal*);

TermList Flattening::flatten (TermList ts)
{
  CALL("Flattening::flatten(TermList)");

  if (ts.isVar()) {
    return ts;
  }

  Term* term = ts.term();

  if (term->shared()) {
    return ts;
  }

 if (term->isSpecial()) {
    Term::SpecialTermData* sd = term->getSpecialData();
    switch (sd->getType()) {
      case Term::SF_FORMULA: {
        Formula* f = sd->getFormula();
        Formula* flattenedF = flatten(f);
        if (f == flattenedF) {
          return ts;
        } else {
          return TermList(Term::createFormula(flattenedF));
        }
      }

      case Term::SF_ITE: {
        TermList thenBranch = *term->nthArgument(0);
        TermList elseBranch = *term->nthArgument(1);
        Formula* condition  = sd->getCondition();

        TermList flattenedThenBranch = flatten(thenBranch);
        TermList flattenedElseBranch = flatten(elseBranch);
        Formula* flattenedCondition  = flatten(condition);

        if ((thenBranch == flattenedThenBranch) &&
            (elseBranch == flattenedElseBranch) &&
            (condition == flattenedCondition)) {
          return ts;
        } else {
          return TermList(Term::createITE(flattenedCondition, flattenedThenBranch, flattenedElseBranch, sd->getSort()));
        }
      }

      case Term::SF_LET: {
        TermList binding = sd->getBinding();
        TermList body = *term->nthArgument(0);

        TermList flattenedBinding = flatten(binding);
        TermList flattenedBody = flatten(body);

        if ((binding == flattenedBinding) && (body == flattenedBody)) {
          return ts;
        } else {
          return TermList(Term::createLet(sd->getFunctor(), sd->getVariables(), flattenedBinding, flattenedBody, sd->getSort()));
        }
      }

      case Term::SF_LET_TUPLE: {
        TermList binding = sd->getBinding();
        TermList body = *term->nthArgument(0);

        TermList flattenedBinding = flatten(binding);
        TermList flattenedBody = flatten(body);

        if ((binding == flattenedBinding) && (body == flattenedBody)) {
          return ts;
        } else {
          return TermList(Term::createTupleLet(sd->getFunctor(), sd->getTupleSymbols(), flattenedBinding, flattenedBody, sd->getSort()));
        }
      }

      case Term::SF_TUPLE: {
        TermList tupleTerm = TermList(sd->getTupleTerm());
        TermList flattenedTupleTerm = flatten(tupleTerm);

        if (tupleTerm == flattenedTupleTerm) {
          return ts;
        } else {
          ASS_REP(flattenedTupleTerm.isTerm(), flattenedTupleTerm.toString())
          return TermList(Term::createTuple(flattenedTupleTerm.term()));
        }
      }

      case Term::SF_MATCH: {
        DArray<TermList> terms(term->arity());
        bool unchanged = true;
        for (unsigned i = 0; i < term->arity(); i++) {
          terms[i] = flatten(*term->nthArgument(i));
          unchanged = unchanged && (terms[i] == *term->nthArgument(i));
        }

        if (unchanged) {
          return ts;
        }
        return TermList(Term::createMatch(sd->getSort(), sd->getMatchedSort(), term->arity(), terms.begin()));
      }

      default:
        ASSERTION_VIOLATION;
    }
  }

  bool flattened = false;
  Stack<TermList> args;
  Term::Iterator terms(term);
  while (terms.hasNext()) {
    TermList argument = terms.next();
    TermList flattenedArgument = flatten(argument);
    if (argument != flattenedArgument) {
      flattened = true;
    }
    args.push(flattenedArgument);
  }

  if (!flattened) {
    return ts;
  }

  return TermList(Term::create(term, args.begin()));
} // Flattening::flatten (Term*)

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
    return FormulaList::append(head->args(), tail);
  }

  if (head == fs->head() && tail == fs->tail()) {
    return fs;
  }
  return new FormulaList(head,tail);
#endif
} // Flattening::flatten


}
