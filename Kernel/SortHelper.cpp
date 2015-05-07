/**
 * @file SortHelper.cpp
 * Implements class SortHelper.
 */

#include "Lib/Environment.hpp"

#include "Clause.hpp"
#include "FormulaUnit.hpp"
#include "Signature.hpp"
#include "Sorts.hpp"
#include "SubformulaIterator.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"

#include "SortHelper.hpp"

using namespace Kernel;

/**
 * Return the type of a term or a literal @c t
 * @author Andrei Voronkov
 */
BaseType& SortHelper::getType(Term* t)
{
  if (t->isLiteral()) {
    return *(env.signature->getPredicate(t->functor())->predType());
  }
  return *env.signature->getFunction(t->functor())->fnType();
} // getType

/**
 * Return the sort of a non-variable term t. This function cannot be applied
 * to a special term, such as if-then-else.
 */
unsigned SortHelper::getResultSort(Term* t)
{
  CALL("SortHelper::getResultSort(Term*)");
  ASS(!t->isSpecial());
  ASS(!t->isLiteral());

  Signature::Symbol* sym = env.signature->getFunction(t->functor());
  return sym->fnType()->result();
}

/**
 * Try get result sort of a term.
 *
 * This function can be applied also to special terms such as if-then-else.
 */
bool SortHelper::tryGetResultSort(Term* t, unsigned& result)
{
  CALL("tryGetResultSort(Term*,unsigned&)");
  ASS(!t->isLiteral());

  TermList masterVar;
  return getResultSortOrMasterVariable(t, result, masterVar);
}

bool SortHelper::tryGetResultSort(TermList t, unsigned& result)
{
  CALL("tryGetResultSort(TermList,unsigned&)");
  if (t.isVar()) {
    return false;
  }
  return tryGetResultSort(t.term(), result);
}

/**
 * This function works also for special terms
 */
unsigned SortHelper::getResultSort(TermList t, DHMap<unsigned,unsigned>& varSorts)
{
  CALL("SortHelper::getResultSort");

  unsigned res;
  TermList masterVar;
  if (!getResultSortOrMasterVariable(t, res, masterVar)) {
    ASS(masterVar.isOrdinaryVar());
    res = varSorts.get(masterVar.var());
  }
  return res;
}

/**
 * If sort of term @c t depends on a variable, assign the variable into
 * @c resultVar and return false. Otherwise assign the sort of the term
 * into @c resultSort and return true.
 */
bool SortHelper::getResultSortOrMasterVariable(Term* t, unsigned& resultSort, TermList& resultVar)
{
  CALL("SortHelper::getResultSortOrMasterVariable");

  if (!t->isSpecial()) {
    resultSort = getResultSort(t);
    return true;
  }
  //we may have many nested special terms. to be safe, we traverse them using our own stack.
  static Stack<Term*> candidates;
  candidates.reset();

  TermList masterVar;
  masterVar.makeEmpty();

  for (;;) {
    switch(t->functor()) {
    case Term::SF_TERM_ITE:
    {
      TermList arg1 = *t->nthArgument(0);
      TermList arg2 = *t->nthArgument(1);
      if (arg1.isTerm()) {
	candidates.push(arg1.term());
      }
      else {
	masterVar = arg1;
      }
      if (arg2.isTerm()) {
	candidates.push(arg2.term());
      }
      else {
	masterVar = arg2;
      }
      break;
    }
    case Term::SF_TERM_LET:
    {
      TermList arg1 = *t->nthArgument(0);
      if (arg1.isTerm()) {
	candidates.push(arg1.term());
      }
      else {
	masterVar = arg1;
      }
      break;
    }
    case Term::SF_FORMULA:
      // will we have a problem with a term being sorted as bool here?
      resultSort = Sorts::SRT_BOOL;
      return true;
    default:
      ASS(!t->isSpecial());
      resultSort = getResultSort(t);
      return true;
    }
    if (candidates.isEmpty()) {
      ASS(masterVar.isVar());
      resultVar = masterVar;
      return false;
    }
    t = candidates.pop();
  }
} // SortHelper::getResultSortOrMasterVariable

/**
 * If sort of term @c t depends on a variable, assign the variable into
 * @c resultVar and return false. Otherwise assign the sort of the term
 * into @c resultSort and return true.
 */
bool SortHelper::getResultSortOrMasterVariable(TermList t, unsigned& resultSort, TermList& resultVar)
{
  CALL("SortHelper::getResultSortOrMasterVariable");

  if (t.isVar()) {
    resultVar = t;
    return false;
  }
  return getResultSortOrMasterVariable(t.term(), resultSort, resultVar);
}

/**
 * Return sort of the argument @c argIndex of the term or literal @c t
 */
unsigned SortHelper::getArgSort(Term* t, unsigned argIndex)
{
  CALL("SortHelper::getArgSort(Term*,unsigned)");
  ASS_L(argIndex, t->arity());

  if (t->isLiteral() && static_cast<Literal*>(t)->isEquality()) {
    return getEqualityArgumentSort(static_cast<Literal*>(t));
  }

  return getType(t).arg(argIndex);
} // getArgSort

unsigned SortHelper::getEqualityArgumentSort(const Literal* lit)
{
  CALL("SortHelper::getEqualityArgumentSort");
  ASS(lit->isEquality());

  if (lit->isTwoVarEquality()) {
    return lit->twoVarEqSort();
  }

  TermList arg1 = *lit->nthArgument(0);
  unsigned srt1;
  if (tryGetResultSort(arg1, srt1)) {
    return srt1;
  }

  TermList arg2 = *lit->nthArgument(1);
  unsigned srt2;
  ALWAYS(tryGetResultSort(arg2, srt2));
  return srt2;
} // 

/**
 * Return sort of term @c trm that appears inside literal @c lit.
 */
unsigned SortHelper::getTermSort(TermList trm, Literal* lit)
{
  CALL("SortHelper::getTermSort");

  if (trm.isTerm()) {
    return getResultSort(trm.term());
  }
  ASS(trm.isVar());
  return getVariableSort(trm, lit);
}

/**
 * Return sort of variable @c var in term or literal @c t
 *
 * Variable @c var must occurr in @c t.
 */
unsigned SortHelper::getVariableSort(TermList var, Term* t)
{
  CALL("SortHelper::getVariableSort(TermList,Term*)");

  unsigned res;
  ALWAYS(tryGetVariableSort(var, t, res));
  return res;
}

/**
 * Return sort of variable @c var in formula @c f.
 *
 * The variable
 */
bool SortHelper::tryGetVariableSort(unsigned var, Formula* f, unsigned& res)
{
  CALL("SortHelper::tryGetVariableSort(unsigned,Formula*,unsigned&)");

  TermList varTerm(var, false);

  SubformulaIterator sfit(f);
  while (sfit.hasNext()) {
    Formula* sf = sfit.next();
    if (sf->connective() != LITERAL) {
      continue;
    }
    Literal* lit = sf->literal();

    if (!lit->containsSubterm(varTerm)) {
      continue;
    }
    res = getVariableSort(varTerm, lit);
    return true;
  }
  return false;
}

/**
 * Insert variable sorts from non-shared subterms of @c t0 into @c map. If a
 * variable is in map already (or appears multiple times), assert that the sorts
 * are equal. @c t0 can be either term or literal.
 * @since 04/05/2013 Manchester, new NonVariableIterator is used
 * @author Andrei Voronkov
 */
void SortHelper::collectVariableSorts(Term* t0, DHMap<unsigned,unsigned>& map)
{
  CALL("SortHelper::collectVariableSorts(Term*,...)");

  NonVariableIterator sit(t0,true);
  while (sit.hasNext()) {
    int idx = 0;
    Term* t = sit.next().term();
    if (t->shared() && t->ground()) {
      sit.right();
    }
    TermList* args = t->args();
    while (!args->isEmpty()) {
      if (args->isOrdinaryVar()) {
	unsigned varNum = args->var();
	unsigned varSort = getArgSort(t, idx);
	if (!map.insert(varNum, varSort)) {
	  ASS_EQ(varSort, map.get(varNum));
	}
      } else if (args->isTerm() && args->term()->isFormula()) {
        collectVariableSorts(args->term()->getSpecialData()->getFormula(), map);
      }
      idx++;
      args=args->next();
    }
  }
} // SortHelper::collectVariableSorts

/**
 * Insert variable sorts from @c f into @c map. If a variable
 * is in map already (or appears multiple times), assert that
 * the sorts are equal.
 */
void SortHelper::collectVariableSorts(Formula* f, DHMap<unsigned,unsigned>& map)
{
  CALL("SortHelper::collectVariableSorts(Formula*,...)");

  SubformulaIterator sfit(f);
  while (sfit.hasNext()) {
    Formula* sf = sfit.next();
    switch (sf->connective()) {
      case LITERAL:
        collectVariableSorts(sf->literal(), map);
        break;

      case BOOL_TERM: {
        TermList ts = sf->getBooleanTerm();
        if (!ts.isVar()) {
          continue;
        }
        if (!map.insert(ts.var(), Sorts::SRT_FOOL_BOOL)) {
          ASS_EQ(Sorts::SRT_FOOL_BOOL, map.get(ts.var()));
        }
        break;
      }

      default:
        continue;
    }
  }
}

/**
 * Insert variable sorts from @c u into @c map. If a variable
 * is in map already (or appears multiple times), assert that
 * the sorts are equal.
 */
void SortHelper::collectVariableSorts(Unit* u, DHMap<unsigned,unsigned>& map)
{
  CALL("SortHelper::collectVariableSorts(Unit*,...)");

  if (!u->isClause()) {
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    collectVariableSorts(fu->formula(), map);
    return;
  }

  Clause* cl = static_cast<Clause*>(u);
  Clause::Iterator cit(*cl);
  while (cit.hasNext()) {
    Literal* l = cit.next();
    collectVariableSorts(l, map);
  }
}

/**
 * If variable @c var occurrs in term @c t, set @c result to its
 * sort and return true. Otherwise return false.
 * @since 04/05/2013 Manchester, new NonVariableIterator is used
 * @author Andrei Voronkov
 */
bool SortHelper::tryGetVariableSort(TermList var, Term* t0, unsigned& result)
{
  CALL("SortHelper::tryGetVariableSort");

  NonVariableIterator sit(t0,true);
  while (sit.hasNext()) {
    Term* t = sit.next().term();
    if (t->ground()) {
      sit.right();
      continue;
    }
    int idx = 0;
    TermList* args = t->args();
    while (!args->isEmpty()) {
      if (*args==var) {
	result = getArgSort(t, idx);
        return true;
      }
      idx++;
      args=args->next();
    }
  }
  return false;
} // SortHelper::tryGetVariableSort

/**
 * Return true iff sorts of immediate subterms of term/literal @c t correspond
 * to the type of @c t.
 *
 * @pre Arguments of t must be shared.
 */
bool SortHelper::areImmediateSortsValid(Term* t)
{
  CALL("SortHelper::areImmediateSortsValid");

  if (t->isLiteral() && static_cast<Literal*>(t)->isEquality()) {
    Literal* lit = static_cast<Literal*>(t);
    unsigned eqSrt = getEqualityArgumentSort(lit);
    for (unsigned i=0; i<2; i++) {
      TermList arg = *t->nthArgument(i);
      if (!arg.isTerm()) { continue; }
      Term* ta = arg.term();
      unsigned argSort = getResultSort(ta);
      if (eqSrt != argSort) {
        return false;
      }
    }
    return true;
  }

  BaseType& type = getType(t);
  unsigned arity = t->arity();
  for (unsigned i=0; i<arity; i++) {
    TermList arg = *t->nthArgument(i);
    if (!arg.isTerm()) { continue; }
    Term* ta = arg.term();
    unsigned argSort = getResultSort(ta);
    if (type.arg(i) != argSort) {
      cout << "error with expected " << type.arg(i) << " and actual " << argSort << " when functor is " << t->functor() << " and arg is " << arg << endl;
      return false;
    }
  }
  return true;
}

/**
 * Return true iff sorts of all terms (both functions and variables) match
 * in clause @c cl.
 *
 * There should not be any clause for which would this function return false.
 */
bool SortHelper::areSortsValid(Clause* cl)
{
  CALL("SortHelper::areSortsValid");

  static DHMap<unsigned,unsigned> varSorts;
  varSorts.reset();

  unsigned clen = cl->length();
  for (unsigned i=0; i<clen; i++) {
    if (!areSortsValid((*cl)[i], varSorts)) {
      return false;
    }
  }
  return true;
}

/**
 * Return true iff the argument sorts are valid in term or literal @c t0.
 * @c varSorts contains sorts of variables -- this map is used to check sorts of variables in the
 * term, and also is extended by sorts of variables that occurr for the first time.
 * @since 04/05/2013 Manchester, new NonVariableIterator is used
 * @author Andrei Voronkov
 */
bool SortHelper::areSortsValid(Term* t0, DHMap<unsigned,unsigned>& varSorts)
{
  CALL("SortHelper::areSortsValid");

  NonVariableIterator sit(t0,true);
  while (sit.hasNext()) {
    Term* t = sit.next().term();
    int idx = 0;
    TermList* args = t->args();
    while (!args->isEmpty()) {
      unsigned argSrt = getArgSort(t,idx);
      TermList arg = *args;
      if (arg.isVar()) {
	unsigned varSrt;
	if (!varSorts.findOrInsert(arg.var(), varSrt, argSrt)) {
	  //the variable is not new
	  if (varSrt != argSrt) {
	    return false;
	  }
	}
      }
      else {
	if (argSrt != getResultSort(arg.term())) {
	  return false;
	}
      }
      idx++;
      args=args->next();
    }
  }
  return true;
} // areSortsValid 
