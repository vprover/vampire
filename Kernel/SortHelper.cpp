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
 * Return type of term or literal @c t
 */
BaseType& SortHelper::getType(Term* t)
{
  if(t->isLiteral()) {
    Signature::Symbol* sym = env.signature->getPredicate(t->functor());
    return *sym->predType();
  }
  else {
    return *env.signature->getFunction(t->functor())->fnType();
  }
}

/**
 * Return the sort of a non-variable term t. This function cannot be applied
 * to a special term, such as if-then-else.
 */
unsigned SortHelper::getResultSort(Term* t)
{
  CALL("SortHelper::getArgSort(Term*,unsigned)");
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

  if(!t->isSpecial()) {
    result = getResultSort(t);
    return true;
  }
  //we may have many nested special terms. to be safe, we traverse them using our own stack.
  static Stack<Term*> candidates;
  candidates.reset();

  for(;;) {
    switch(t->functor()) {
    case Term::SF_TERM_ITE:
      if(t->nthArgument(0)->isTerm()) { candidates.push(t->nthArgument(0)->term()); }
      if(t->nthArgument(1)->isTerm()) { candidates.push(t->nthArgument(1)->term()); }
      break;
    case Term::SF_LET_TERM_IN_TERM:
    case Term::SF_LET_FORMULA_IN_TERM:
      if(t->nthArgument(0)->isTerm()) { candidates.push(t->nthArgument(0)->term()); }
      break;
    default:
      ASS(!t->isSpecial());
      result = getResultSort(t);
      return true;
    }
    if(candidates.isEmpty()) {
      return false;
    }
    t = candidates.pop();
  }
}

bool SortHelper::tryGetResultSort(TermList t, unsigned& result)
{
  CALL("tryGetResultSort(TermList,unsigned&)");
  if(t.isVar()) { return false; }
  return tryGetResultSort(t.term(), result);
}

/**
 * Return argument sort of term or literal @c t
 */
unsigned SortHelper::getArgSort(Term* t, unsigned argIndex)
{
  CALL("SortHelper::getArgSort(Term*,unsigned)");
  ASS_L(argIndex, t->arity());

  if(t->isLiteral() && static_cast<Literal*>(t)->isEquality()) {
    return getEqualityArgumentSort(static_cast<Literal*>(t));
  }

  return getType(t).arg(argIndex);
}

unsigned SortHelper::getEqualityArgumentSort(const Literal* lit)
{
  CALL("SortHelper::getEqualityArgumentSort");
  ASS(lit->isEquality());

  if(lit->isTwoVarEquality()) {
    return lit->twoVarEqSort();
  }

  TermList arg1 = *lit->nthArgument(0);
  unsigned srt1;
  if(tryGetResultSort(arg1, srt1)) {
    return srt1;
  }

  TermList arg2 = *lit->nthArgument(1);
  unsigned srt2;
  ALWAYS(tryGetResultSort(arg2, srt2));
  return srt2;
}

/**
 * Return sort of term @c trm that appears inside literal @c lit.
 */
unsigned SortHelper::getTermSort(TermList trm, Literal* lit)
{
  CALL("SortHelper::getTermSort");

  if(trm.isTerm()) {
    return getResultSort(trm.term());
  }
  else {
    ASS(trm.isVar());
    return getVariableSort(trm, lit);
  }
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
  while(sfit.hasNext()) {
    Formula* sf = sfit.next();
    if(sf->connective()!=LITERAL) {
      continue;
    }
    Literal* lit = sf->literal();

    if(!lit->containsSubterm(varTerm)) {
      continue;
    }
    res = getVariableSort(varTerm, lit);
    return true;
  }
  return false;
}

/**
 * Insert variable sorts from @c t0 into @c map. If a variable
 * is in map already (or appears multiple times), assert that
 * the sorts are equal.
 * @c t0 can be either term or literal.
 */
void SortHelper::collectVariableSorts(Term* t0, DHMap<unsigned,unsigned>& map)
{
  CALL("SortHelper::collectVariableSorts(Term*,...)");

  if(t0->ground()) {
    return;
  }

  NonVariableIterator sit(t0);
  Term* t = t0;

  //in the first iteration, t is equal to t0, in subsequent ones
  //we iterate through its non-ground non-variable subterms
  for(;;) {
    int idx = 0;
    TermList* args = t->args();
    while(!args->isEmpty()) {
      if(args->isOrdinaryVar()) {
	unsigned varNum = args->var();
	unsigned varSort = getArgSort(t, idx);
	LOG("srt_collect_var_sorts","seen variable "<<varNum<<" in "<<t->toString()<<" with sort "<<env.sorts->sortName(varSort));
	if(!map.insert(varNum, varSort)) {
	  ASS_EQ(varSort, map.get(varNum));
	}
      }
      idx++;
      args=args->next();
    }

    for(;;) {
      if(!sit.hasNext()) {
        return;
      }
      t = sit.next().term();
      if(t->ground()) {
	sit.right();
      }
      else {
	break;
      }
    }
  }
}

/**
 * Insert variable sorts from @c f into @c map. If a variable
 * is in map already (or appears multiple times), assert that
 * the sorts are equal.
 */
void SortHelper::collectVariableSorts(Formula* f, DHMap<unsigned,unsigned>& map)
{
  CALL("SortHelper::collectVariableSorts(Formula*,...)");
  LOG("srt_collect_var_sorts","collecting variable sorts for formula " << f->toString());

  SubformulaIterator sfit(f);
  while(sfit.hasNext()) {
    Formula* sf = sfit.next();
    if(sf->connective()!=LITERAL) {
      continue;
    }
    LOG("srt_collect_var_sorts","collecting for subformula: "<<sf->toString());
    Literal* lit = sf->literal();

    collectVariableSorts(lit, map);
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

  LOG("srt_collect_var_sorts","collection variable sorts for unit " << u->toString());

  if(!u->isClause()) {
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    collectVariableSorts(fu->formula(), map);
    return;
  }

  Clause* cl = static_cast<Clause*>(u);
  Clause::Iterator cit(*cl);
  while(cit.hasNext()) {
    Literal* l = cit.next();
    collectVariableSorts(l, map);
  }
}

/**
 * If variable @c var occurrs in term @c t, assign into @c result its
 * sort and return true. Otherwise return false.
 */
bool SortHelper::tryGetVariableSort(TermList var, Term* t0, unsigned& result)
{
  CALL("SortHelper::tryGetVariableSort");

  if(t0->ground()) {
    return false;
  }

  NonVariableIterator sit(t0);
  Term* t = t0;

  //in the first iteration, t is equal to t0, in subsequent ones
  //we iterate through its non-ground non-variable subterms
  for(;;) {
    int idx = 0;
    TermList* args = t->args();
    while(!args->isEmpty()) {
      if(*args==var) {
	result = getArgSort(t, idx);
        return true;
      }
      idx++;
      args=args->next();
    }

    for(;;) {
      if(!sit.hasNext()) {
        return false;
      }
      t = sit.next().term();
      if(t->ground()) {
	sit.right();
      }
      else {
	break;
      }
    }
  }
  ASSERTION_VIOLATION;
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
  for(unsigned i=0; i<clen; i++) {
    if(!areSortsValid((*cl)[i], varSorts)) {
      return false;
    }
  }
  return true;
}

/**
 * Return true iff sorts are valid in term or literal @c t0. @c varSorts contains
 * sorts of variables -- this map is used to check sorts of variables in the
 * term, and also is extended by sorts of variables that occurr for the first time.
 */
bool SortHelper::areSortsValid(Term* t0, DHMap<unsigned,unsigned>& varSorts)
{
  CALL("SortHelper::areSortsValid");

  NonVariableIterator sit(t0);
  Term* t = t0;

  //in the first iteration, t is equal to t0, in subsequent ones
  //we iterate through its non-variable subterms
  for(;;) {
    int idx = 0;
    TermList* args = t->args();
    while(!args->isEmpty()) {
      unsigned argSrt = getArgSort(t, idx);
      TermList arg = *args;
      if(arg.isVar()) {
	unsigned varSrt;
	if(!varSorts.findOrInsert(arg.var(), varSrt, argSrt)) {
	  //the variable is not new
	  if(varSrt!=argSrt) {
	    return false;
	  }
	}
      }
      else {
	if(argSrt!=getResultSort(arg.term())) {
	  return false;
	}
      }
      idx++;
      args=args->next();
    }

    if(!sit.hasNext()) {
      return true;
    }
    t = sit.next().term();
  }
  ASSERTION_VIOLATION;
}

