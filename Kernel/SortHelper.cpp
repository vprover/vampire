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

#undef LOGGING
#define LOGGING 0

namespace Kernel
{

/**
 * Return type of term or literal @c t
 */
BaseType& SortHelper::getType(Term* t)
{
  if(t->isLiteral()) {
    Signature::Symbol* sym = env.signature->getPredicate(t->functor());
    LOGV(sym->name());
    LOGV(sym->predType()->toString());
    return *sym->predType();
  }
  else {
    return *env.signature->getFunction(t->functor())->fnType();
  }
}

unsigned SortHelper::getResultSort(Term* t)
{
  CALL("SortHelper::getArgSort(Term*,unsigned)");
  ASS(!t->isLiteral());

  Signature::Symbol* sym = env.signature->getFunction(t->functor());
  return sym->fnType()->result();
}

/**
 * Return argument sort of term or literal @c t
 */
unsigned SortHelper::getArgSort(Term* t, unsigned argIndex)
{
  CALL("SortHelper::getArgSort(Term*,unsigned)");
  ASS_L(argIndex, t->arity());

  if(t->isLiteral() && static_cast<Literal*>(t)->isEquality()) {
    LOG("getting eq sort");
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
  if(arg1.isTerm()) {
    return getResultSort(arg1.term());
  }
  TermList arg2 = *lit->nthArgument(1);
  ASS(arg2.isTerm()); //otherwise lit->isTwoVarEquality() would hold
  return getResultSort(arg2.term());
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
	LOGV(t->toString());
	LOGV(varNum);
	LOGV(varSort);
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
  LOG("collection variable sorts for formula " << f->toString());

  LOGV(f->toString());
  SubformulaIterator sfit(f);
  while(sfit.hasNext()) {
    Formula* sf = sfit.next();
    if(sf->connective()!=LITERAL) {
      continue;
    }
    LOGV(sf->toString());
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

  LOG("collection variable sorts for unit " << u->toString());

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

}




