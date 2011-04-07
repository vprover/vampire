/**
 * @file SortHelper.cpp
 * Implements class SortHelper.
 */

#include "Lib/Environment.hpp"

#include "Clause.hpp"
#include "Signature.hpp"
#include "Sorts.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"

#include "SortHelper.hpp"

namespace Kernel
{

/**
 * Return type of term or literal @c t
 */
BaseType& SortHelper::getType(Term* t)
{
  if(t->isLiteral()) {
    return *env.signature->getPredicate(t->functor())->predType();
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
    return getEqualityArgumentSort(static_cast<Literal*>(t));
  }

  return getType(t).arg(argIndex);
}

unsigned SortHelper::getEqualityArgumentSort(Literal* lit)
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

  static DHMap<TermList,unsigned> varSorts;
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
bool SortHelper::areSortsValid(Term* t0, DHMap<TermList,unsigned>& varSorts)
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
	if(!varSorts.findOrInsert(arg, varSrt, argSrt)) {
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




