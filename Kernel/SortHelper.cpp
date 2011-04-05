/**
 * @file SortHelper.cpp
 * Implements class SortHelper.
 */

#include "Lib/Environment.hpp"

#include "Signature.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"

#include "SortHelper.hpp"

namespace Kernel
{

unsigned SortHelper::getResultSort(Term* t)
{
  CALL("SortHelper::getArgSort(Term*,unsigned)");
  ASS(!t->isLiteral());

  Signature::Symbol* sym = env.signature->getFunction(t->functor());
  return sym->fnType()->result();
}

unsigned SortHelper::getArgSort(Term* t, unsigned argIndex)
{
  CALL("SortHelper::getArgSort(Term*,unsigned)");
  ASS_L(argIndex, t->arity());
  ASS(!t->isLiteral());

  Signature::Symbol* sym = env.signature->getFunction(t->functor());
  return sym->fnType()->arg(argIndex);
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

unsigned SortHelper::getArgSort(Literal* lit, unsigned argIndex)
{
  CALL("SortHelper::getArgSort(Literal*,unsigned)");
  ASS_L(argIndex, lit->arity());

  if(lit->isEquality()) {
    return getEqualityArgumentSort(lit);
  }
  Signature::Symbol* sym = env.signature->getPredicate(lit->functor());
  return sym->predType()->arg(argIndex);
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
 * Return sort of variable @c var in literal @c lit
 *
 * Variable @c var must occurr in @c lit.
 */
unsigned SortHelper::getVariableSort(TermList var, Literal* lit)
{
  CALL("SortHelper::getVariableSort(TermList,Literal*)");

  int idx = 0;
  TermList* args = lit->args();
  while(!args->isEmpty()) {
    if(*args==var) {
      return getArgSort(lit, idx);
    }
    idx++;
    args=args->next();
  }

  args = lit->args();
  while(!args->isEmpty()) {
    if(args->isTerm()) {
      unsigned res;
      if(tryGetVariableSort(var, args->term(), res)) {
	return res;
      }
    }
    args=args->next();
  }
  ASSERTION_VIOLATION;
}

/**
 * Return sort of variable @c var in term @c t
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

}
