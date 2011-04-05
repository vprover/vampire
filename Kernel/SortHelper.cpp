/**
 * @file SortHelper.cpp
 * Implements class SortHelper.
 */

#include "Lib/Environment.hpp"

#include "Signature.hpp"
#include "Term.hpp"

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


}
