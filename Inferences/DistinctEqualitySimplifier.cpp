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
 * @file DistinctEqualitySimplifier.cpp
 * Implements class DistinctEqualitySimplifier.
 */

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"

#include "DistinctEqualitySimplifier.hpp"

namespace Inferences
{

Clause* DistinctEqualitySimplifier::simplify(Clause* cl)
{
  CALL("DistinctEqualitySimplifier::simplify");

  if(!canSimplify(cl)) {
    return cl;
  }
  static LiteralStack lits;
  static Stack<Unit*> prems;
  prems.reset();
  lits.reset();
  unsigned clen = cl->length();
  for(unsigned i=0; i<clen; i++) {
    Literal* lit = (*cl)[i];
    unsigned grp;
    if(!lit->isEquality() || !mustBeDistinct(*lit->nthArgument(0),*lit->nthArgument(1), grp)) {
      lits.push(lit);
      continue;
    }
    if(lit->isNegative()) {
      //we have a clause that is implied by the distinctness constraints
      return 0;
    }
    Unit* prem = env.signature->getDistinctGroupPremise(grp);
    if(prem) {
      prems.push(prem);
    }
    //we have a false literal - equality on two distinct constants
  }

  //we must have removed some literal, since the canSimplify()
  //function returned true
  ASS_L(lits.size(), clen);

  prems.push(cl);
  UnitList* premLst = 0;
  UnitList::pushFromIterator(Stack<Unit*>::Iterator(prems), premLst);
  ASS(premLst); // at least, because of "prems.push(cl);" above

  Clause* res = Clause::fromStack(lits,
      SimplifyingInferenceMany(InferenceRule::DISTINCT_EQUALITY_REMOVAL, premLst));
  return res;
}

bool DistinctEqualitySimplifier::mustBeDistinct(TermList t1, TermList t2)
{
  CALL("DistinctEqualitySimplifier::mustBeDistinct/2");

  unsigned aux;
  return mustBeDistinct(t1, t2, aux);
}

bool DistinctEqualitySimplifier::mustBeDistinct(TermList t1, TermList t2, unsigned& grp)
{
  CALL("DistinctEqualitySimplifier::mustBeDistinct/3");

  if(!t1.isTerm() || t1.term()->arity()!=0 || !t2.isTerm() || t2.term()->arity()!=0 || t1.term() == t2.term()) {
    return false;
  }
  unsigned fn1 = t1.term()->functor();
  unsigned fn2 = t2.term()->functor();
  const List<unsigned>* dlst1 = env.signature->getFunction(fn1)->distinctGroups();
  if(!dlst1) {
    return false;
  }
  const List<unsigned>* dlst2 = env.signature->getFunction(fn2)->distinctGroups();
  if(!dlst2) {
    return false;
  }
  List<unsigned>::Iterator dl1it(dlst1);
  while(dl1it.hasNext()) {
    unsigned candGrp = dl1it.next(); //candidate group
    if(List<unsigned>::member(candGrp, dlst2)) {
      grp = candGrp;
      return true;
    }
  }
  return false;
}

bool DistinctEqualitySimplifier::canSimplify(Clause* cl)
{
  CALL("DistinctEqualitySimplifier::canSimplify");

  unsigned clen = cl->length();
  for(unsigned i=0; i<clen; i++) {
    Literal* lit = (*cl)[i];
    if(lit->isEquality() && mustBeDistinct(*lit->nthArgument(0),*lit->nthArgument(1))) {
      return true;
    }
  }
  return false;
}

}
