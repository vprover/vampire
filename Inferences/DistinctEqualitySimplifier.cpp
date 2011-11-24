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
  LOG("inf_des","can simplify: "<<cl->toString());
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
      LOG_TAUT("inf_des",cl);
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
  Inference* inf;
  if(premLst) {
    inf = new InferenceMany(Inference::DISTINCT_EQUALITY_REMOVAL, premLst);
  }
  else {
    inf = new Inference(Inference::DISTINCT_EQUALITY_REMOVAL);
  }
  Unit::InputType inpType = cl->inputType();
  Clause* res = Clause::fromStack(lits, inpType, inf);
  LOG_SIMPL("inf_des",cl,res);
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

  if(!t1.isTerm() || t1.term()->arity()!=0 || !t2.isTerm() || t2.term()->arity()!=0) {
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
    if(dlst2->member(candGrp)) {
      grp = candGrp;
      LOG("inf_des","must be distinct: "<<t1<<" and "<<t2<<" due to "<<grp);
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
