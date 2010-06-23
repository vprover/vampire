/**
 * @file PropositionalToBDDISE.cpp
 * Implements class PropositionalToBDDISE.
 */

#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/BDD.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Shell/Statistics.hpp"
#include "Shell/Options.hpp"

#include "PropositionalToBDDISE.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;


Clause* PropositionalToBDDISE::simplify(Clause* c)
{
  CALL("PropositionalToBDDISE::simplify");

  BDD* bdd=BDD::instance();

  ASS(bdd->isFalse(c->prop()));

  unsigned propCnt=0;
  BDDNode* propPart=bdd->getFalse();

  static Stack<Clause*> premises(8);
  premises.reset();

  unsigned clen=c->length();
  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*c)[i];

    if(canBddize(lit)) {
      propCnt++;
    }
  }

  if(!propCnt) {
    return c;
  }



  unsigned nlen=clen-propCnt;

  Inference* inf=new Inference1(Inference::BDDZATION, c);

  Clause* newCl=new(nlen) Clause(nlen, c->inputType(), inf);
  newCl->setAge(c->age());

  List<int>* propVars=0;

  unsigned newIndex=0;
  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*c)[i];
    if(canBddize(lit)) {
      int name = getPropPredName(lit);
      List<int>::push(name, propVars);
      propPart = bdd->disjunction(propPart, bdd->getAtomic(name, lit->isPositive()));
    } else {
      (*newCl)[newIndex++]=lit;
    }
  }
  ASS_EQ(newIndex, nlen);

  newCl->initProp(propPart);

  if(bdd->isTrue(propPart)) {
    newCl->destroyIfUnnecessary();
    return 0;
  }

  InferenceStore::instance()->recordNonPropInference(newCl);
  InferenceStore::instance()->recordBddizeVars(newCl, propVars);

  return newCl;
}

bool PropositionalToBDDISE::canBddize(Literal* l)
{
  return l->arity()==0 && l->color()==COLOR_TRANSPARENT &&
    (!env.options->showSymbolElimination() || l->skip()) &&
    !env.signature->getPredicate(l->functor())->cfName();
}
int PropositionalToBDDISE::getPropPredName(Literal* lit)
{
  CALL("PropositionalToBDDISE::getPropPredName");
  ASS_EQ(lit->arity(), 0);

  unsigned pred=lit->functor();
  int* pname;
  if(_propPredNames.getValuePtr(pred, pname)) {
    *pname=BDD::instance()->getNewVar(pred);
  }
  return *pname;
}

}
