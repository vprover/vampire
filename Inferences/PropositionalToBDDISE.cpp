/**
 * @file PropositionalToBDDISE.cpp
 * Implements class PropositionalToBDDISE.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/Stack.hpp"

#include "../Kernel/BDD.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/InferenceStore.hpp"
#include "../Kernel/Signature.hpp"
#include "../Kernel/Term.hpp"

#include "../Shell/Statistics.hpp"
#include "../Shell/Options.hpp"

#include "PropositionalToBDDISE.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;


Clause* PropositionalToBDDISE::simplify(Clause* c)
{
  CALL("PropositionalToBDDISE::simplify");

  BDD* bdd=BDD::instance();

  unsigned propCnt=0;

  BDDNode* propPart=bdd->getFalse();

  static Stack<Clause*> premises(8);
  premises.reset();

  unsigned clen=c->length();
  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*c)[i];

    if(lit->arity()==0) {
      propCnt++;
    }
  }

  if(!propCnt) {
    return c;
  }



  InferenceStore::SplittingRecord* srec=new InferenceStore::SplittingRecord(c);

  unsigned nlen=clen-propCnt;

  Inference* inf=new Inference(Inference::TAUTOLOGY_INTRODUCTION);

  Clause* newCl=new(nlen) Clause(nlen, c->inputType(), inf);
  newCl->setAge(c->age());

  unsigned newIndex=0;
  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*c)[i];
    if(lit->arity()==0) {
      int name;
      Clause* premise;
      bool newPremise;

      getPropPredName(lit, name, premise, newPremise);
      propPart=bdd->disjunction(propPart, bdd->getAtomic(name, lit->isPositive()));

      premises.push(premise);
      srec->namedComps.push(make_pair(name, premise));
    } else  {
      (*newCl)[newIndex++]=lit;
    }
  }
  ASS_EQ(newIndex, nlen);

  newCl->setProp(bdd->getTrue());
  InferenceStore::instance()->recordNonPropInference(newCl);

  newCl->setProp(propPart);

  srec->setResult(newCl);
  srec->oldResBDD=bdd->getTrue();
  InferenceStore::instance()->recordSplitting(newCl, bdd->getTrue(), newCl->prop(),
	    propCnt, premises.begin(), srec);


  return newCl;
}


void PropositionalToBDDISE::getPropPredName(Literal* lit, int& name, Clause*& premise, bool& newPremise)
{
  CALL("PropositionalToBDDISE::getPropPredName");
  ASS_EQ(lit->arity(), 0);

  unsigned pred=lit->functor();
  int* pname;
  if(_propPredNames.getValuePtr(pred, pname)) {
    *pname=BDD::instance()->getNewVar(pred);

    if(env.options->showDefinitions()) {
      env.out << "Definition: " << BDD::instance()->getPropositionalPredicateName(*pname)
	    << " <=> " << env.signature->predicateName(pred) << endl;
    }
  }
  name=*pname;

  Clause** ppremise;
  if(lit->isPositive()) {
    _propPredPosNamePremises.getValuePtr(pred, ppremise, 0);
  } else {
    _propPredNegNamePremises.getValuePtr(pred, ppremise, 0);
  }
  newPremise=*ppremise;
  if(!*ppremise) {
    Clause* cl=new(1) Clause(1,Clause::AXIOM,new Inference(Inference::CLAUSE_NAMING));
    (*cl)[0]=lit;
    cl->setProp( BDD::instance()->getAtomic(name, lit->isNegative()) );
    InferenceStore::instance()->recordNonPropInference(cl);
    *ppremise=cl;
  }
  premise=*ppremise;
}

}
