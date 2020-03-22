
/*
 * File SATInference.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file SATInference.cpp
 * Implements class SATInference.
 */

#include "Kernel/Clause.hpp"
#include "Lib/TimeCounter.hpp"
#include "Shell/Statistics.hpp"

#include "SATInference.hpp"

#include "MinisatInterfacing.hpp"

namespace SAT
{

///////////////////////
// SATInference
//

/**
 * Collect first-order premises of @c cl into @c res. Make sure that elements in @c res are unique.
 */
void SATInference::collectFOPremises(SATClause* cl, Stack<Unit*>& acc)
{
  CALL("SATInference::collectFOPremises");
  
  collectFilteredFOPremises(cl,acc, [](SATClause*) {return true; } );
}


UnitList* SATInference::getFOPremises(SATClause* cl)
{
  CALL("SATInference::getFOPremises");
  ASS(cl);
  ASS(cl->inference());

  static Stack<Unit*> prems;
  prems.reset();

  collectFOPremises(cl, prems);

  UnitList* res = 0;
  while (prems.isNonEmpty()) {
    Unit* us = prems.pop();
    UnitList::push(us, res);
  }

  return res;
}

SATInference* SATInference::copy(const SATInference* inf)
{
  CALL("SATInference::copy");

  switch(inf->getType()) {
  case PROP_INF:
    return new PropInference(SATClauseList::copy(static_cast<const PropInference*>(inf)->getPremises()));
  case FO_CONVERSION:
    return new FOConversionInference(static_cast<const FOConversionInference*>(inf)->getOrigin());
  case ASSUMPTION:
    return new AssumptionInference();
  default:
    ASSERTION_VIOLATION;
  }
}

void SATInference::collectPropAxioms(SATClause* cl, SATClauseStack& res)
{
  CALL("SATInference::collectPropAxioms");

  static Stack<SATClause*> toDo;
  static DHSet<SATClause*> seen;
  toDo.reset();
  seen.reset();

  toDo.push(cl);
  while (toDo.isNonEmpty()) {
    SATClause* cur = toDo.pop();
    if (!seen.insert(cur)) {
      continue;
    }
    SATInference* sinf = cur->inference();
    ASS(sinf);
    switch(sinf->getType()) {
    case SATInference::FO_CONVERSION:
      res.push(cur);
      break;
    case SATInference::ASSUMPTION:
      break;
    case SATInference::PROP_INF:
    {
      PropInference* pinf = static_cast<PropInference*>(sinf);
      toDo.loadFromIterator(SATClauseList::Iterator(pinf->getPremises()));
      break;
    }
    default:
      ASSERTION_VIOLATION;
    }
  }
  makeUnique(res);
}

///////////////////////
// FOConversionInference
//

FOConversionInference::FOConversionInference(Unit* origin) : _origin(origin)
{
  _origin->incRefCnt();
}
FOConversionInference::FOConversionInference(Clause* cl) : _origin(cl)
{
  _origin->incRefCnt();
}
FOConversionInference::~FOConversionInference()
{
  CALL("FOConversionInference::~FOConversionInference");
  _origin->decRefCnt();
}

/////////////////////////

SATClauseList* InferenceFromSatRefutation::minimizePremises() {
  CALL("InferenceFromSatRefutation::minimizePremises");

  if (_minimized) {
    return nullptr;
  }

  TimeCounter tc(TC_SAT_PROOF_MINIMIZATION);

  SATClauseList* minimized = MinisatInterfacing::minimizePremiseList(_satPremises,_usedAssumptions);

  SATClause* newSatRef = new(0) SATClause(0);
  newSatRef->setInference(new PropInference(minimized));

  UnitList* newFOPrems = SATInference::getFOPremises(newSatRef);

  // cout << "Minimized from " << _premises->length() << " to " << newFOPrems->length() << endl;

  // "release" the old list
  {
    UnitList* it=_premises;
    while(it) {
      it->head()->decRefCnt();
      it=it->tail();
    }
  }

  // assign and keep the new one
  {
    _premises = newFOPrems;
    UnitList* it=_premises;
    unsigned maxInd = 0;
    while(it) {
      Unit* u = it->head();
      u->incRefCnt();

      Inference* inf = u->inference();
      Inference::Iterator iit = inf->iterator();
      while(inf->hasNext(iit)) {
        Unit* premUnit = inf->next(iit);
        if(premUnit->isClause()){
          unsigned ind = static_cast<Clause*>(premUnit)->inductionDepth();
          if(ind>maxInd){ maxInd=ind; }
        }
      }

      it=it->tail();
    }
    env.statistics->maxInductionDepth=maxInd;
  }

  // newSatRef->destroy(); // deletes also the inference and with it the list minimized, but not the clauses inside

  _minimized = true;

  return minimized;
}


}
