/**
 * @file SATInference.cpp
 * Implements class SATInference.
 */

#include "Kernel/Clause.hpp"
#include "Lib/TimeCounter.hpp"

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
    return new PropInference(static_cast<const PropInference*>(inf)->getPremises()->copy());
  case FO_CONVERSION:
    return new FOConversionInference(static_cast<const FOConversionInference*>(inf)->getOrigin());
  case FO_SPLITTING:
  {
    const FOSplittingInference* splInf = static_cast<const FOSplittingInference*>(inf);
    return new FOSplittingInference(splInf->getOrigin(), splInf->getNames()->copy());
  }
  case ASSUMPTION:
    return new AssumptionInference();
  default:
    ASSERTION_VIOLATION;
  }
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
// FOSplittingInference
//

FOSplittingInference::FOSplittingInference(Clause* origin, ClauseList* names) : _origin(origin), _names(names)
{
  CALL("FOSplittingInference::FOSplittingInference");

  _origin->incRefCnt();
  ClauseList::Iterator nit(_names);
  while (nit.hasNext()) {
    Clause* n = nit.next();
    n->incRefCnt();
  }
}

FOSplittingInference::~FOSplittingInference()
{
  CALL("FOSplittingInference::~FOSplittingInference");

  _origin->decRefCnt();
  while (_names) {
    Clause* n = ClauseList::pop(_names);
    n->decRefCnt();
  }
}

void InferenceFromSatRefutation::minimizePremises() {
  CALL("InferenceFromSatRefutation::minimizePremises");

  if (_minimized) {
    return;
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
    while(it) {
      it->head()->incRefCnt();
      it=it->tail();
    }
  }

  newSatRef->destroy(); // deletes also the inference and with it the list minimized, but not the clauses inside

  _minimized = true;
}


}
