/**
 * @file SATInference.cpp
 * Implements class SATInference.
 */

#include "Kernel/Clause.hpp"

#include "SATInference.hpp"

namespace SAT
{

///////////////////////
// SATInference
//

/**
 * Collect first-order premises of @c cl into @c res. Make sure that elements in @c res are unique.
 */
void SATInference::collectFOPremises(SATClause* cl, Stack<UnitSpec>& acc)
{
  CALL("SATInference::collectFOPremises");
  
  collectFilteredFOPremises(cl,acc, [](SATClause*) {return true; } );
}


UnitList* SATInference::getFOPremises(SATClause* cl)
{
  CALL("SATInference::getFOPremises");
  ASS(cl);
  ASS(cl->inference());

  static Stack<UnitSpec> prems;
  prems.reset();

  collectFOPremises(cl, prems);

  UnitList* res = 0;
  while (prems.isNonEmpty()) {
    UnitSpec us = prems.pop();

    //ASS_REP(us.withoutProp() || BDD::instance()->isTrue(us.prop()), us.toString());
    UnitList::push(us.unit(), res);
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

FOConversionInference::FOConversionInference(UnitSpec origin) : _origin(origin)
{
  _origin.unit()->incRefCnt();
}
FOConversionInference::FOConversionInference(Clause* cl) : _origin(UnitSpec(cl))
{
  _origin.unit()->incRefCnt();
}
FOConversionInference::~FOConversionInference()
{
  CALL("FOConversionInference::~FOConversionInference");
  _origin.unit()->decRefCnt();
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


}
