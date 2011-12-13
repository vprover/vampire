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

UnitList* SATInference::getFOPremises(SATClause* cl)
{
  CALL("SATInference::getFOPremises");
  ASS(cl);
  ASS(cl->inference());

  static ClauseStack prems;
  static SATClauseStack toDo;
  static DHSet<SATClause*> seen;
  prems.reset();
  toDo.reset();
  seen.reset();

  toDo.push(cl);
  while(toDo.isNonEmpty()) {
    SATClause* cur = toDo.pop();
    if(!seen.insert(cur)) {
      continue;
    }
    SATInference* sinf = cur->inference();
    ASS(sinf);
    switch(sinf->getType()) {
    case SATInference::FO_CONVERSION:
      prems.push(static_cast<FOConversionInference*>(sinf)->getOrigin().cl());
      break;
    case SATInference::ASSUMPTION:
      break;
    case SATInference::PROP_INF:
    {
      PropInference* pinf = static_cast<PropInference*>(sinf);
      toDo.loadFromIterator(SATClauseList::Iterator(pinf->getPremises()));
      break;
    }
    case SATInference::FO_SPLITTING:
    {
      FOSplittingInference* inf = static_cast<FOSplittingInference*>(sinf);
      prems.push(inf->getOrigin());
      prems.loadFromIterator(ClauseList::Iterator(inf->getNames()));
      break;
    }
    default:
      ASSERTION_VIOLATION;
    }
  }

  makeUnique(prems);

  UnitList* res = 0;
  UnitList::pushFromIterator(ClauseStack::Iterator(prems), res);

  return res;
}

///////////////////////
// FOConversionInference
//

FOConversionInference::FOConversionInference(UnitSpec origin) : _origin(origin)
{
  _origin.unit()->incRefCnt();
}
FOConversionInference::FOConversionInference(Clause* cl) : _origin(UnitSpec(cl, false))
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
  while(nit.hasNext()) {
    Clause* n = nit.next();
    n->incRefCnt();
  }
}

FOSplittingInference::~FOSplittingInference()
{
  CALL("FOSplittingInference::~FOSplittingInference");

  _origin->decRefCnt();
  while(_names) {
    Clause* n = ClauseList::pop(_names);
    n->decRefCnt();
  }
}


}
