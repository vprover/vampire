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

}
