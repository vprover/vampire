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

#include "SATInference.hpp"

namespace SAT
{

///////////////////////
// SATInference
//

UnitList* SATInference::getFOPremises(SATClause* cl)
{
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
  _origin->decRefCnt();
}

}
