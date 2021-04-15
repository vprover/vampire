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
 * @file FormulaIndex.cpp
 * Implements class FormulaIndex.
 */

#include "ResultSubstitution.hpp"

#include "Kernel/Formula.hpp"

#include "FormulaIndex.hpp"

namespace Indexing
{

///////////////////////
// StringFormulaIndex
//

struct StringFormulaIndex::Entry2QR
{

  FormulaQueryResult operator()(const Entry& e) const
  {
    CALL("StringFormulaIndex::Entry2QR::operator()");

    return FormulaQueryResult(e.unit, e.formula, IdentitySubstitution::instance());
  }
};

vstring StringFormulaIndex::getKey(Formula* f)
{
  CALL("StringFormulaIndex::getKey");

  return f->toString();
}

FormulaQueryResultIterator StringFormulaIndex::getEquivalent(Formula* f)
{
  CALL("StringFormulaIndex::getEquivalent");

  vstring key = getKey(f);
  return pvi( getMappingIterator(_map.keyIterator(key), Entry2QR()) );
}

void StringFormulaIndex::insert(FormulaUnit* unit, Formula* f)
{
  CALL("StringFormulaIndex::insert");

  vstring key = getKey(f);
  _map.pushToKey(key, Entry(unit, f));
}

void StringFormulaIndex::remove(FormulaUnit* unit, Formula* f)
{
  CALL("StringFormulaIndex::remove");

  vstring key = getKey(f);
  ALWAYS(_map.removeFromKey(key, Entry(unit, f)));
}

}
