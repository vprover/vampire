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
  DECL_RETURN_TYPE(FormulaQueryResult);

  OWN_RETURN_TYPE operator()(const Entry& e) const
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


///////////////////////
// AIGFormulaIndex
//

struct AIGFormulaIndex::Entry2QR
{
  DECL_RETURN_TYPE(FormulaQueryResult);

  OWN_RETURN_TYPE operator()(const Entry& e) const
  {
    CALL("AIGFormulaIndex::Entry2QR::operator()");

    return FormulaQueryResult(e.unit, e.formula, IdentitySubstitution::instance());
  }
};

Formula* AIGFormulaIndex::getKey(Formula* f)
{
  CALL("AIGFormulaIndex::getKey");

  return _aig.apply(f).first;
}

FormulaQueryResultIterator AIGFormulaIndex::getEquivalent(Formula* f)
{
  CALL("StringFormulaIndex::getEquivalent");

  Formula* key = getKey(f);
  return pvi( getMappingIterator(_map.keyIterator(key), Entry2QR()) );
}

void AIGFormulaIndex::insert(FormulaUnit* unit, Formula* f)
{
  CALL("StringFormulaIndex::insert");

  Formula* key = getKey(f);
  _map.pushToKey(key, Entry(unit, f));
}

void AIGFormulaIndex::remove(FormulaUnit* unit, Formula* f)
{
  CALL("StringFormulaIndex::remove");

  Formula* key = getKey(f);
  ALWAYS(_map.removeFromKey(key, Entry(unit, f)));
}


}
