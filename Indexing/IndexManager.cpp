/**
 * @file IndexManager.cpp
 * Implements class IndexManager.
 */

#include "../Lib/Exception.hpp"
#include "../Lib/Environment.hpp"

#include "../Kernel/Signature.hpp"
#include "../Saturation/SaturationAlgorithm.hpp"

#include "SubstitutionTree.hpp"
#include "IndexManager.hpp"

using namespace Lib;
using namespace Indexing;

Index* IndexManager::request(IndexType t)
{
  CALL("IndexManager::request");

  Entry e;
  if(_store.find(t,e)) {
    e.refCnt++;
  } else {
    e.index=create(t);
    e.refCnt=1;
  }
  _store.set(t,e);
  return e.index;
}

void IndexManager::release(IndexType t)
{
  CALL("IndexManager::release");

  Entry e;
  ALWAYS(_store.find(t,e));

  e.refCnt--;
  if(e.refCnt==0) {
    delete e.index;
    _store.remove(t);
  } else {
    _store.set(t,e);
  }
}

bool IndexManager::contains(IndexType t)
{
  return _store.find(t);
}

Index* IndexManager::create(IndexType t)
{
  CALL("IndexManager::create");

  Index* res;
  switch(t) {
  case GENERATING_SUBST_TREE:
    res=new SubstitutionTree(2*env.signature->predicates());
    res->attachContainer(_alg->getGenerationClauseContainer());
    break;
  default:
    INVALID_OPERATION("Unsupported IndexType.");
  }
  return res;
}
