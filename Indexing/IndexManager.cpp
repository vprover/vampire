/**
 * @file IndexManager.cpp
 * Implements class IndexManager.
 */

#include "../Lib/Exception.hpp"

#include "../Saturation/SaturationAlgorithm.hpp"

#include "ArithmeticIndex.hpp"
#include "CodeTreeInterfaces.hpp"
#include "LiteralIndex.hpp"
#include "LiteralSubstitutionTree.hpp"
#include "TermIndex.hpp"
#include "TermSubstitutionTree.hpp"

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

  Entry e=_store.get(t);

  e.refCnt--;
  if(e.refCnt==0) {
    if(t==GENERATING_SUBST_TREE) {
      _genLitIndex=0;
    }
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
  LiteralIndexingStructure* is;
  TermIndexingStructure* tis;
  switch(t) {
  case GENERATING_SUBST_TREE:
#if COMPIT_GENERATOR==2
    is=new CompitUnificationRecordingLiteralSubstitutionTree();
#else
    is=new LiteralSubstitutionTree();
#endif
    _genLitIndex=is;
    res=new GeneratingLiteralIndex(is);
    res->attachContainer(_alg->getGenerationClauseContainer());
    break;
  case SIMPLIFYING_SUBST_TREE:
    is=new LiteralSubstitutionTree();
    res=new SimplifyingLiteralIndex(is);
    res->attachContainer(_alg->getSimplificationClauseContainer());
    break;
  case SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE:
    is=new LiteralSubstitutionTree();
    res=new UnitClauseSimplifyingLiteralIndex(is);
    res->attachContainer(_alg->getSimplificationClauseContainer());
    break;

  case SUPERPOSITION_SUBTERM_SUBST_TREE:
#if COMPIT_GENERATOR==1
    tis=new CompitUnificationRecordingTermSubstitutionTree();
#else
    tis=new TermSubstitutionTree();
#endif
    res=new SuperpositionSubtermIndex(tis);
    res->attachContainer(_alg->getGenerationClauseContainer());
    break;
  case SUPERPOSITION_LHS_SUBST_TREE:
    tis=new TermSubstitutionTree();
    res=new SuperpositionLHSIndex(tis);
    res->attachContainer(_alg->getGenerationClauseContainer());
    break;

  case DEMODULATION_SUBTERM_SUBST_TREE:
    tis=new TermSubstitutionTree();
    res=new DemodulationSubtermIndex(tis);
    res->attachContainer(_alg->getSimplificationClauseContainer());
    break;
  case DEMODULATION_LHS_SUBST_TREE:
//    tis=new TermSubstitutionTree();
    tis=new CodeTreeTIS();
    res=new DemodulationLHSIndex(tis);
    res->attachContainer(_alg->getSimplificationClauseContainer());
    break;

  case FW_SUBSUMPTION_CODE_TREE:
    res=new CodeTreeSubsumptionIndex();
    res->attachContainer(_alg->getSimplificationClauseContainer());
    break;

  case FW_SUBSUMPTION_SUBST_TREE:
    is=new LiteralSubstitutionTree();
//    is=new CodeTreeLIS();
    res=new FwSubsSimplifyingLiteralIndex(is);
    res->attachContainer(_alg->getSimplificationClauseContainer());
    break;

  case REWRITE_RULE_SUBST_TREE:
    is=new LiteralSubstitutionTree();
    res=new RewriteRuleIndex(is);
    res->attachContainer(_alg->getSimplificationClauseContainer());
    break;

  case ARITHMETIC_INDEX:
    res=new ArithmeticIndex();
    res->attachContainer(_alg->getSimplificationClauseContainer());
    break;

  default:
    INVALID_OPERATION("Unsupported IndexType.");
  }
  return res;
}
