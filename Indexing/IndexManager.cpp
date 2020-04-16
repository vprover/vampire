
/*
 * File IndexManager.cpp.
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
 * @file IndexManager.cpp
 * Implements class IndexManager.
 */

#include "Lib/Exception.hpp"

#include "Kernel/Grounder.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "AcyclicityIndex.hpp"
#include "ArithmeticIndex.hpp"
#include "CodeTreeInterfaces.hpp"
#include "GroundingIndex.hpp"
#include "LiteralIndex.hpp"
#include "LiteralSubstitutionTree.hpp"
#include "TermIndex.hpp"
#include "TermSubstitutionTree.hpp"

#include "IndexManager.hpp"

using namespace Lib;
using namespace Indexing;

IndexManager::IndexManager(SaturationAlgorithm* alg) : _alg(alg), _genLitIndex(0)
{
  CALL("IndexManager::IndexManager");

  if(alg) {
    attach(alg);
  }
}

IndexManager::~IndexManager()
{
  CALL("IndexManager::~IndexManager");

  if(_alg) {
    release(GENERATING_SUBST_TREE);
  }
}

void IndexManager::setSaturationAlgorithm(SaturationAlgorithm* alg)
{
  CALL("IndexManager::setSaturationAlgorithm");
  ASS(!_alg);
  ASS(alg);

  _alg = alg;
  attach(alg);
}

void IndexManager::attach(SaturationAlgorithm* salg)
{
  CALL("IndexManager::attach");

  request(GENERATING_SUBST_TREE);
}

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

/**
 * If IndexManager contains index @b t, return pointer to it
 *
 * The pointer can become invalid after return from the code that
 * has requested it through this function.
 */
Index* IndexManager::get(IndexType t)
{
  return _store.get(t).index;
}

/**
 * Provide index form the outside
 *
 * There must not be index of the same type from before.
 * The provided index is never deleted by the IndexManager.
 */
void IndexManager::provideIndex(IndexType t, Index* index)
{
  CALL("IndexManager::provideIndex");
  ASS(!_store.find(t));

  Entry e;
  e.index = index;
  e.refCnt = 1; //reference to 1, so that we never delete the provided index
  _store.set(t,e);
}

Index* IndexManager::create(IndexType t)
{
  CALL("IndexManager::create");

  Index* res;
  LiteralIndexingStructure* is;
  TermIndexingStructure* tis;

  bool isGenerating;
  static bool const useConstraints = env.options->unificationWithAbstraction()!=Options::UnificationWithAbstraction::OFF;

  switch(t) {
  case GENERATING_SUBST_TREE:
    is=new LiteralSubstitutionTree(useConstraints);
#if VDEBUG
    //is->markTagged();
#endif
    _genLitIndex=is;
    res=new GeneratingLiteralIndex(is);
    isGenerating = true;
    break;
  case SIMPLIFYING_SUBST_TREE:
    is=new LiteralSubstitutionTree();
    res=new SimplifyingLiteralIndex(is);
    isGenerating = false;
    break;

  case SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE:
    is=new LiteralSubstitutionTree();
    res=new UnitClauseLiteralIndex(is);
    isGenerating = false;
    break;
  case GENERATING_UNIT_CLAUSE_SUBST_TREE:
    is=new LiteralSubstitutionTree();
    res=new UnitClauseLiteralIndex(is);
    isGenerating = true;
    break;
  case GENERATING_NON_UNIT_CLAUSE_SUBST_TREE:
    is=new LiteralSubstitutionTree();
    res=new NonUnitClauseLiteralIndex(is);
    isGenerating = true;
    break;

  case SUPERPOSITION_SUBTERM_SUBST_TREE:
    tis=new TermSubstitutionTree(useConstraints);
#if VDEBUG
    //tis->markTagged();
#endif
    res=new SuperpositionSubtermIndex(tis, _alg->getOrdering());
    isGenerating = true;
    break;
  case SUPERPOSITION_LHS_SUBST_TREE:
    tis=new TermSubstitutionTree(useConstraints);
    res=new SuperpositionLHSIndex(tis, _alg->getOrdering(), _alg->getOptions());
    isGenerating = true;
    break;

  case ACYCLICITY_INDEX:
    tis = new TermSubstitutionTree();
    res = new AcyclicityIndex(tis);
    isGenerating = true;
    break;

  case DEMODULATION_SUBTERM_SUBST_TREE:
    tis=new TermSubstitutionTree();
    res=new DemodulationSubtermIndex(tis);
    isGenerating = false;
    break;
  case DEMODULATION_LHS_SUBST_TREE:
//    tis=new TermSubstitutionTree();
    tis=new CodeTreeTIS();
    res=new DemodulationLHSIndex(tis, _alg->getOrdering(), _alg->getOptions());
    isGenerating = false;
    break;

  case FW_SUBSUMPTION_CODE_TREE:
    res=new CodeTreeSubsumptionIndex();
    isGenerating = false;
    break;

  case FW_SUBSUMPTION_SUBST_TREE:
    is=new LiteralSubstitutionTree();
//    is=new CodeTreeLIS();
    res=new FwSubsSimplifyingLiteralIndex(is);
    isGenerating = false;
    break;

  case FSD_SUBST_TREE:
    is = new LiteralSubstitutionTree();
    res = new FSDLiteralIndex(is);
    isGenerating = false;
    break;

  case REWRITE_RULE_SUBST_TREE:
    is=new LiteralSubstitutionTree();
    res=new RewriteRuleIndex(is, _alg->getOrdering());
    isGenerating = false;
    break;

  case GLOBAL_SUBSUMPTION_INDEX:
    res = new GroundingIndex(_alg->getOptions());
    isGenerating = false;
    break;

//  case ARITHMETIC_INDEX:
//    res=new ArithmeticIndex();
//    isGenerating = false;
//    break;

  default:
    INVALID_OPERATION("Unsupported IndexType.");
  }
  if(isGenerating) {
    res->attachContainer(_alg->getGeneratingClauseContainer());
  }
  else {
    res->attachContainer(_alg->getSimplifyingClauseContainer());
  }
  return res;
}
