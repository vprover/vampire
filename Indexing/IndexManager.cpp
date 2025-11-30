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
 * @file IndexManager.cpp
 * Implements class IndexManager.
 */

#include "Indexing/Index.hpp"
#include "Lib/Exception.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "LiteralIndex.hpp"
#include "TermIndex.hpp"
#include "TermSubstitutionTree.hpp"
#include "Inferences/ALASCA/Demodulation.hpp"
#include "Inferences/ALASCA/FourierMotzkin.hpp"
#include "Inferences/ALASCA/Superposition.hpp"
#include "Inferences/ALASCA/BinaryResolution.hpp"
#include "Inferences/ALASCA/Coherence.hpp"

#include "IndexManager.hpp"
#include "Kernel/ALASCA/Index.hpp"

using namespace Lib;
using namespace Indexing;

IndexManager::IndexManager(SaturationAlgorithm& alg)
  : _alg(alg)
{ }

Index* IndexManager::request(IndexType t)
{
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
  Entry e=_store.get(t);

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

template<bool isGenerating>
void IndexManager::attachContainer(Index* i)
{
  if constexpr (isGenerating) {
    i->attachContainer(_alg.getGeneratingClauseContainer());
  } else {
    i->attachContainer(_alg.getSimplifyingClauseContainer());
  }
}

template void IndexManager::attachContainer<true>(Index*);
template void IndexManager::attachContainer<false>(Index*);

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

Index* IndexManager::create(IndexType t)
{
  Index* res;
  using TermSubstitutionTree    = Indexing::TermSubstitutionTree<TermLiteralClause>;

  bool isGenerating;
  switch(t) {
  case URR_UNIT_CLAUSE_SUBST_TREE:
    res = new UnitClauseLiteralIndex(_alg);
    isGenerating = true;
    break;
  case URR_UNIT_CLAUSE_WITH_AL_SUBST_TREE:
    res = new UnitClauseWithALLiteralIndex();
    isGenerating = true;
    break;
  case URR_NON_UNIT_CLAUSE_SUBST_TREE:
    res = new NonUnitClauseLiteralIndex();
    isGenerating = true;
    break;
  case URR_NON_UNIT_CLAUSE_WITH_AL_SUBST_TREE:
    res=new NonUnitClauseWithALLiteralIndex();
    isGenerating = true;
    break;

  case ALASCA_FWD_DEMODULATION_SUBST_TREE:
    res = new AlascaIndex<ALASCA::Demodulation::Lhs>();
    isGenerating = false;
    break;

  case ALASCA_BWD_DEMODULATION_SUBST_TREE:
    res = new AlascaIndex<ALASCA::Demodulation::Rhs>();
    isGenerating = false;
    break;

  case ALASCA_FOURIER_MOTZKIN_LHS_SUBST_TREE:
    res=new AlascaIndex<Inferences::ALASCA::FourierMotzkin::Lhs>();
    isGenerating = true;
    break;

  case ALASCA_FOURIER_MOTZKIN_RHS_SUBST_TREE:
    res=new AlascaIndex<Inferences::ALASCA::FourierMotzkin::Rhs>();
    isGenerating = true;
    break;

  case ALASCA_BINARY_RESOLUTION_LHS_SUBST_TREE:
    res = new AlascaIndex<Inferences::ALASCA::BinaryResolution::Lhs>();
    isGenerating = true;
    break;

  case ALASCA_BINARY_RESOLUTION_RHS_SUBST_TREE:
    res = new AlascaIndex<Inferences::ALASCA::BinaryResolution::Rhs>();
    isGenerating = true;
    break;

  case ALASCA_SUPERPOSITION_LHS_SUBST_TREE:
    res = new AlascaIndex<Inferences::ALASCA::Superposition::Lhs>();
    isGenerating = true;
    break;

  case ALASCA_SUPERPOSITION_RHS_SUBST_TREE:
    res = new AlascaIndex<Inferences::ALASCA::Superposition::Rhs>();
    isGenerating = true;
    break;

  case ALASCA_COHERENCE_LHS_SUBST_TREE:
    res = new AlascaIndex<Inferences::ALASCA::Coherence<RealTraits>::Lhs>();
    isGenerating = true;
    break;

  case ALASCA_COHERENCE_RHS_SUBST_TREE:
    res = new AlascaIndex<Inferences::ALASCA::Coherence<RealTraits>::Rhs>();
    isGenerating = true;
    break;

  case SKOLEMISING_FORMULA_INDEX:
    res = new SkolemisingFormulaIndex(new Indexing::TermSubstitutionTree<TermWithValue<Kernel::TermList>>());
    isGenerating = false;
    break;

  default:
    INVALID_OPERATION("Unsupported IndexType.");
  }
  if(isGenerating) {
    res->attachContainer(_alg.getGeneratingClauseContainer());
  }
  else {
    res->attachContainer(_alg.getSimplifyingClauseContainer());
  }
  return res;
}
