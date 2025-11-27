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

#include "AcyclicityIndex.hpp"
#include "CodeTreeInterfaces.hpp"
#include "LiteralIndex.hpp"
#include "LiteralSubstitutionTree.hpp"
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

IndexManager::IndexManager(SaturationAlgorithm* alg)
  : _alg(alg)
  , _uwa(AbstractionOracle::create())
  , _uwaFixedPointIteration(env.options->unificationWithAbstractionFixedPointIteration())
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
  ASS(!_store.find(t));

  Entry e;
  e.index = index;
  e.refCnt = 1; //reference to 1, so that we never delete the provided index
  _store.set(t,e);
}

Index* IndexManager::create(IndexType t)
{
  Index* res;
  using TermSubstitutionTree    = Indexing::TermSubstitutionTree<TermLiteralClause>;
  using LiteralSubstitutionTree = Indexing::LiteralSubstitutionTree<LiteralClause>;

  bool isGenerating;
  switch(t) {
  case BINARY_RESOLUTION_SUBST_TREE:
    res = new BinaryResolutionIndex(new LiteralSubstitutionTree());
    isGenerating = true;
    break;
  case BACKWARD_SUBSUMPTION_SUBST_TREE:
    res = new BackwardSubsumptionIndex(new LiteralSubstitutionTree());
    isGenerating = false;
    break;
  case FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE:
    res = new UnitClauseLiteralIndex(new LiteralSubstitutionTree());
    isGenerating = false;
    break;
  case URR_UNIT_CLAUSE_SUBST_TREE:
    res = new UnitClauseLiteralIndex(new LiteralSubstitutionTree());
    isGenerating = true;
    break;
  case URR_UNIT_CLAUSE_WITH_AL_SUBST_TREE:
    res=new UnitClauseWithALLiteralIndex(new LiteralSubstitutionTree());
    isGenerating = true;
    break;
  case URR_NON_UNIT_CLAUSE_SUBST_TREE:
    res  =new NonUnitClauseLiteralIndex(new LiteralSubstitutionTree());
    isGenerating = true;
    break;
  case URR_NON_UNIT_CLAUSE_WITH_AL_SUBST_TREE:
    res=new NonUnitClauseWithALLiteralIndex(new LiteralSubstitutionTree());
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

  case SUPERPOSITION_SUBTERM_SUBST_TREE:
    res = new SuperpositionSubtermIndex(new TermSubstitutionTree(), _alg->getOrdering());
    isGenerating = true;
    break;

  case SUPERPOSITION_LHS_SUBST_TREE:
    res = new SuperpositionLHSIndex(new TermSubstitutionTree(), _alg->getOrdering(), _alg->getOptions());
    isGenerating = true;
    break;

  case SKOLEMISING_FORMULA_INDEX:
    res = new SkolemisingFormulaIndex(new Indexing::TermSubstitutionTree<TermWithValue<Kernel::TermList>>());
    isGenerating = false;
    break;

   case ACYCLICITY_INDEX:
    res = new AcyclicityIndex(new TermSubstitutionTree());
    isGenerating = true;
    break;

  case DEMODULATION_SUBTERM_SUBST_TREE:
    res = new DemodulationSubtermIndex(new TermSubstitutionTree(),_alg->getOptions());
    isGenerating = false;
    break;
  case DEMODULATION_LHS_CODE_TREE:
    res = new DemodulationLHSIndex(new CodeTreeTIS<DemodulatorData>(), _alg->getOrdering(), _alg->getOptions());
    isGenerating = false;
    break;

  case FW_SUBSUMPTION_CODE_TREE:
    res = new CodeTreeSubsumptionIndex();
    isGenerating = false;
    break;

  case FW_SUBSUMPTION_SUBST_TREE:
    res = new FwSubsSimplifyingLiteralIndex(new LiteralSubstitutionTree());
    isGenerating = false;
    break;

  case FSD_SUBST_TREE:
    res = new FSDLiteralIndex(new LiteralSubstitutionTree());
    isGenerating = false;
    break;

  case REWRITE_RULE_SUBST_TREE:
    res = new RewriteRuleIndex(new LiteralSubstitutionTree(), _alg->getOrdering());
    isGenerating = false;
    break;

  case UNIT_INT_COMPARISON_INDEX:
    res = new UnitIntegerComparisonLiteralIndex(new LiteralSubstitutionTree());
    isGenerating = true;
    break;

  case INDUCTION_TERM_INDEX:
    res = new InductionTermIndex(new TermSubstitutionTree(), _alg->getOptions());
    isGenerating = true;
    break;

  case STRUCT_INDUCTION_TERM_INDEX:
    res = new StructInductionTermIndex(new TermSubstitutionTree(), _alg->getOptions());
    isGenerating = true;
    break;

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
