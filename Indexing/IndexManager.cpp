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

#include "CodeTreeInterfaces.hpp"
#include "AcyclicityIndex.hpp"
#include "LiteralIndex.hpp"
#include "TermIndex.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Inferences/ALASCA/Demodulation.hpp"
#include "Inferences/ALASCA/FourierMotzkin.hpp"
#include "Inferences/ALASCA/Superposition.hpp"
#include "Inferences/ALASCA/BinaryResolution.hpp"
#include "Inferences/ALASCA/Coherence.hpp"

#include "IndexManager.hpp"
#include "Kernel/ALASCA/Index.hpp"

using namespace Lib;
using namespace Indexing;

SIMP_INDEX_IMPL(AlascaIndex<ALASCA::Demodulation::Lhs>)
SIMP_INDEX_IMPL(AlascaIndex<ALASCA::Demodulation::Rhs>)
SIMP_INDEX_IMPL(DemodulationLHSIndex)
SIMP_INDEX_IMPL(CodeTreeSubsumptionIndex)
SIMP_INDEX_IMPL(BackwardSubsumptionIndex)
SIMP_INDEX_IMPL(FwSubsSimplifyingLiteralIndex)
SIMP_INDEX_IMPL(RewriteRuleIndex)
SIMP_INDEX_IMPL(UnitClauseLiteralIndex)
SIMP_INDEX_IMPL(DemodulationSubtermIndex)
SIMP_INDEX_IMPL(SkolemisingFormulaIndex)
SIMP_INDEX_IMPL(FSDLiteralIndex)

GEN_INDEX_IMPL(AlascaIndex<ALASCA::CoherenceConf<NumTraits<RealConstantType>>::Lhs>)
GEN_INDEX_IMPL(AlascaIndex<ALASCA::CoherenceConf<NumTraits<RealConstantType>>::Rhs>)
GEN_INDEX_IMPL(AlascaIndex<ALASCA::CoherenceConf<NumTraits<RationalConstantType>>::Lhs>)
GEN_INDEX_IMPL(AlascaIndex<ALASCA::SuperpositionConf::Lhs>)
GEN_INDEX_IMPL(AlascaIndex<ALASCA::SuperpositionConf::Rhs>)
GEN_INDEX_IMPL(AlascaIndex<ALASCA::FourierMotzkinConf::Lhs>)
GEN_INDEX_IMPL(AlascaIndex<ALASCA::FourierMotzkinConf::Rhs>)
GEN_INDEX_IMPL(AlascaIndex<ALASCA::BinaryResolutionConf::Lhs>)
GEN_INDEX_IMPL(AlascaIndex<ALASCA::BinaryResolutionConf::Rhs>)
GEN_INDEX_IMPL(SuperpositionSubtermIndex)
GEN_INDEX_IMPL(SuperpositionLHSIndex)
GEN_INDEX_IMPL(AcyclicityIndex)
GEN_INDEX_IMPL(BinaryResolutionIndex)
GEN_INDEX_IMPL(NonUnitClauseLiteralIndex)
GEN_INDEX_IMPL(NonUnitClauseWithALLiteralIndex)
GEN_INDEX_IMPL(UnitClauseLiteralIndex)
GEN_INDEX_IMPL(UnitClauseWithALLiteralIndex)
GEN_INDEX_IMPL(InductionTermIndex)
GEN_INDEX_IMPL(StructInductionTermIndex)
GEN_INDEX_IMPL(UnitIntegerComparisonLiteralIndex)

IndexManager::IndexManager(SaturationAlgorithm& alg)
  : _alg(alg)
{}

template<bool isGenerating>
void IndexManager::attachContainer(Index &i)
{
  if constexpr (isGenerating) {
    i.attachContainer(_alg.getGeneratingClauseContainer());
  } else {
    i.attachContainer(_alg.getSimplifyingClauseContainer());
  }
}

template void IndexManager::attachContainer<true>(Index &);
template void IndexManager::attachContainer<false>(Index &);
