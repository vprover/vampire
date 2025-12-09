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

#include "Saturation/SaturationAlgorithm.hpp"

#include "AcyclicityIndex.hpp"
#include "CodeTreeInterfaces.hpp"
#include "LiteralIndex.hpp"
#include "TermIndex.hpp"
#include "Inferences/ALASCA/Demodulation.hpp"
#include "Inferences/ALASCA/FourierMotzkin.hpp"
#include "Inferences/ALASCA/Superposition.hpp"
#include "Inferences/ALASCA/BinaryResolution.hpp"
#include "Inferences/ALASCA/Coherence.hpp"

#include "IndexManager.hpp"
#include "Kernel/ALASCA/Index.hpp"

using namespace Lib;
using namespace Indexing;

#define INDEX_ID_IMPL(IndexType, Id) template<> unsigned IndexManager::indexId<IndexType>() { return Id; }

INDEX_ID_IMPL(AlascaIndex<ALASCA::Demodulation::Lhs>,                                   0)
INDEX_ID_IMPL(AlascaIndex<ALASCA::Demodulation::Rhs>,                                   1)
INDEX_ID_IMPL(AlascaIndex<ALASCA::CoherenceConf<NumTraits<RealConstantType>>::Lhs>,     2)
INDEX_ID_IMPL(AlascaIndex<ALASCA::CoherenceConf<NumTraits<RealConstantType>>::Rhs>,     3)
INDEX_ID_IMPL(AlascaIndex<ALASCA::CoherenceConf<NumTraits<RationalConstantType>>::Lhs>, 4)
INDEX_ID_IMPL(AlascaIndex<ALASCA::SuperpositionConf::Lhs>,                              5)
INDEX_ID_IMPL(AlascaIndex<ALASCA::SuperpositionConf::Rhs>,                              6)
INDEX_ID_IMPL(AlascaIndex<ALASCA::FourierMotzkinConf::Lhs>,                             7)
INDEX_ID_IMPL(AlascaIndex<ALASCA::FourierMotzkinConf::Rhs>,                             8)
INDEX_ID_IMPL(AlascaIndex<ALASCA::BinaryResolutionConf::Lhs>,                           9)
INDEX_ID_IMPL(AlascaIndex<ALASCA::BinaryResolutionConf::Rhs>,                          10)
INDEX_ID_IMPL(AcyclicityIndex,                                                         11)
INDEX_ID_IMPL(FSDLiteralIndex,                                                         12)
INDEX_ID_IMPL(RewriteRuleIndex,                                                        13)
INDEX_ID_IMPL(InductionTermIndex,                                                      14)
INDEX_ID_IMPL(DemodulationLHSIndex,                                                    15)
INDEX_ID_IMPL(BinaryResolutionIndex,                                                   16)
INDEX_ID_IMPL(SuperpositionLHSIndex,                                                   17)
INDEX_ID_IMPL(UnitClauseLiteralIndex,                                                  18)
INDEX_ID_IMPL(SkolemisingFormulaIndex,                                                 19)
INDEX_ID_IMPL(BackwardSubsumptionIndex,                                                20)
INDEX_ID_IMPL(CodeTreeSubsumptionIndex,                                                21)
INDEX_ID_IMPL(DemodulationSubtermIndex,                                                22)
INDEX_ID_IMPL(StructInductionTermIndex,                                                23)
INDEX_ID_IMPL(NonUnitClauseLiteralIndex,                                               24)
INDEX_ID_IMPL(SuperpositionSubtermIndex,                                               25)
INDEX_ID_IMPL(UnitClauseWithALLiteralIndex,                                            26)
INDEX_ID_IMPL(FwSubsSimplifyingLiteralIndex,                                           27)
INDEX_ID_IMPL(NonUnitClauseWithALLiteralIndex,                                         28)
INDEX_ID_IMPL(UnitIntegerComparisonLiteralIndex,                                       29)

IndexManager::IndexManager(SaturationAlgorithm& alg)
  : _alg(alg)
{ }

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
