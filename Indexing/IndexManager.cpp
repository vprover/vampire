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

/**
 * IMPORTANT: Keep these values distinct from each other!
 */
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

IndexManager::IndexManager(SaturationAlgorithm& alg)
  : _alg(alg) {}

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
