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

#include "Index.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "IndexManager.hpp"

using namespace Lib;
using namespace Indexing;

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
