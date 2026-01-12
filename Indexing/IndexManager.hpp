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
 * @file IndexManager.hpp
 * Defines class IndexManager
 *
 */

#ifndef __IndexManager__
#define __IndexManager__

#include <memory>

#include "Forwards.hpp"
#include "Index.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Saturation;

class IndexManager
{
public:
  explicit IndexManager(SaturationAlgorithm& alg);

  template<typename IndexType, bool isGenerating>
  std::shared_ptr<IndexType> tryGet() {
    return getUniqueWeakPtr<IndexType, isGenerating>().lock();
  }

  template<typename IndexType, bool isGenerating>
  std::shared_ptr<IndexType> get() {
    auto &weak = getUniqueWeakPtr<IndexType, isGenerating>();
    auto shared = weak.lock();
    if (shared) {
      return shared;
    }

    shared = std::make_shared<IndexType>(_alg);
    weak = shared;
    attachContainer<isGenerating>(*shared);
    return shared;
  }

private:
  template<typename IndexType, bool isGenerating>
  std::weak_ptr<IndexType> &getUniqueWeakPtr();

  template<bool isGenerating>
  void attachContainer(Index &i);
  SaturationAlgorithm& _alg;
};

#define INDEX_IMPL(IndexType, isGenerating)                                 \
  template<> std::weak_ptr<IndexType> &                                     \
  IndexManager::getUniqueWeakPtr<IndexType, isGenerating>() {               \
    static std::weak_ptr<IndexType> index;                                  \
    return index;                                                           \
  }

#define GEN_INDEX_IMPL(IndexType) INDEX_IMPL(IndexType, /*isGenerating=*/true)
#define SIMP_INDEX_IMPL(IndexType) INDEX_IMPL(IndexType, /*isGenerating=*/false)

};

#endif /*__IndexManager__*/
