/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef REQUESTEDINDEX_HPP
#define REQUESTEDINDEX_HPP

#include "Saturation/SaturationAlgorithm.hpp"

namespace Indexing {

template <typename IndexType, bool isGenerating>
class RequestedIndex final
{
  public:
    RequestedIndex() = default;

    // Disallow copying
    RequestedIndex(RequestedIndex const&) = delete;
    RequestedIndex& operator=(RequestedIndex const&) = delete;

    // Moving transfers ownership of the index
    RequestedIndex(RequestedIndex&& other) noexcept
      : _index{std::exchange(other._index, nullptr)}
      , _indexManager{std::exchange(other._indexManager, nullptr)}
    { }

    // Moving transfers ownership of the index
    RequestedIndex& operator=(RequestedIndex&& other) noexcept
    {
      this->swap(other);
      return *this;
    }

    ~RequestedIndex()
    {
      release();
    }

    void request(SaturationAlgorithm* salg)
    {
      ASS(!_index);
      ASS(!_indexManager);
      _indexManager = salg->getIndexManager();
      _index = _indexManager->request<IndexType, isGenerating>();
    }

    // NOTE: release() might be called multiple times (manually and by destructor)
    void release()
    {
      _index = nullptr;
      if (_indexManager != nullptr) {
        _indexManager->release<IndexType, isGenerating>();
        _indexManager = nullptr;
      }
    }

    IndexType& operator*() const
    {
      ASS(_index);
      return *_index;
    }

    IndexType* operator->() const
    {
      ASS(_index);
      return _index;
    }

    IndexType* get() const
    {
      return _index;
    }

    void swap(RequestedIndex& other)
    {
      using std::swap;
      swap(_index, other._index);
      swap(_indexManager, other._indexManager);
    }

  private:
    IndexType* _index = nullptr;
    IndexManager* _indexManager = nullptr;
};


}

#endif /* !REQUESTEDINDEX_HPP */
