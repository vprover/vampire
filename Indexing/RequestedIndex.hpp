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

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Lib/Allocator.hpp"
#include "Lib/STL.hpp"

namespace Indexing {


template <typename Index>
class RequestedIndex final
{
  public:
    CLASS_NAME(RequestedIndex);
    USE_ALLOCATOR(RequestedIndex);

    RequestedIndex()
    { }

    // Disallow copying
    RequestedIndex(RequestedIndex const&) = delete;
    RequestedIndex& operator=(RequestedIndex const&) = delete;

    // Moving transfers ownership of the index
    RequestedIndex(RequestedIndex&& other) noexcept
      : _index{std::exchange(other._index, nullptr)}
      , _type{other._type}
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

    void request(IndexManager* indexManager, IndexType type)
    {
      ASS(!_index);
      ASS(!_indexManager);
      _indexManager = indexManager;
      _type = type;
      _index = dynamic_cast<Index*>(_indexManager->request(type));
      ASS(_index != nullptr);  // if this fails, the wrong index type was requested
    }

    // NOTE: release() might be called multiple times (manually and by destructor)
    void release()
    {
      _index = nullptr;
      if (_indexManager != nullptr) {
        _indexManager->release(_type);
        _indexManager = nullptr;
      }
    }

    Index& operator*() const
    {
      ASS(_index);
      return *_index;
    }

    Index* operator->() const
    {
      ASS(_index);
      return _index;
    }

    Index* get() const
    {
      ASS(_index);
      return _index;
    }

    void swap(RequestedIndex& other)
    {
      using std::swap;
      swap(_index, other._index);
      swap(_type, other._type);
      swap(_indexManager, other._indexManager);
    }

  private:
    Index* _index = nullptr;
    IndexType _type;
    IndexManager* _indexManager = nullptr;
};


}

#endif /* !REQUESTEDINDEX_HPP */
