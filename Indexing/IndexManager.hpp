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

#include "Forwards.hpp"
#include "Lib/DHMap.hpp"
#include "Index.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Saturation;

class IndexManager
{
public:
  explicit IndexManager(SaturationAlgorithm& alg);

  template<typename IndexType> static unsigned indexId();

  template<typename IndexType, bool isGenerating>
  static auto key()
  {
    static_assert(std::is_base_of<Index, IndexType>());
    return std::make_pair(indexId<IndexType>(), isGenerating);
  }

  template<typename IndexType, bool isGenerating>
  IndexType* request()
  {
    Entry* e;
    if (_store.getValuePtr(key<IndexType, isGenerating>(), e)) {
      e->index = new IndexType(_alg);
      attachContainer<isGenerating>(e->index);
      e->refCnt=1;
    } else {
      e->refCnt++;
    }
    return static_cast<IndexType*>(e->index);
  }

  template<typename IndexType, bool isGenerating>
  void release()
  {
    auto ptr = _store.findPtr(key<IndexType, isGenerating>());
    ASS(ptr);

    ptr->refCnt--;
    if (ptr->refCnt == 0) {
      delete ptr->index;
      _store.remove(key<IndexType, isGenerating>());
    }
  }

private:
  template<bool isGenerating>
  void attachContainer(Index* i);

  struct Entry {
    Index* index;
    int refCnt;
  };
  SaturationAlgorithm& _alg;
  // indices mapped by unsigned index id and Boolean telling
  // whether they are for the generating container or not
  DHMap<std::pair<unsigned, bool>,Entry> _store;
};

};

#endif /*__IndexManager__*/
