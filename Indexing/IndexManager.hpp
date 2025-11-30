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

#include "Lib/ConstTypeId.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Saturation;

class IndexManager
{
public:
  explicit IndexManager(SaturationAlgorithm& alg);

  template<typename IndexType, bool isGenerating>
  constexpr static auto key()
  { return std::make_pair(ConstTypeId::getTypeId<IndexType>(), isGenerating); }

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

  template<typename IndexType, bool isGenerating>
  bool contains()
  {
    return _store.find(key<IndexType, isGenerating>());
  }

  template<typename IndexType, bool isGenerating> IndexType* get()
  {
    return static_cast<IndexType*>(_store.get(key<IndexType, isGenerating>()).index);
  }

private:
  template<bool isGenerating>
  void attachContainer(Index* i);

  struct Entry {
    Index* index;
    int refCnt;
  };
  SaturationAlgorithm& _alg;
  DHMap<std::pair<ConstTypeId,bool>,Entry> _store;
};

};

#endif /*__IndexManager__*/
