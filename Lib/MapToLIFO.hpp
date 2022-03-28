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
 * @file MapToLIFO.hpp
 * Defines class MapToLIFO
 */

#ifndef __MapToLIFO__
#define __MapToLIFO__

#include "DHMap.hpp"
#include "List.hpp"
#include "Hash.hpp"
#include "VirtualIterator.hpp"
#include "Metaiterators.hpp"

namespace  Lib
{

template<typename K,typename V, class Hash1, class Hash2>
class MapToLIFO
{
public:
  typedef List<V> ValList;
  typedef typename ValList::Iterator ValIterator;
  typedef DHMap<K,ValList*, Hash1, Hash2> InnerMap;

  ~MapToLIFO()
  {
    CALL("MapToLIFO::~MapToLIFO");

    makeEmpty();
  }

  void reset()
  {
    CALL("MapToLIFO::reset");

    if(!_data.size()) {
      return;
    }
    typename InnerMap::Iterator it(_data);
    while(it.hasNext()) {
      ValList::destroy(it.next());
    }
    _data.reset();
  }

  void pushToKey(K key, V val)
  {
    CALL("MapToLIFO::pushToKey");

    ValList** pLst;
    _data.getValuePtr(key, pLst, 0);
    ValList::push(val, *pLst);
  }

  void pushManyToKey(K key, ValList* val)
  {
    CALL("MapToLIFO::pushManyToKey");

    ValList** pLst;
    _data.getValuePtr(key, pLst, 0);
    *pLst=ValList::concat(val, *pLst);
  }

  V popFromKey(K key)
  {
    CALL("MapToLIFO::popFromKey");

    ValList** pLst;
    _data.getValuePtr(key, pLst, 0);
    ASS(*pLst);
    V res=ValList::pop(*pLst);
    if(*pLst==0) {
      _data.remove(key);
    }
    return res;
  }

  /**
   * If @c val is stored under @c key, remove it and return true;
   * otherwise return false.
   *
   * The complexity is linar with the size of the list stored under
   * @c key.
   */
  bool removeFromKey(K key, V val)
  {
    CALL("MapToLIFO::removeFromKey");

    if(!_data.find(key)) {
      return false;
    }

    ValList** pLst;
    _data.getValuePtr(key, pLst);

    if(!(*pLst)->member(val)) {
      return false;
    }

    *pLst = (*pLst)->remove(val);
    if(!*pLst) {
      _data.remove(key);
    }
    return true;
  }

  bool isKeyEmpty(K key) const
  {
    CALL("MapToLIFO::isKeyEmpty");

    bool found=_data.find(key);
    ASS(!found || _data.get(key)!=0);
    return !found;
  }


  ValIterator keyIterator(K key) const
  {
    ValList* lst=0;
    _data.find(key, lst); //if the key isn't found, the lst remains unchanged
    return ValIterator(lst);
  }

  VirtualIterator<V> allValIterator() const
  {
    return pvi( getMapAndFlattenIterator( KeyIterator(*this), KeyToIterFn(*this) ) );
  }

  ValList* keyVals(K key)
  {
    ValList* lst=0;
    _data.find(key, lst); //if the key isn't found, the lst remains unchanged
    return lst;
  }

  const ValList* keyVals(K key) const
  {
    return const_cast<MapToLIFO*>(this)->keyVals(key);
  }

  size_t keyValCount(K key) const
  {
    return keyVals(key)->length();
  }


  class KeyIterator
  {
  public:
    DECL_ELEMENT_TYPE(K);

    KeyIterator(const MapToLIFO& m) : it(m._data) {}

    bool hasNext()
    {
      return it.hasNext();
    }
    K next()
    {
      return it.nextKey();
    }
  private:
    typename InnerMap::Iterator it;
  };

private:
  struct KeyToIterFn
  {
    KeyToIterFn(const MapToLIFO& parent) : _par(parent) {}
    typename ValList::Iterator operator() (K key)
    {
      return _par.keyIterator(key);
    }
  private:
    const MapToLIFO& _par;
  };

  void makeEmpty()
  {
    typename InnerMap::Iterator it(_data);
    while(it.hasNext()) {
      ValList::destroy(it.next());
    }
    _data.reset();
  }

  InnerMap _data;
};

}



#endif /* __MapToLIFO__ */
