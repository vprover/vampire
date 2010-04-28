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
      ValList* lst=it.next();
      lst->destroy();
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

  bool isKeyEmpty(K key)
  {
    CALL("MapToLIFO::isKeyEmpty");

    bool found=_data.find(key);
    ASS(!found || _data.get(key)!=0);
    return !found;
  }


  typename ValList::Iterator keyIterator(K key)
  {
    ValList* lst=0;
    _data.find(key, lst); //if the key isn't found, the lst remains unchanged
    return typename ValList::Iterator(lst);
  }

  VirtualIterator<V> allValIterator()
  {
    return pvi( getMapAndFlattenIterator( KeyIterator(*this), KeyToIterFn(*this) ) );
  }

  ValList* keyVals(K key)
  {
    ValList* lst=0;
    _data.find(key, lst); //if the key isn't found, the lst remains unchanged
    return lst;
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
    KeyToIterFn(MapToLIFO& parent) : _par(parent) {}
    DECL_RETURN_TYPE(typename ValList::Iterator);
    OWN_RETURN_TYPE operator() (K key)
    {
      return _par.keyIterator(key);
    }
  private:
    MapToLIFO& _par;
  };

  void makeEmpty()
  {
    typename InnerMap::Iterator it(_data);
    while(it.hasNext()) {
      ValList* lst=it.next();
      lst->destroy();
    }
    _data.reset();
  }

  InnerMap _data;
};

}



#endif /* __MapToLIFO__ */
