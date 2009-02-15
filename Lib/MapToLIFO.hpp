/**
 * @file MapToLIFO.hpp
 * Defines class MapToLIFO
 */

#ifndef __MapToLIFO__
#define __MapToLIFO__

#include "DHMap.hpp"
#include "List.hpp"
#include "Hash.hpp"

namespace  Lib
{

template<typename K,typename V, class Hash1=Hash, class Hash2=Hash>
class MapToLIFO
{
  typedef List<V> ValList;
  typedef DHMap<K,ValList*, Hash1, Hash2> InnerMap;
public:
  ~MapToLIFO()
  {
    makeEmpty();
  }

  void pushToKey(K key, V val)
  {
    ValList** pLst;
    _data.getValuePtr(key, pLst, 0);
    ValList::push(val, *pLst);
  }
  V popFromKey(K key)
  {
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
    bool found=_data.find(key);
    ASS(!found || _data.get(key)!=0);
    return !found;
  }

private:
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
