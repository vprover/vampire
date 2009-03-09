/**
 * @file InverseLookup.hpp
 * Defines class InverseLookup.
 */


#ifndef __InverseLookup__
#define __InverseLookup__

#include "Hash.hpp"
#include "DHMap.hpp"

namespace Lib {

template<typename T>
class InverseLookup
{
private:
  //private and undefined operator= and copy constructor to avoid implicitly generated ones
  InverseLookup(const InverseLookup&);
  InverseLookup& operator=(const InverseLookup&);
public:
  template<typename Arr>
  InverseLookup(Arr arr, size_t size)
  {
    for(size_t i=0;i<size;i++) {
      ALWAYS(_data.insert(arr[i],i));
    }
  }

  template<typename Arr>
  void update(Arr arr)
  {
    size_t size=_data.size();
    for(size_t i=0;i<size;i++) {
      ALWAYS(_data.set(arr[i],i));
    }
  }

  size_t get(T* val)
  {
    return _data.get(val);
  }

private:
  DHMap<T*,size_t,PtrIdentityHash> _data;
};

};

#endif /* __InverseLookup__ */
