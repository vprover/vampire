
/*
 * File InverseLookup.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file InverseLookup.hpp
 * Defines class InverseLookup.
 */


#ifndef __InverseLookup__
#define __InverseLookup__

#include "Hash.hpp"
#include "DHMap.hpp"

#include "Lib/Allocator.hpp"

namespace Lib {

template<typename T>
class InverseLookup
{
private:
  //private and undefined operator= and copy constructor to avoid implicitly generated ones
  InverseLookup(const InverseLookup&);
  InverseLookup& operator=(const InverseLookup&);
public:
  CLASS_NAME(InverseLookup<T>);
  USE_ALLOCATOR(InverseLookup<T>);

  template<typename Arr>
  InverseLookup(Arr arr, size_t size)
  {
    CALL("InverseLookup::InverseLookup");
    for(size_t i=0;i<size;i++) {
      ALWAYS(_data.insert(arr[i],i));
    }
  }

  template<typename Arr>
  void update(Arr arr)
  {
    CALL("InverseLookup::update");
    size_t size=_data.size();
    for(size_t i=0;i<size;i++) {
      NEVER(_data.set(arr[i],i));
    }
  }

  size_t get(T* val)
  {
    CALL("InverseLookup::get");
    return _data.get(val);
  }

private:
  DHMap<T*,size_t,PtrIdentityHash> _data;
};

};

#endif /* __InverseLookup__ */
