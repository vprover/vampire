/**
 * @file DArray.hpp
 * Defines a class of self-deallocating arrays. They should be used instead
 * of Array when the size is known in advance
 *
 * @since 30/12/2007 Manchester
 */

#ifndef __ArrayMap__
#define __ArrayMap__

#include "../Forwards.hpp"

#include "DArray.hpp"

namespace Lib {

template<typename T>
struct ArrayMapEntry
{
  ArrayMapEntry() : _timestamp(0) {}

  T _obj;
  unsigned _timestamp;
};

template<typename T>
class ArrayMap
: DArray<ArrayMapEntry<T> >
{
  typedef ArrayMapEntry<T> Entry;
public:
  ArrayMap() : DArray<Entry>(8), _timestamp(1) {}
  ArrayMap(size_t size) : DArray<Entry>(size), _timestamp(1) {}

  void reset()
  {
    _timestamp++;
    if(_timestamp==0) {
      Entry* nptr=DArray<Entry>::_array;
      Entry* afterLast=DArray<Entry>::_array+DArray<Entry>::_capacity;
      while(nptr!=afterLast) {
        (nptr++)->_timestamp=0;
      }
      _timestamp=1;
    }
  }

  inline
  void ensure(size_t size)
  {
    DArray<Entry>::ensure(size);
  }

  inline
  void insert(size_t index, T obj)
  {
    CALL("ArrayMap::insert");
    Entry& e=(*this)[index];
    e._obj=obj;
    e._timestamp=_timestamp;
  }
  inline
  T get(size_t index)
  {
    CALL("ArrayMap::get");
    ASS((*this)[index]._timestamp==_timestamp);
    return (*this)[index]._obj;
  }
  inline
  bool find(size_t index)
  {
    CALL("ArrayMap::find");
    return (*this)[index]._timestamp==_timestamp;
  }
  inline
  void remove(size_t index)
  {
    CALL("ArrayMap::remove");
    ASS((*this)[index]._timestamp==_timestamp);
    (*this)[index]._timestamp=0;
  }


  inline
  bool getValuePtr(size_t index, T*& pObj, T init)
  {
    CALL("ArrayMap::getValuePtr");

    Entry& e=(*this)[index];
    pObj=&e._obj;
    if(e._timestamp!=_timestamp) {
      e._timestamp=_timestamp;
      e._obj=init;
      return true;
    }
    return false;
  }
private:
  unsigned _timestamp;
};

}

#endif
