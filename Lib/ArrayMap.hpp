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
 * @file ArrayMap.hpp
 * Defines a class ArrayMap, a map from a bounded range of unsigned keys
 * with constant time reset via timestamps.
 *
 * @since 30/12/2007 Manchester
 */

#ifndef __ArrayMap__
#define __ArrayMap__

#include "Forwards.hpp"

#include "DArray.hpp"

namespace Lib {

/**
 * An entry of the @b ArrayMap object
 */
template<typename T>
struct ArrayMapEntry
{
  ArrayMapEntry() : _timestamp(0) {}

  T _obj;
  unsigned _timestamp;
};

/**
 * A map from @b size_t type to elements @b T
 *
 * The @b ensure function has to be called with an upper bound of
 * key values.
 */
template<typename T>
class ArrayMap
: DArray<ArrayMapEntry<T> >
{
  typedef ArrayMapEntry<T> Entry;
public:
  CLASS_NAME(ArrayMap<T>);
  USE_ALLOCATOR(ArrayMap<T>); 

  /**
   * Create the map object
   *
   * The @b ensure function has to be called to determine what keys
   * can be stored in the map
   */
  ArrayMap() : DArray<Entry>(8), _timestamp(1) {}

  /**
   * Create the map object that can contain keys less than @b size
   */
  ArrayMap(size_t size) : DArray<Entry>(size), _timestamp(1) {}

  /**
   * Make the map empty
   */
  void reset()
  {
    _timestamp++;
    if(_timestamp==0) {
      Entry* nptr=DArray<Entry>::_array;
      Entry* afterLast=DArray<Entry>::_array +DArray<Entry>::_capacity;
      while(nptr!=afterLast) {
        (nptr++)->_timestamp=0;
      }
      _timestamp=1;
    }
  }

  /**
   * Ensure that keys less than @b size can be stored in the map
   *
   * Call to this function makes the content of the map undefined,
   * so @b reset should be called after each call to this function.
   */
  inline
  void ensure(size_t size)
  {
    DArray<Entry>::ensure(size);
  }

  /**
   * Ensure that keys less than @b size can be stored in the map.
   * The current content of the map remains unchanged.
   */
  inline
  void expand(size_t size)
  {
    DArray<Entry>::expand(size);
  }

  /**
   * Insert the object @b obj into the map under the key @b index.
   * There must not have been any object stored under the key
   * @b index before.
   */
  inline
  void insert(size_t index, T obj=T())
  {
    CALL("ArrayMap::insert");

    Entry& e=(*this)[index];
    ASS_NEQ(e._timestamp,_timestamp);
    e._obj=obj;
    e._timestamp=_timestamp;
  }

  /**
   * Assign the key @b index the object @b obj
   *
   * The difference from the @b insert function is that with this
   * function the key could have been assigned an object before.
   */
  inline
  void set(size_t index, T obj=T())
  {
    CALL("ArrayMap::set");

    Entry& e=(*this)[index];
    e._obj=obj;
    e._timestamp=_timestamp;
  }

  /**
   * Return the object assigned to key @b index. The key @b index must
   * have an object assigned.
   */
  inline
  T get(size_t index)
  {
    CALL("ArrayMap::get");
    ASS_EQ((*this)[index]._timestamp,_timestamp);
    return (*this)[index]._obj;
  }

  /**
   * Return the object assigned to key @b index or @b def if there isn't any.
   */
  inline
  T get(size_t index, T def)
  {
    CALL("ArrayMap::get");
    if((*this)[index]._timestamp!=_timestamp) {
      return def;
    }
    return (*this)[index]._obj;
  }

  /**
   * Return @b true if key @b index has an object assigned
   *
   * Even for this function the value of @b index must be
   * lower that the bound set by the @b ensure function.
   */
  inline
  bool find(size_t index)
  {
    CALL("ArrayMap::find");
    return (*this)[index]._timestamp==_timestamp;
  }

  /**
   * Return @b true if key @b index has an object assigned and assign
   * its value into @c val. Otherwise return false and leave @c val
   * unmodified.
   *
   * Even for this function the value of @b index must be
   * lower that the bound set by the @b ensure function.
   */
  inline
  bool find(size_t index, T& val)
  {
    CALL("ArrayMap::find");
    if((*this)[index]._timestamp==_timestamp) {
      val = (*this)[index]._obj;
      return true;
    }
    return false;
  }

  /**
   * Remove the value assigned to the @b index key. The key
   * @b index must have been assigned a value before.
   */
  inline
  void remove(size_t index)
  {
    CALL("ArrayMap::remove");
    ASS((*this)[index]._timestamp==_timestamp);
    (*this)[index]._timestamp=0;
  }

  /**
   * Assign into @b pObj the pointer that stores the value associated
   * with key @b index. If the key was not previously assigned a value,
   * initialize it to @b init and return true; otherwise return false.
   */
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

  class KeyIterator
  {
  public:
    DECL_ELEMENT_TYPE(unsigned);
    KeyIterator(const ArrayMap& parent) : _parent(parent), _idx(0) {}

    bool hasNext()
    {
      while(_idx < static_cast<const DArray<Entry>&>(_parent).size()) {
	if(_parent[_idx]._timestamp == _parent._timestamp) {
	  return true;
	}
	++_idx;
      }
      return false;
    }

    size_t next()
    {
      CALL("ArrayMap::KeyIterator::next");
      ASS_L(_idx,_parent.size());
      ASS_EQ(_parent[_idx]._timestamp,_parent._timestamp);
      return _idx++;
    }

  private:
    const ArrayMap& _parent;
    size_t _idx;
  };

private:
  /**
   * Timestamp value that is stored in map entries that correspond
   * to existing key-value pairs
   *
   * This is to allow reset of the map in constant time by increasing
   * the value of this field.
   */
  unsigned _timestamp;
};

class ArraySet : public ArrayMap<EmptyStruct>
{
public:
  ArraySet() {}
  ArraySet(size_t size) : ArrayMap<EmptyStruct>(size) {}

  template<class It>
  void insertFromIterator(It it)
  {
    CALL("ArraySet::insertFromIterator");

    while(it.hasNext()) {
      insert(it.next());
    }
  }

  typedef KeyIterator Iterator;
};

}

#endif
