
/*
 * File DHMap.hpp.
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
 * @file DHMap.hpp
 * Defines class DHMap<Key,Val,Hash1,Hash2> of maps, implemented as
 * double hashed hashtables.
 */

#ifndef __BiMap__
#define __BiMap__

#include <cstdlib>
#include <utility>

#if VDEBUG
#include <typeinfo>
#endif

#include "Debug/Assertion.hpp"
#include "Allocator.hpp"
#include "Exception.hpp"
#include "DHMap.hpp"

namespace Lib {


template <typename Key1, typename Key2>
class BiMap
{
public:
  CLASS_NAME(BiMap);
  USE_ALLOCATOR(BiMap);
  
  /** Create a new DHMap */
  BiMap() 
  {
  }

  //copy constructor?

  /** Deallocate the BiMap */
  ~BiMap()
  { //Do the destructors of _map1 and _map2 need to be called?
  }

  /** Empty the BiMap */
  void reset()
  {
    CALL("BiMap::reset");
    _map1.reset();
    _map2.reset();
  }

  /**
   *  Find value by the @b key. The result is true if a pair
   *  with this key is in the map. If such a pair is found,
   *  then its value is returned in @b val. Otherwise, the
   *  value of @b val remains unchanged.
   */
  inline
  bool find1(Key1 key, Key2& val) const
  {
    CALL("BiMap::find1");
    return _map1.find(key, val);
  }

  inline
  bool find2(Key2 key, Key1& val) const
  {
    CALL("BiMap::find2");
    return _map2.find(key, val);
  }


  /**
   *  Return true iff a pair with @b key as a key is in the map.
   */
  inline
  bool find1(Key1 key) const
  {
    CALL("BiMap::find1");
    return _map1.find(key);
  }

  inline
  bool find2(Key2 key) const
  {
    CALL("BiMap::find2");
    return _map2.find(key);
  }

  /**
   *  Return value associated with given key. A pair with
   *  this key has to be present.
   */
  inline
  const Key2& get1(Key1 key) const
  {
    return _map1.get(key);
  }

  inline
  const Key1 get2(Key2 key) const
  {
    return _map2.get(key);
  }

  /**
   *  Return value associated with given key. A pair with
   *  this key has to be present.
   */
  inline
  Key2& get1(Key1 key)
  {
    return _map1.get(key);
  }

  inline
  Key1& get2(Key2 key)
  {
    return _map2.get(key);
  }

  /**
   * If there is no value stored under @b key in the map,
   * insert pair (key,value) and return true. Otherwise,
   * return false.
   */
  bool insert(Key1 key1, Key2 key2)
  {
    CALL("BiMap::insert");
    bool inserted = _map1.insert(key1, key2);
    bool inserted2 = _map2.insert(key2, key1);
    ASS(inserted == inserted2);
    return inserted;
  }


  /**
   * If there is a value stored under the @b key, remove
   * it and return true. Otherwise, return false.
   */
  bool remove1(Key1 key1)
  {
    CALL("BiMap::remove1");
    Key2 key2;
    bool found = _map1.find(key1, key2);
    if(found){
      _map1.remove(key1);
      _map2.remove(key2);
    }
    return found;
  }


  bool remove2(Key2 key2)
  {
    CALL("BiMap::remove2");
    Key1 key1;
    bool found = _map2.find(key2, key1);
    if(found){
      _map1.remove(key1);
      _map2.remove(key2);
    }
    return found;
  }

  /** Return mumber of entries stored in this DHMap */
  inline
  unsigned size() const
  {
    ASS(_map1.size() == _map2.size());
    return _map1.size();
  }

  /** Return true iff there are any entries stored in this DHMap */
  inline
  bool isEmpty() const
  {
    ASS(_map1.isEmpty() == _map2.isEmpty());
    return _map1.isEmpty();
  }

private:
  
  DHMap<Key1, Key2> _map1;
  DHMap<Key2, Key1> _map2;

//Itertors?


}; // class BiMap

}

#endif // __DHMap__

