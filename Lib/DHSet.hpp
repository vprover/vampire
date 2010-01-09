/**
 * @file DHMap.hpp
 * Defines class DHMap<Key,Val,Hash1,Hash2> of maps, implemented as
 * double hashed hashtables.
 */

#ifndef __DHSet__
#define __DHSet__

#include "DHMap.hpp"

namespace Lib {

/**
 * Class DHMap implements generic maps with keys of a class Key
 * and values of a class Value. If you implement a map with
 * a new class Key, Hash1 and Hash2 are classes containing a function
 * hash() mapping keys to unsigned integer values.
 *
 * @param Key a pointer or integral value (e.g., integer or long):
 *        anything that can be hashed to an unsigned integer
 *        and compared using ==
 * @param Hash1 class containig the hash function for keys which
 *	  determines position of entry in hashtable when no collision
 *	  occurs. This function can also take second int parameter,
 * 	  which will contain current capacity of the hashtable. In
 * 	  this case, HashTraits struct has to be specialized for this
 * 	  class, so that enum member SINGLE_PARAM_HASH is equal to 0.
 * @param Hash2 class containig the hash function for keys which
 *	  will be used when collision occurs. Otherwise it will not be
 *	  enumerated.
 */
template <typename Val, class Hash1, class Hash2>
class DHSet
{
public:
  DHSet() {}

  /** Empty the DHSet */
  void reset()
  {
    CALL("DHSet::reset");

    _map.reset();
  }

  /**
   *  Return true iff @b val is in the set.
   */
  inline
  bool find(Val val) const
  {
    CALL("DHSet::find");

    return _map.find(val);
  }

  /**
   * If the @b val is not in the set, insert it and return true.
   * Otherwise, return false.
   */
  bool insert(Val val)
  {
    CALL("DHSet::insert");

    return _map.insert(val, EmptyStruct());
  }


  /**
   * If there is a value stored under the @b key, remove
   * it and return true. Otherwise, return false.
   */
  bool remove(Val val)
  {
    CALL("DHSet::remove");

    return _map.remove(val);
  }

  /** Return mumber of entries stored in this DHMap */
  inline
  int size() const
  {
    return _map.size();
  }

  /** Return true iff there are any entries stored in this DHMap */
  inline
  bool isEmpty() const
  {
    return _map.isEmpty();
  }

  /** Return one arbitrary item that is present in the set */
  Val getOneKey()
  {
    return _map.getOneKey();
  }

  VirtualIterator<Val> iterator() const
  {
    return _map.domain();
  }

private:
  /** Copy constructor is private and without a body, because we don't want any. */
  DHSet(const DHSet& obj);
  /** operator= is private and without a body, because we don't want any. */
  DHSet& operator=(const DHSet& obj);


  struct EmptyStruct
  {
  };

  DHMap<Val,EmptyStruct,Hash1,Hash2> _map;

}; // class DHSet

}

#endif // __DHSet__

