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
 * @file DHMap.hpp
 * Defines class DHMap<Key,Val,Hash1,Hash2> of maps, implemented as
 * double hashed hashtables.
 */

#ifndef __DHMultiset__
#define __DHMultiset__

#include <cstdlib>
#include <algorithm>

#include "Debug/Assertion.hpp"
#include "Allocator.hpp"
#include "Exception.hpp"
#include "Hash.hpp"
#include "DHMap.hpp"
#include "Portability.hpp"

namespace Lib {

#define DHMULTISET_MAX_CAPACITY_INDEX DHMAP_MAX_CAPACITY_INDEX
#define DHMULTISET_MAX_MULTIPLICITY 0x3FFFFFFFu
#define DHMULTISET_FILL_UP_COEFFICIENT 0.7f


/**
 * Class DHMultiset implements generic multisets with values of a class Val.
 * Hash1 and Hash2 are classes containing a function hash() mapping
 * values to unsigned integer values.
 *
 * @param Val values, a pointer or integral value (e.g., integer or long):
 *        anything that can be hashed to an unsigned integer
 *        and compared using ==
 * @param Hash1 class containing the hash function for values which
 *	  determines position of entry in hashtable when no collision
 *	  occurs.
 * @param Hash2 class containing the hash function for values which
 *	  will be used when collision occurs. Otherwise it will not be
 *	  enumerated.
 */
template <typename Val, class Hash1=Hash, class Hash2=Hash>
class DHMultiset
{
public:
  CLASS_NAME(DHMultiset);
  USE_ALLOCATOR(DHMultiset);
  
  /** Create a new DHMultiset */
  DHMultiset()
  : _size(0), _multiplicities(0), _deleted(0), _capacityIndex(0), _capacity(0),
  _nextExpansionOccupancy(0), _entries(0), _afterLast(0)
  {
    ensureExpanded();
  }

  /** Deallocate the DHMultiset */
  ~DHMultiset()
  {
    if(_entries) {
      array_delete(_entries, _capacity);
      DEALLOC_KNOWN(_entries,_capacity*sizeof(Entry),"DHMultiset::Entry");
    }
  }

  /**
   * Return true iff given value is stored in the set.
   */
  inline
  bool find(Val val) const
  {
    CALL("DHMultiset::find/1");
    const Entry* e=findEntry(val);
    return e;
  }

  /**
   * Return multiplicity of given value in the set.
   */
  inline
  unsigned multiplicity(Val val) const
  {
    CALL("DHMultiset::find/1");
    const Entry* e=findEntry(val);
    return e ? e->_info.multiplicity : 0;
  }

  /**
   * Insert given value into the multiset.
   */
  inline
  int insert(Val val)
  {
    return insert(val,1);
  }

  /**
   * Insert given value into the multiset @b multiplicity times and
   * return its new multiplicity in the multi-set.
   */
  int insert(Val val, int multiplicity)
  {
    CALL("DHMultiset::insert");
    ASS(multiplicity>0 && ((unsigned)multiplicity)<DHMULTISET_MAX_MULTIPLICITY);

    ensureExpanded();
    Entry* e=findEntryToInsert(val);
    bool exists = e->_info.multiplicity;
    if(exists) {
      ASS(e->_info.multiplicity+(unsigned)multiplicity<DHMULTISET_MAX_MULTIPLICITY);
      e->_info.multiplicity+=multiplicity;
      _multiplicities+=multiplicity;
    } else {
      ASS_EQ(e->_info.multiplicity, 0);
      e->_info.multiplicity=multiplicity;
      _multiplicities+=multiplicity-1;
      if(e->_info.deleted) {
	e->_info.deleted=0;
	_deleted--;
      }
      e->_val=val;
      _size++;
    }
    return e->_info.multiplicity;
  }

  /**
   * If given value is stored in the multiset, remove
   * it (once) and return true. Otherwise, return false.
   */
  bool remove(Val val)
  {
    CALL("DHMultiset::remove");
    Entry* e=findEntry(val);
    if(!e) {
      return false;
    }
    ASS(e->_info.multiplicity>0);
    e->_info.multiplicity--;
    if(e->_info.multiplicity==0) {
      e->_info.deleted=1;
      _size--;
      _deleted++;
    } else {
      _multiplicities--;
    }
    return true;
  }

  /**
   * If given value is stored in the multiset, remove
   * it (once). Return multiplicity of the value before removal.
   *
   * If the item is not in the multiset, 0 is returned and
   * nothing happens.
   */
  unsigned getMultiplicityAndRemove(Val val)
  {
    CALL("DHMultiset::getMultiplicityAndRemove");
    Entry* e=findEntry(val);
    if(!e) {
      return 0;
    }
    ASS(e->_info.multiplicity>0);
    e->_info.multiplicity--;
    if(e->_info.multiplicity==0) {
      e->_info.deleted=1;
      _size--;
      _deleted++;
    } else {
      _multiplicities--;
    }
    return e->_info.multiplicity+1;
  }


  /** Return number of values stored in this multiset (including multiplicities)*/
  inline
  int size() const
  {
    ASS(_size>=0);
    return _size+_multiplicities;
  }

  /** Return true iff there are any values stored in this set */
  inline
  bool isEmpty() const
  {
    ASS(_size>=0);
    return _size==0;
  }

  /** Return one arbitrary value, that is stored in this set */
  Val getOneValue()
  {
    Iterator it(*this);
    ALWAYS(it.hasNext());
    return it.next();
  }

private:
  struct Entry
  {
    /** Create a new Entry */
    inline
    Entry() : _infoData(0) {}
    /** Return true, if nothing was ever stored in this entry
     * (so nothing could have ever collided with it as well). */
    inline
    bool isEmpty() { return !_infoData; }
    union {
      struct {
	/** 1 if first collision occured on this entry during some insertion */
	unsigned collision : 1;
	unsigned deleted : 1;
	unsigned multiplicity : 30;
      } _info;
      int32_t _infoData;
    };
    Val _val;
  };

  /** Copy constructor is private and without a body, because we don't want any. */
  DHMultiset(const DHMultiset& obj);
  /** operator= is private and without a body, because we don't want any. */
  DHMultiset& operator=(const DHMultiset& obj);


  /** Check whether an expansion is needed and if so, expand */
  inline
  void ensureExpanded()
  {
    if(_size+_deleted>=_nextExpansionOccupancy) {
      expand();
    }
  }

  /** Expand DHMultiset to about double of its current size */
  void expand()
  {
    CALL("DHMultiset::expand");

    if(_capacityIndex>=DHMULTISET_MAX_CAPACITY_INDEX) {
      throw Exception("Lib::DHMultiset::expand: MaxCapacityIndex reached.");
    }

    int newCapacity=DHMapTableCapacities[_capacityIndex+1];
    void* mem = ALLOC_KNOWN(newCapacity*sizeof(Entry),"DHMultiset::Entry");

    Entry* oldEntries=_entries;
    Entry* oldAfterLast=_afterLast;
    int oldCapacity=_capacity;

    _size=0;
    _multiplicities=0;
    _deleted=0;
    _capacityIndex++;
    _capacity = newCapacity;
    _nextExpansionOccupancy = DHMapTableNextExpansions[_capacityIndex];

    _entries = array_new<Entry>(mem, _capacity);
    _afterLast = _entries + _capacity;

    Entry* ep=oldEntries;
    while(ep!=oldAfterLast) {
      if(ep->_info.multiplicity) {
	insert(ep->_val, ep->_info.multiplicity);
      }
      (ep++)->~Entry();
    }

    if(oldCapacity) {
      DEALLOC_KNOWN(oldEntries,oldCapacity*sizeof(Entry),"DHMultiset::Entry");
    }
  }

  /** Return pointer to an Entry object which contains specified value,
   * or 0, if there is no such */
  inline
  Entry* findEntry(Val val)
  {
    return const_cast<Entry*>(static_cast<const DHMultiset*>(this)->findEntry(val));
  }

  /** Return pointer to an Entry object which contains specified value,
   * or 0, if there is no such */
  const Entry* findEntry(Val val) const
  {
    CALL("DHMultiset::findEntry");
    ASS(_capacity>_size+_deleted);

    unsigned h1=computeHash<Hash1>(val, _capacity);
    int pos=h1%_capacity;
    Entry* res=&_entries[pos];
    if(res->isEmpty()) {
      return 0;
    }
    if(res->_val==val) {
      return res->_info.deleted ? 0 : res;
    }

    //We have a collision...

    if(!res->_info.collision) {
      //There were no collisions on this position during inserting,
      //so the value, we're searching for isn't here anyway
      return 0;
    }

    unsigned h2=Hash2::hash(val)%_capacity;
    if(h2==0) {
      h2=1;
    }
    do {
      pos=(pos+h2)%_capacity;
      res=&_entries[pos];
    } while (!res->isEmpty() && res->_val!=val);

    if(res->isEmpty()) {
      return 0;
    }

    ASS(res->_val==val);
    return res->_info.deleted ? 0 : res;
  }

  /** Return pointer to an Entry object which contains, or could contain
   * specified value */
  Entry* findEntryToInsert(Val val)
  {
    CALL("DHMultiset::findEntryToInsert");
    ASS(_capacity>_size+_deleted);

    unsigned h1=computeHash<Hash1>(val, _capacity);
    int pos=h1%_capacity;
    Entry* res=&_entries[pos];
    if( (res->_info.multiplicity==0 && res->_info.collision==0) || res->_val==val) {
      return res;
    }

    //We have a collision...

    bool collisionBefore=res->_info.collision;

    //mark the entry where the collision occured
    res->_info.collision=1;

    unsigned h2=Hash2::hash(val)%_capacity;
    if(h2==0) {
      h2=1;
    }

    if(collisionBefore) {
      Entry* available=0;
      do {
        pos=(pos+h2)%_capacity;
        res=&_entries[pos];
        if(!available && res->_info.multiplicity==0) {
          available=res;
        }
      } while (!res->isEmpty() && res->_val!=val );
      if(res->isEmpty()) {
	//the value isn't present in the multiset,
	//so well store it in position with will
	//lead to least collisions
	res=available;
      }
    } else {
      //val is not present in the multiset
      do {
        pos=(pos+h2)%_capacity;
        res=&_entries[pos];
      } while (res->_info.multiplicity!=0);
    }

    return res;
  }


  /** Number of entries stored in this DHMultiset */
  int _size;
  /**
   * Number of multiplicities
   *
   * First value in an entry is not a multiplicity,
   * so _size+_multiplicities is the number of values
   * stored by client.
   */
  int _multiplicities;
  /** Number of entries marked as deleted */
  int _deleted;
  /** Index of current _capacity in the TableCapacities array */
  int _capacityIndex;
  /** Size of the _entries array */
  int _capacity;
  /** When _size+_deleted reaches this, expansion will occur */
  int _nextExpansionOccupancy;

  /** Array containing hashtable storing content of this set */
  Entry* _entries;
  /** Pointer to element after the last element of _entries array */
  Entry* _afterLast;

public:

#if VDEBUG
  void assertValid()
  {
    int sz=size();
    int cnt=0;
    Iterator it(*this);
    while(it.hasNext()) {
      cnt++;
      it.next();
    }
    ASS_EQ(sz,cnt);
  }
#endif

  /**
   * Iterator over the multiset object. The object is iterated
   * as a set -- each contained element is returned just once,
   * irregarding its multiplicity.
   */
  class SetIterator {
  public:
    /** Create a new iterator */
    inline SetIterator(const DHMultiset& set)
    : _next(set._entries), _afterLast(set._afterLast)
    {
    }

    /**
     * True if there exists next element
     */
    bool hasNext()
    {
      CALL("DHMultiset::SetIterator::hasNext");
      while (_next != _afterLast) {
	//we don't have to check for _info.deleted, as long as we
	//set the multiplicity of deleted entries to zero
	if (_next->_info.multiplicity) {
	  return true;
	}
	_next++;
      }
      return false;
    }

    /**
     * Return the next value
     * @warning hasNext() must have been called before
     */
    inline
    Val next()
    {
      CALL("DHMultiset::SetIterator::next");
      ASS_NEQ(_next, _afterLast);

      return (_next++)->_val;
    }

    /**
     * Return the next value
     * @warning hasNext() must have been called before
     */
    inline
    Val next(unsigned& multiplicity)
    {
      CALL("DHMultiset::SetIterator::next/1");
      ASS_NEQ(_next, _afterLast);

      multiplicity=_next->_info.multiplicity;
      return (_next++)->_val;
    }

  private:
    /** iterator will look for the next occupied cell starting with this one */
    Entry* _next;
    /** iterator will stop looking for the next cell after reaching this one */
    Entry* _afterLast;
  };

  /**
   * Class to allow iteration over values stored in the set.
   */
  class Iterator {
  public:
    /** Create a new iterator */
    inline Iterator(const DHMultiset& set)
    : _next(set._entries), _afterLast(set._afterLast), _nextIndex(0)
    {
    }

    /**
     * True if there exists next element
     */
    bool hasNext()
    {
      CALL("DHMultiset::Iterator::hasNext");
      if(_next->_info.multiplicity > _nextIndex)
	return true;
      _nextIndex=0;
      _next++;
      while (_next != _afterLast) {
	//we don't have to check for _info.deleted, as long as we
	//set the multiplicity of deleted entries to zero
	if (_next->_info.multiplicity) {
	  return true;
	}
	_next++;
      }
      return false;
    }

    /**
     * Return the next value
     * @warning hasNext() must have been called before
     */
    inline
    Val next()
    {
      CALL("DHMultiset::Iterator::next");
      ASS(_next != _afterLast);
      ASS(_next->_info.multiplicity > _nextIndex);
      _nextIndex++;
      return _next->_val;
    }

  private:
    /** iterator will look for the next occupied cell starting with this one */
    Entry* _next;
    /** iterator will stop looking for the next cell after reaching this one */
    Entry* _afterLast;
    /**
     * Index of the returned value in current entry.
     * (the values in one entry are all the same, but we have to
     * yield them multiple times, as we're in a multiset)
     */
    unsigned _nextIndex;
  }; // class DHMultiset::Iterator


}; // class DHMultiset

}

#endif // __DHMultiset__

