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

#ifndef __DHMap__
#define __DHMap__

#include <cstdlib>
#include <utility>

#if VDEBUG
#include <typeinfo>
#endif

#include "Debug/Assertion.hpp"
#include "Allocator.hpp"
#include "Exception.hpp"
#include "Hash.hpp"
#include "VirtualIterator.hpp"

namespace Lib {

#define DHMAP_MAX_CAPACITY_INDEX 29


/**
 * Traits class for hash classes, which should be specialized
 * for classes whose hash functions have second parameter for
 * hashtable capacity.
 */
template<typename Hash>
struct HashTraits
{
  enum {SINGLE_PARAM_HASH=1};
};

/**
 * Auxiliary class for computing of hash values which depends on
 * specializations of HashTraits class.
 */
template<int I, class Hash, typename Key>
class HashCompClass {
};

/**
 * Auxiliary class for computing of hash values which depends on
 * specializations of HashTraits class.
 */
template<class Hash, typename Key>
struct HashCompClass<1,Hash,Key> {
  static inline unsigned compute(Key& key, int capacity)
  {
    return Hash::hash(key);
  }
};

/**
 * Auxiliary class for computing of hash values which depends on
 * specializations of HashTraits class.
 */
template<class Hash, typename Key>
struct HashCompClass<0,Hash,Key> {
  static inline unsigned compute(Key& key, int capacity)
  {
    return Hash::hash(key, capacity);
  }
};

/** Computes hash value of given key for hashtable with specified capacity */
template<class Hash, typename Key>
inline
unsigned computeHash(Key& key, int capacity)
{
  return HashCompClass<HashTraits<Hash>::SINGLE_PARAM_HASH,Hash,Key>::compute(key, capacity);
};

extern const unsigned DHMapTableCapacities[];
extern const unsigned DHMapTableNextExpansions[];

/**
 * Class DHMap implements generic maps with keys of a class Key
 * and values of a class Value. If you implement a map with
 * a new class Key, Hash1 and Hash2 are classes containing a function
 * hash() mapping keys to unsigned integer values.
 *
 * @param Key a pointer or integral value (e.g., integer or long):
 *        anything that can be hashed to an unsigned integer
 *        and compared using ==
 * @param Val values, can be anything
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
template <typename Key, typename Val, class Hash1, class Hash2>
class DHMap
{
public:
  CLASS_NAME(DHMap);
  USE_ALLOCATOR(DHMap);
  
  /** Create a new DHMap */
  DHMap()
  : _timestamp(1), _size(0), _deleted(0), _capacityIndex(0), _capacity(0),
  _nextExpansionOccupancy(0), _entries(0), _afterLast(0)
  {
    ensureExpanded();
  }

  DHMap(const DHMap& obj)
  : _timestamp(1), _size(0), _deleted(0), _capacityIndex(0), _capacity(0),
  _nextExpansionOccupancy(0), _entries(0), _afterLast(0)
  {
    ensureExpanded();

    typename DHMap::Iterator iit(obj);
    while(iit.hasNext()) {
      Key k;
      Val v;
      iit.next(k, v);
      ALWAYS(insert(k,v));
    }
  }

  /** Deallocate the DHMap */
  ~DHMap()
  {
    if(_entries) {
      ASS_EQ(_afterLast-_entries,_capacity);
      array_delete(_entries, _capacity);
      DEALLOC_KNOWN(_entries,_capacity*sizeof(Entry),"DHMap::Entry");
//      DEALLOC_KNOWN(_entries,_capacity*sizeof(Entry),typeid(Entry).name());
    }
  }

  /** Empty the DHMap */
  void reset()
  {
    CALL("DHMap::reset");
    unsigned oldTS=_timestamp;
    _timestamp++;
    _size=0;
    _deleted=0;

    if(oldTS>(_timestamp&0x3FFFFFFF)) {
      //We store timestamp only in 30 bits in entries,
      //and they've just overflowed.
      _timestamp=1;
      Entry* pe=_afterLast;
      while(pe--!=_entries) {
	pe->_info.timestamp=0;
      }
    }
  }

  /**
   *  Find value by the @b key. The result is true if a pair
   *  with this key is in the map. If such a pair is found,
   *  then its value is returned in @b val. Otherwise, the
   *  value of @b val remains unchanged.
   */
  inline
  bool find(Key key, Val& val) const
  {
    CALL("DHMap::find/2");
    const Entry* e=findEntry(key);
    if(!e) {
      return false;
    }
    val=e->_val;
    return true;
  }

  /**
   * Return a pointer to Val inside the map
   * if entry corresponding to Key exists.
   * Otherwise return nullptr.
   */
  Val* findPtr(Key key)
  {
    CALL("DHMap::findPtr");
    Entry* e=findEntry(key);
    if(!e) {
      return nullptr;
    }
    return &e->_val;
  }

  /**
   *  Return true iff a pair with @b key as a key is in the map.
   */
  inline
  bool find(Key key) const
  {
    CALL("DHMap::find/1");
    return findEntry(key);
  }

  /**
   *  Return value associated with given key. A pair with
   *  this key has to be present.
   */
  inline
  const Val& get(Key key) const
  {
    const Entry* e=findEntry(key);
    ASS(e);
    return e->_val;
  }

  /**
   *  Return value associated with given key. A pair with
   *  this key has to be present.
   */
  inline
  Val& get(Key key)
  {
    Entry* e=findEntry(key);
    ASS(e);
    return e->_val;
  }

  /**
   *  If @b key is present in the map, return value associated
   *  with it; otherwise return @b def
   */
  inline
  Val get(Key key, Val def) const
  {
    const Entry* e=findEntry(key);
    if(!e) {
      return def;
    }
    return e->_val;
  }


  /** Load key-value pairs from a DHMap. The current map must not contain any elements from @c map. */
  void loadFromMap(const DHMap& map)
  {
    Iterator iit(map);
    while(iit.hasNext()) {
      Key k;
      Val v;
      iit.next(k, v);
      ALWAYS(insert(k,v));
    }
  }

  /** Load key-value pairs from an inverted DHMap. The @b inverted map must be one-to-one. */
  template<class HashX1, class HashX2>
  void loadFromInverted(const DHMap<Val, Key, HashX1, HashX2>& inverted)
  {
    typename DHMap<Val, Key, HashX1, HashX2>::Iterator iit(inverted);
    while(iit.hasNext()) {
      Key k;
      Val v;
      iit.next(v, k);
      ALWAYS(insert(k,v));
    }
  }

  /** same as @b insert but using move semantics instead of copying */
  bool emplace(Key key, Val&& val)
  {
    CALL("DHMap::emplace");
    ensureExpanded();
    Entry* e=findEntryToInsert(key);
    bool exists = e->_info.timestamp==_timestamp && !e->_info.deleted;
    if(!exists) {
      if(e->_info.timestamp!=_timestamp) {
	e->_info.timestamp=_timestamp;
	//no collision has occured on this entry while this _timestamp is set
	e->_info.collision=0;
      } else {
	ASS(e->_info.deleted);
	_deleted--;
      }
      e->_info.deleted=0;
      e->_key=key;
      e->_val=std::move(val);
      _size++;
    }
    return !exists;

  }

  /**
   * If there is no value stored under @b key in the map,
   * insert pair (key,value) and return true. Otherwise,
   * return false.
   * This function copies copies @b val.
   */
  bool insert(Key key, const Val& val)
  {
    CALL("DHMap::insert");
    return emplace(key, Val(val));
  }

  /**
   * If there is no value stored under @b key in the map,
   * insert pair (key,value). Return value stored under @b key.
   */
  Val findOrInsert(Key key, const Val& val)
  {
    CALL("DHMap::insert");
    ensureExpanded();
    Entry* e=findEntryToInsert(key);
    bool exists = e->_info.timestamp==_timestamp && !e->_info.deleted;
    if(!exists) {
      if(e->_info.timestamp!=_timestamp) {
	e->_info.timestamp=_timestamp;
	//no collision has occured on this entry while this _timestamp is set
	e->_info.collision=0;
      } else {
	ASS(e->_info.deleted);
	_deleted--;
      }
      e->_info.deleted=0;
      e->_key=key;
      e->_val=val;
      _size++;
    }
    return e->_val;
  }

  /**
   * If there is no value stored under @b key in the map,
   * insert pair (key,initial). Assign value stored under
   * @b key into @b val. Return true iff the new value was
   * inserted.
   */
  bool findOrInsert(Key key, Val& val, const Val& initial)
  {
    CALL("DHMap::insert");
    ensureExpanded();
    Entry* e=findEntryToInsert(key);
    bool exists = e->_info.timestamp==_timestamp && !e->_info.deleted;
    if(!exists) {
      if(e->_info.timestamp!=_timestamp) {
	e->_info.timestamp=_timestamp;
	//no collision has occured on this entry while this _timestamp is set
	e->_info.collision=0;
      } else {
	ASS(e->_info.deleted);
	_deleted--;
      }
      e->_info.deleted=0;
      e->_key=key;
      e->_val=initial;
      _size++;
    }
    val=e->_val;
    return !exists;
  }

  /**
   * Assign pointer to value stored under @b key into @b pval.
   * If nothing was previously stored under @b key, initialize
   * the value with @b initial, and return true. Otherwise,
   * return false.
   */
  bool getValuePtr(Key key, Val*& pval, const Val& initial)
  {
    CALL("DHMap::getValuePtr/3");
    ensureExpanded();
    Entry* e=findEntryToInsert(key);
    bool exists = e->_info.timestamp==_timestamp && !e->_info.deleted;
    if(!exists) {
      if(e->_info.timestamp!=_timestamp) {
	e->_info.timestamp=_timestamp;
	//no collision has occured on this entry while this _timestamp is set
	e->_info.collision=0;
      } else {
	ASS(e->_info.deleted);
	_deleted--;
      }
      e->_info.deleted=0;
      e->_key=key;
      e->_val=initial;
      _size++;
    }
    pval=&e->_val;
    return !exists;
  }

  /**
   * Assign pointer to value stored under @b key into @b pval.
   * If nothing was previously stored under @b key, return true
   * and recreate the value object default constructor.
   * Otherwise, return false.
   */
  bool getValuePtr(Key key, Val*& pval)
  {
    CALL("DHMap::getValuePtr/2");
    ensureExpanded();
    Entry* e=findEntryToInsert(key);
    bool exists = e->_info.timestamp==_timestamp && !e->_info.deleted;
    if(!exists) {
      if(e->_info.timestamp!=_timestamp) {
	e->_info.timestamp=_timestamp;
	//no collision has occured on this entry while this _timestamp is set
	e->_info.collision=0;
      } else {
	ASS(e->_info.deleted);
	_deleted--;
      }
      e->_info.deleted=0;
      e->_key=key;
      e->_val.~Val();
      new(&e->_val) Val();
      _size++;
    }
    pval=&e->_val;
    return !exists;
  }

  /**
   * Store @b value under @b key. Return true if nothing was
   * previously stored under @b key. Otherwise,
   * return false.
   */
  bool set(Key key, const Val& val)
  {
    CALL("DHMap::set");
    ensureExpanded();
    Entry* e=findEntryToInsert(key);
    bool exists = e->_info.timestamp==_timestamp && !e->_info.deleted;
    if(!exists) {
      if(e->_info.timestamp!=_timestamp) {
	e->_info.timestamp=_timestamp;
	//no collision has occured on this entry while this _timestamp is set
	e->_info.collision=0;
      } else {
	ASS(e->_info.deleted);
	_deleted--;
      }
      e->_info.deleted=0;
      e->_key=key;
      _size++;
    }
    e->_val=val;
    return !exists;
  }


  /**
   *  Find value by the @b key. The result is true iff a pair
   *  with this key is in the map. If such a pair is found,
   *  then its value is returned in @b val, and the pair is
   *  removed. Otherwise, the value of @b val remains unchanged.
   */
  inline
  bool pop(Key key, Val& val)
  {
    CALL("DHMap::pop");
    Entry* e=findEntry(key);
    if(!e) {
      return false;
    }
    val=e->_val;
    e->_info.deleted=1;
    _size--;
    _deleted++;
    return true;
  }


  /**
   * If there is a value stored under the @b key, remove
   * it and return true. Otherwise, return false.
   */
  bool remove(Key key)
  {
    CALL("DHMap::remove");
    Entry* e=findEntry(key);
    if(!e) {
      return false;
    }
    e->_info.deleted=1;
    _size--;
    _deleted++;
    return true;
  }


  /** Return mumber of entries stored in this DHMap */
  inline
  unsigned size() const
  {
    ASS(_size>=0);
    return _size;
  }

  /** Return true iff there are any entries stored in this DHMap */
  inline
  bool isEmpty() const
  {
    ASS(_size>=0);
    return _size==0;
  }

  /** Return one arbitrary key, that is present in the map */
  Key getOneKey()
  {
    Iterator it(*this);
    ALWAYS(it.hasNext());
    return it.nextKey();
  }

  /** move assignment operator */
  DHMap& operator=(DHMap&& obj) = default;

  /** applies the function f to every value */
  template<class F> 
  void mapValues(F f) 
  { 
    for (Entry* e = _entries; e != _afterLast; e++) {
      if (e->_info.timestamp==_timestamp && !e->_info.deleted) {
        e->_val = f(std::move(e->_val));
      }
    }
  }



private:
  struct Entry
  {
    /** Create a new Entry */
    Entry() : _infoData(0) {}
    union {
      struct {
	unsigned deleted : 1;
	/** 1 if first collision occured on this entry during some insertion */
	unsigned collision : 1;
	unsigned timestamp : 30;
      } _info;
      int _infoData;
    };
    Key _key;
    Val _val;
  };

  /** operator= is private and without a body, because we don't want any. */
  DHMap& operator=(const DHMap& obj);


  /** Check whether an expansion is needed and if so, expand */
  inline
  void ensureExpanded()
  {
    if(_size+_deleted>=_nextExpansionOccupancy) {
      //cout << this << ", " << _size << ", " << _deleted << ", " << _nextExpansionOccupancy << endl;
      expand();
    }
  }

  /** Expand DHMap to about double of its current size */
  void expand()
  {
    CALL("DHMap::expand");

    if(_capacityIndex>=DHMAP_MAX_CAPACITY_INDEX) {
      throw Exception("Lib::DHMap::expand: MaxCapacityIndex reached.");
    }

    int newCapacity=DHMapTableCapacities[_capacityIndex+1];
    void* mem = ALLOC_KNOWN(newCapacity*sizeof(Entry),"DHMap::Entry");
//    void* mem = ALLOC_KNOWN(newCapacity*sizeof(Entry),typeid(Entry).name());

    //std::cout << (_size+_deleted) << std::endl;

    Entry* oldEntries=_entries;
    Entry* oldAfterLast=_afterLast;
    unsigned oldTimestamp=_timestamp;
    int oldCapacity=_capacity;

    _timestamp=1;
    _size=0;
    _deleted=0;
    _capacityIndex++;
    _capacity = newCapacity;
    _nextExpansionOccupancy = DHMapTableNextExpansions[_capacityIndex];

    _entries = array_new<Entry>(mem, _capacity);
    _afterLast = _entries + _capacity;

    Entry* ep=oldEntries;
    while(ep!=oldAfterLast) {
      ASS(ep);
      if(ep->_info.timestamp==oldTimestamp && !ep->_info.deleted) {
	insert(ep->_key, ep->_val);
      }
      (ep++)->~Entry();
    }
    //std::cout << "copied" << std::endl;
    if(oldCapacity) {
      DEALLOC_KNOWN(oldEntries,oldCapacity*sizeof(Entry),"DHMap::Entry");
//      DEALLOC_KNOWN(oldEntries,oldCapacity*sizeof(Entry),typeid(Entry).name());
    }
  }

  /** Return pointer to an Entry object which contains specified key,
   * or 0, if there is no such */
  inline
  Entry* findEntry(Key key)
  {
    return const_cast<Entry*>(static_cast<const DHMap*>(this)->findEntry(key));
  }

  /** Return pointer to an Entry object which contains specified key,
   * or 0, if there is no such */
  const Entry* findEntry(Key key) const
  {
    CALL("DHMap::findEntry");
    ASS(_capacity>_size+_deleted);

    unsigned h1=computeHash<Hash1>(key, _capacity);
    int pos=h1%_capacity;
    Entry* res=&_entries[pos];
    if(res->_info.timestamp != _timestamp ) {
      return 0;
    }
    if(res->_key==key) {
      return res->_info.deleted ? 0 : res;
    }

    //We have a collision...

    if(!res->_info.collision) {
      //There were no collisions on this position during inserting,
      //so the key we're searching for isn't here anyway
      return 0;
    }

    unsigned h2=Hash2::hash(key)%_capacity;
    if(h2==0) {
      h2=1;
    }
    do {
      pos=(pos+h2)%_capacity;
      res=&_entries[pos];
    } while (res->_info.timestamp == _timestamp && res->_key!=key);

    if(res->_info.timestamp != _timestamp ) {
      return 0;
    }

    ASS(res->_key==key);
    return res->_info.deleted ? 0 : res;
  }

  /** Return pointer to an Entry object which contains, or could contain
   * specified key */
  Entry* findEntryToInsert(Key key)
  {
    CALL("DHMap::findEntryToInsert");
    ASS(_capacity>_size+_deleted);

    unsigned h1=computeHash<Hash1>(key, _capacity);
    int pos=h1%_capacity;
    Entry* res=&_entries[pos];
    if(res->_info.timestamp != _timestamp || res->_key==key) {
      return res;
    }

    //We have a collision...

    //mark the entry where the collision occured
    res->_info.collision=1;

    unsigned h2=Hash2::hash(key)%_capacity;
    if(h2==0) {
      h2=1;
    }
    do {
      pos=(pos+h2)%_capacity;
      res=&_entries[pos];
    } while (res->_info.timestamp == _timestamp && res->_key!=key);
    return res;
  }

  /** Entries with _timestamp different from this are considered empty */
  unsigned _timestamp;
  /** Number of entries stored in this DHMap */
  int _size;
  /** Number of entries marked as deleted */
  int _deleted;
  /** Index of current _capacity in the TableCapacities array */
  int _capacityIndex;
  /** Size of the _entries array */
  int _capacity;
  /** When _size+_deleted reaches this, expansion will occur */
  int _nextExpansionOccupancy;

  /** Array containing hashtable storing content of this map */
  Entry* _entries;
  /** Pointer to element after the last element of _entries array */
  Entry* _afterLast;

private:
  class IteratorBase {
  public:
    /** Create a new IteratorBase */
    inline IteratorBase(const DHMap& map)
    : _next(map._entries), _last(map._afterLast),
    _timestamp(map._timestamp) {}

    /**
     * True if there exists next element
     */
    bool hasNext()
    {
      CALL("DHMap::DomainIteratorCore::hasNext");
      while (_next != _last) {
	if (_next->_info.timestamp==_timestamp && !_next->_info.deleted) {
	  return true;
	}
	_next++;
      }
      return false;
    }

    /**
     * Return the next entry
     * @warning hasNext() must have been called before
     */
    inline
    Entry* next()
    {
      CALL("DHMap::DomainIteratorCore::next");
      ASS(_next != _last);
      ASS(_next->_info.timestamp==_timestamp && !_next->_info.deleted);
      return _next++;
    }

  private:
    /** iterator will look for the next occupied cell starting with this one */
    Entry* _next;
    /** iterator will stop looking for the next cell after reaching this one */
    Entry* _last;
    /** only cells with _timestamp equal to this are considered occupied */
    unsigned _timestamp;
  }; // class DHMap::IteratorBase

  class DomainIteratorCore
  : public IteratorCore<Key> {
  public:
    /** Create a new iterator */
    inline DomainIteratorCore(const DHMap& map) : _base(map) {}
    /** True if there exists next element */
    inline bool hasNext() { return _base.hasNext(); }

    /**
     * Return the next key
     * @warning hasNext() must have been called before
     */
    inline Key next() { return _base.next()->_key; }
  private:
    IteratorBase _base;
  }; // class DHMap::DomainIteratorCore
    
    class RangeIteratorCore
    : public IteratorCore<Val> {
    public:
        /** Create a new iterator */
        inline RangeIteratorCore(const DHMap& map) : _base(map) {}
        /** True if there exists next element */
        inline bool hasNext() { return _base.hasNext(); }
        
        /**
         * Return the next key
         * @warning hasNext() must have been called before
         */
        inline Val next() { return _base.next()->_val; }
    private:
        IteratorBase _base;
    }; // class DHMap::RangeIteratorCore
    
public:
  VirtualIterator<Key> domain() const
  {
    return VirtualIterator<Key>(new DomainIteratorCore(*this));
  }
  VirtualIterator<Val> range() const
  {
    return VirtualIterator<Val>(new RangeIteratorCore(*this));
  }
    
  typedef std::pair<Key,Val> Item;

private:
  class ItemIteratorCore
  : public IteratorCore<Item> {
  public:
    /** Create a new iterator */
    inline ItemIteratorCore(const DHMap& map) : _base(map) {}
    /** True if there exists next element */
    inline bool hasNext() { return _base.hasNext(); }

    /**
     * Return the next key
     * @warning hasNext() must have been called before
     */
    inline Item next()
    {
      Entry* e=_base.next();
      return Item(e->_key, e->_val);
    }
  private:
    IteratorBase _base;
  }; // class DHMap::DomainIteratorCore
public:

  VirtualIterator<Item> items() const
  {
    return VirtualIterator<Item>(new ItemIteratorCore(*this));
  }


  /**
   * Class to allow iteration over keys and values stored in the map.
   */
  class Iterator {
  public:
    /** Create a new iterator */
    inline Iterator(const DHMap& map) : _base(map) {}

    /** True if there exists next element */
    bool hasNext() { return _base.hasNext(); }

    /**
     * Assign key and value of the next entry to respective parameters
     * @warning hasNext() must have been called before
     */
    inline
    void next(Key& key, Val& val)
    {
      Entry* e=_base.next();
      key=e->_key;
      val=e->_val;
    }

    /**
     * Return next value via reference and pass corresponding key via argument.
     * @warning hasNext() must have been called before
     */
    inline
    Val& nextRef(Key& key)
    {
      Entry* e= _base.next();
      key= e->_key;
      return e->_val;
    }

    /**
     * Return the next value
     * @warning hasNext() must have been called before
     */
    inline Val next() { return _base.next()->_val; }

    /**
     * Return the key of next entry
     * @warning hasNext() must have been called before
     */
    inline Key nextKey() { return _base.next()->_key; }

  private:
    IteratorBase _base;
  }; // class DHMap::Iterator

  /**
   * Class to allow iteration over keys and values stored in the map,
   * modification of the value and deleteion of the entry.
   */
  class DelIterator {
  public:
    /** Create a new iterator */
    inline DelIterator(DHMap& map) : _base(map), _map(map), _curr(nullptr) {}

    /** True if there exists next element */
    bool hasNext() { return _base.hasNext(); }

    /**
     * Assign key and value of the next entry to respective parameters
     * @warning hasNext() must have been called before
     */
    inline
    void next(Key& key, Val& val)
    {
      Entry* e=getNextEntry();
      key=e->_key;
      val=e->_val;
    }

    /**
     * Return the next value
     * @warning hasNext() must have been called before
     */
    inline Val next() { return getNextEntry()->_val; }

    /**
     * Return the key of next entry
     * @warning hasNext() must have been called before
     */
    inline Key nextKey() { return getNextEntry()->_key; }

    void del() {
      CALL("DHMap::DelIterator::del");
      _curr->_info.deleted=1;
      _map._size--;
      _map._deleted++;
    }

    void setValue(Val val) {
      CALL("DHMap::DelIterator::setValue");
      _curr->_val = val;
    }

  private:
    Entry* getNextEntry() {
      _curr = _base.next();
      return _curr;
    }

    IteratorBase _base;
    DHMap& _map;
    Entry* _curr;
  }; // class DHMap::Iterator



}; // class DHMap

}

#endif // __DHMap__

