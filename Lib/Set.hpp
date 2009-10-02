/**
 * @file Set.hpp
 * Defines class Set<Type> of arbitrary sets, implemented in the same way
 * as Map.
 */

#ifndef __Set__
#define __Set__

#include <cstdlib>

#include "Allocator.hpp"
#include "Hash.hpp"
#include "Reflection.hpp"

namespace Lib {

/**
 * Defines class Set<Val> of arbitrary sets, implemented in the same way
 * as Map. Values are compared using Hash::equals.
 */
template <typename Val,class Hash=Lib::Hash>
class Set
{
protected:
  class Entry
  {
  public:
    /** Create a new entry */
    inline Entry ()
      : code(0)
    {
    } // Set::Entry::Entry

    /** True if the cell is occupied */
    inline bool occupied () const
    {
      return code;
    } // Set::Entry::occupied

    /** declared but not defined, to prevent on-heap allocation */
    void* operator new (size_t);

    /** Hash code of the value, 0 if not occupied */
    unsigned code;
    /** The value in this cell (if any) */
    Val value;
  }; // class Set::Entry

public:
  /** Create a new Set */
  Set()
    : _capacity(0),
      _noOfEntries(0),
      _entries(0)
  {
    CALL("Set::Set");
    expand();
  } // Set::Set

  /** Deallocate the set */
  inline ~Set ()
  {
    if (_entries) {
      DEALLOC_KNOWN(_entries,_capacity*sizeof(Entry),"Set::Entry");
    }
  } // Set::~Set

  /**
   * If the set contains value equal to @b key, return true,
   * and assign the value to @b result
   */
  template<typename Key>
  bool find (Key key, Val& result) const
  {
    CALL("Set::contains");

    unsigned code = Hash::hash(key);
    if (code == 0) {
      code = 1;
    }
    for (Entry* entry = firstEntryForCode(code);
	 entry->occupied();
	 entry = nextEntry(entry)) {
      if (entry->code == code &&
	  Hash::equals(entry->value,key)) {
	result=entry->value;
	return true;
      }
    }
    return false;
  } // Set::contains

  /**
   * True if the set contains @b val.
   * @since 29/09/2002 Manchester
   */
  bool contains (Val val) const
  {
    CALL("Set::contains");

    unsigned code = Hash::hash(val);
    if (code == 0) {
      code = 1;
    }
    for (Entry* entry = firstEntryForCode(code);
	 entry->occupied();
	 entry = nextEntry(entry)) {
      if (entry->code == code &&
	  Hash::equals(entry->value,val)) {
	return true;
      }
    }
    return false;
  } // Set::contains

  /**
   * If a value equal to @b val is not contained in the set, insert @b val
   * in the set.
   * Return the value equal to @b val from the set.
   * @since 29/09/2002 Manchester
   * @since 09/12/2006 Manchester, reimplemented
   */
  inline Val insert(const Val val)
  {
    CALL("Set::insert");

    if (_noOfEntries >= _maxEntries) { // too many entries
      expand();
    }

    unsigned code;
    code = Hash::hash(val);

    if (code == 0) {
      code = 1;
    }

    return insert(val,code);
  } // Set::insert

  /**
   * Insert a value with a given code in the set.
   * The set must have a sufficient capacity
   * @since 09/12/2006 Manchester, reimplemented
   */
  Val insert(const Val val,unsigned code)
  {
    CALL("Set::insert/2");

    Entry* entry;
    for (entry = firstEntryForCode(code);
	 entry->occupied();
	 entry = nextEntry(entry)) {
      if (entry->code == code &&
	  Hash::equals(entry->value,val)) {
	return entry->value;
      }
    }
    // entry is not occupied
    _noOfEntries++;
    entry->value = val;
    entry->code = code;
    return entry->value;
  } // Set::insert

  /** Insert all elements from @b it iterator in the set */
  template<class It>
  void insertFromIterator(It it)
  {
    while(it.hasNext()) {
      insert(it.next());
    }
  }

  /** Return the number of elements */
  inline int numberOfElements() const
  {
    return _noOfEntries;
  }

  // declared but not defined, to prevent on-heap allocation
  void* operator new (size_t);

  /** the current capacity */
  int _capacity;
  /** the current number of entries */
  int _noOfEntries;
  /** the array of entries */
  Entry* _entries;
  /** the entry after the last one, required since the
   *  array of entries is logically a ring */
  Entry* _afterLast; // entry after the last one
  /** the maximal number of entries for this capacity */
  int _maxEntries;

  /**
   * Expand the set to the next available capacity
   * @throws Exception if map cannot be expanded (that is,
   *         maximal capacity exceeded)
   * @since 29/09/2002 Manchester
   */
  void expand()
  {
    CALL("Set::expand");

    size_t newCapacity = _capacity ? _capacity * 2 : 31;
    Entry* oldEntries = _entries;

    void* mem = ALLOC_KNOWN(newCapacity*sizeof(Entry),"Set::Entry");

    _entries = new(mem) Entry [newCapacity];
    _afterLast = _entries + newCapacity;
    _maxEntries = (int)(newCapacity * 0.8);
    size_t oldCapacity = _capacity;
    _capacity = newCapacity;

    // experiments using (a) random numbers (b) consecutive numbers
    // and 30,000,000 allocations
    // 0.6 :  8.49 7.55
    // 0.7 :  9.19 7.71
    // 0.8 :  9.10 8.44
    // 0.9 :  9.34 7.36 (fewer allocations (21 vs. 22), fewer cache faults)
    // 0.95: 10.21 7.48
    // copy old entries
    Entry* current = oldEntries;
    int remaining = _noOfEntries;
    _noOfEntries = 0;
    while (remaining != 0) {
      // find first occupied entry
      while (! current->occupied()) {
	current ++;
      }
      // now current is occupied
      insert(current->value,current->code);
      current ++;
      remaining --;
    }

    if (oldEntries) {
      DEALLOC_KNOWN(oldEntries,oldCapacity*sizeof(Entry),"Set::Entry");
    }
  } // Set::expand

  /**
   * Return the entry next to @b entry.
   * @since 09/12/2006 Manchester
   */
  inline Entry* nextEntry(Entry* entry) const
  {
    entry ++;
    // check if the entry is a valid one
    return entry == _afterLast ? _entries : entry;
  } // nextEntry

  /**
   * Return the first entry for @b code.
   * @since 09/12/2006 Manchester
   */
  inline Entry* firstEntryForCode(unsigned code) const
  {
    return _entries + (code % _capacity);
  } // Set::firstEntryForCode

public:
  /**
   * Class to allow iteration over values stored in the set.
   * @since 13/08/2005 Novotel, Moscow
   */
  class Iterator {
  public:
    DECL_ELEMENT_TYPE(Val);

    /** Create a new empty iterator */
    inline Iterator() : _next(0), _last(0) {}

    /** Create a new iterator */
    explicit inline Iterator(const Set& set)
      : _next(set._entries),
	_last(set._afterLast)
    {
    } // Set::Iterator

    /**
     * True if there exists next element
     * @since 13/08/2005 Novotel, Moscow
     */
    bool hasNext()
    {
      while (_next != _last) {
	if (_next->occupied()) {
	  return true;
	}
	_next++;
      }
      return false;
    } // Set::Iterator::hasNext

    /**
     * Return the next value
     * @since 13/08/2005 Novotel, Moscow
     * @warning hasNext() must have been called before
     */
    Val next()
    {
      ASS(_next != _last);
      ASS(_next->occupied());
      Val result = _next->value;
      _next++;
      return result;
    } // Set::Iterator::next

  private:
    /** iterator will look for the next occupied cell starting with this one */
    Entry* _next;
    /** iterator will stop looking for the next cell after reaching this one */
    Entry* _last;
  };

}; // class Set


}

#endif // __Set__

