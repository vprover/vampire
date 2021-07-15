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
 * @file Cache.hpp
 * Defines class Cache.
 */

#ifndef __Cache__
#define __Cache__

#include <iostream>

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Shell/Options.hpp"

#include "Allocator.hpp"
#include "Environment.hpp"

#ifndef SIZE_MAX
# define SIZE_MAX ((size_t)-1)
#endif

/**
 * When set to 1, at each cache expansion the number of empty cache entries
 * will be printed out. This is to help discover problems with hash functions.
 */
#define REPORT_VACANCIES 0

/**
 * If cache size is greater than this amount of bytes, it will not be expanded
 */
#define NONEXPANDABLE_CACHE_THRESHOLD MAXIMAL_ALLOCATION/2


namespace Lib {

namespace __Cache_AUX {

using namespace Shell;

/**
 * Return true if cache size can be expanded to number of bytes @c sz.
 */
bool canExpandToBytes(size_t sz)
{
  return sz<(MAXIMAL_ALLOCATION/2) && sz<(env.options->memoryLimit()-Allocator::getUsedMemory());
}

}

using namespace __Cache_AUX;

/**
 * A direct mapped cache that expands if the number of cache evictions is
 * too high
 *
 * The number of cache evictions for expansion is two times the size of
 * the cache. On the expansion, elements previously stored in the cache are
 * not copied.
 *
 * Currently the Cache object is used to implement cache in BDD operations.
 */
template<typename Key, typename Val, class Hash>
class Cache {
private:
  struct Entry {
    Entry() : _occupied(false) {}
    Key _key;
    Val _value;
    bool _occupied;
  };
public:
  Cache() : _size(0), _data(0)
  {
    expand(32);
  }

  ~Cache()
  {
    if(_size) {
      ASS(_data);
      array_delete(_data, _size);
      DEALLOC_KNOWN(_data,_size*sizeof(Entry),"Cache<>");
    }
  }

  bool find(Key k, Val& v) const
  {
    Entry* e=_data+getPosition(k);
    if(e->_occupied && e->_key==k) {
      v=e->_value;
      return true;
    }
    return false;
  }

  bool find(Key k) const
  {
    Entry* e=_data+getPosition(k);
    return e->_occupied && e->_key==k;
  }

  void insert(Key k, Val v=Val())
  {
    Entry* e=_data+getPosition(k);

    if(e->_occupied) {
      if(e->_key==k) {
	return;
      }
      _evictionCounter++;

      if(shouldExpand()) {
	tryExpand();
	e=_data+getPosition(k);
	ASS(!e->_occupied);
      }
    }

    if(!e->_occupied) { //e could have changed from the last time
      e->_occupied=true;
#if REPORT_VACANCIES
    _vacancies--;
#endif
    }
    e->_key=k;
    e->_value=v;
  }

  void resetEvictionCounter()
  {
    _evictionCounter=0;
  }
private:
  /** Return true if the cache should be expanded */
  bool shouldExpand() const
  {
    return _evictionCounter>=_evictionThreshold;
  }

  /** Return the possible position of key @b k in the cache */
  size_t getPosition(Key k) const
  {
    return Hash::hash(k) & _sizeMask;
  }

  /** Expand the cache to double of its current size */
  void tryExpand()
  {
    size_t newSize = _size*2;
    if(canExpandToBytes(newSize*sizeof(Entry))) {
      expand(newSize);
    }
    else {
      //we will never want to expand again if we cannot expand now
      _evictionThreshold=SIZE_MAX;
    }
  }

  /**
   * Expand the cache to @b newSize
   *
   * @b newSize must be a power of two
   */
  void expand(size_t newSize)
  {
    CALL("Cache::expand");
    ASS_G(newSize, _size);

    size_t oldSize=_size;
    Entry* oldData=_data;
#if REPORT_VACANCIES
    size_t oldVacancies=_vacancies;
#endif

    void* mem=ALLOC_KNOWN(newSize*sizeof(Entry),"Cache<>");
    _data=array_new<Entry>(mem, newSize);
    _size=newSize;
    _sizeMask=newSize-1;

    _evictionThreshold=2*newSize;
    _evictionCounter=0;

#if REPORT_VACANCIES
    _vacancies=newSize;
#endif

    if(oldSize) {
      ASS(oldData);
      array_delete(oldData, oldSize);
      DEALLOC_KNOWN(oldData,oldSize*sizeof(Entry),"Cache<>");
#if REPORT_VACANCIES
      std::cout<<"Expanding from "<<oldSize<<" with "<<oldVacancies<<" vacancies to "<<newSize<<endl;
#endif
    }


  }

  /**
   * Size of the cache
   *
   * Has to be a power of two.
   */
  size_t _size;

  /**
   * Mask for computing the modulo by cache size (taking advantage
   * of the fact that @b _size is a power of two)
   */
  size_t _sizeMask;

  /** Array of @b _size entries containing the cached values */
  Entry* _data;

  /**
   * Number of evictions that occurred since the last cache expansion
   */
  size_t _evictionCounter;
  /**
   * Number of evictions that must occurr to trigger next cache expansion
   *
   * We check whether we should expand in the @b shouldExpand function.
   */
  size_t _evictionThreshold;

#if REPORT_VACANCIES
  /** Number of empty cache entries */
  size_t _vacancies;
#endif
};

}

#endif // __Cache__
