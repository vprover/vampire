/**
 * @file Cache.hpp
 * Defines class Cache.
 */

#ifndef __Cache__
#define __Cache__

#include <iostream>

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Allocator.hpp"

/**
 * When set to 1, at each cache expansion the number of empty cache entries
 * will be printed out. This is to help discover problems with hash functions.
 */
#define REPORT_VACANCIES 0

namespace Lib {

/**
 * A direct mapped cache that expands if the number of cache evictions is
 * too high
 *
 * The number of cache evictions for expancion is two times the size of
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

  void insert(Key k, Val v)
  {
    Entry* e=_data+getPosition(k);

    if(e->_occupied) {
      if(e->_key==k) {
	return;
      }
      _evictionCounter++;

      if(shouldExpand()) {
	expand();
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
  bool shouldExpand() const
  {
    return _evictionCounter>=_evictionThreshold;
  }

  size_t getPosition(Key k) const
  {
    return Hash::hash(k) & _sizeMask;
  }

  void expand()
  {
    expand(_size*2);
  }

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
  size_t _sizeMask;
  Entry* _data;

  size_t _evictionCounter;
  size_t _evictionThreshold;

#if REPORT_VACANCIES
  size_t _vacancies;
#endif
};

}

#endif // __Cache__
