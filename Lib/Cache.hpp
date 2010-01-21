/**
 * @file Cache.hpp
 * Defines class Cache.
 */

#ifndef __Cache__
#define __Cache__

#include <iostream>

#include "../Forwards.hpp"

#include "../Debug/Assertion.hpp"

#include "Allocator.hpp"

#define REPORT_VACANCIES 0

namespace Lib {

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
  bool shouldExpand() const
  {
    return _evictionCounter>=_evictionTreshold;
  }
private:
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

    if(_size) {
      ASS(_data);
      array_delete(_data, _size);
      DEALLOC_KNOWN(_data,_size*sizeof(Entry),"Cache<>");
#if REPORT_VACANCIES
      std::cout<<"Expanding from "<<_size<<" with "<<_vacancies<<" vacancies to "<<newSize<<endl;
#endif
    }

    _size=newSize;
    _sizeMask=_size-1;
    void* mem=ALLOC_KNOWN(_size*sizeof(Entry),"Cache<>");
    _data=array_new<Entry>(mem, _size);

    _evictionTreshold=2*_size;
    _evictionCounter=0;

#if REPORT_VACANCIES
    _vacancies=_size;
#endif
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
  size_t _evictionTreshold;

#if REPORT_VACANCIES
  size_t _vacancies;
#endif
};

}

#endif // __Cache__
