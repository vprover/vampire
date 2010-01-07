/**
 * @file Set.hpp
 * Defines class SharedSet.
 */

#ifndef __SharedSet__
#define __SharedSet__

#include "../Forwards.hpp"

#include "../Debug/Assertion.hpp"
#include "../Debug/Tracer.hpp"

#include "Allocator.hpp"
#include "Set.hpp"
#include "Stack.hpp"

namespace Lib {


template<typename T>
class SharedSet {
public:
  typedef Stack<T> ItemStack;

  SharedSet(size_t sz) : _size(sz) {}

  /** Return the size of the set */
  inline unsigned size() const {
    return _size;
  }

  inline bool isEmpty() const { return !_size; }

  inline T operator[] (int n) const
  {
    CALL("SharedSet::operator[]");
    ASS_L(n,size());

    return _items[n];
  }

  SharedSet* getUnion(SharedSet* s)
  {
    CALL("SharedSet::getUnion");

    static ItemStack acc;
    ASS(acc.isEmpty());

    T* p1=_items;
    T* p2=s->_items;
    T* p1e=size();
    T* p2e=s->size();

    while(p1!=p1e && p2!=p2e) {
      if(*p1==*p2) {
	acc.push(*p1);
	p1++;
	p2++;
      }
      else if(*p1>*p2) {
	acc.push(*p2);
	p2++;
      }
      else {
	ASS_L(*p1,*p2);
	acc.push(*p1);
	p1++;
      }
    }

    while(p1!=p1e) {
      acc.push(*p1);
      p1++;
    }
    while(p2!=p2e) {
      acc.push(*p2);
      p2++;
    }

    SharedSet* res=create(acc);
    acc.reset();
    return res;
  }

  /**
   * Subtract a set @b s from the current set and return the result
   */
  SharedSet* subtract(SharedSet* s)
  {
    CALL("SharedSet::getUnion");

    static ItemStack acc;
    ASS(acc.isEmpty());

    T* p1=_items;
    T* p2=s->_items;
    T* p1e=size();
    T* p2e=s->size();

    while(p1!=p1e && p2!=p2e) {
      if(*p1==*p2) {
	p1++;
	p2++;
      }
      else if(*p1>*p2) {
	p2++;
      }
      else {
	ASS_L(*p1,*p2);
	acc.push(*p1);
	p1++;
      }
    }

    while(p1!=p1e) {
      acc.push(*p1);
      p1++;
    }

    SharedSet* res=create(acc);
    acc.reset();
    return res;
  }


  static SharedSet* getEmpty()
  {
    CALL("SharedSet::getEmpty");

    static SharedSet* empty=0;
    if(!empty) {
      empty=new(0) SharedSet(0);
    }
    return empty;
  }

  static SharedSet* getSingleton(T val)
  {
    CALL("SharedSet::getSingleton");

    static ItemStack is(1);
    ASS(is.isEmpty());

    is.push(val);
    SharedSet* res=create(is);
    is.pop();

    return res;
  }

private:
  void* operator new(size_t sz,size_t length)
  {
    CALL("SharedSet::operator new");

    //We have to get sizeof(SharedSet) + (length-1)*sizeof(T)
    //this way, because length-1 wouldn't behave well for
    //length==0 on x64 platform.
    size_t size=sizeof(SharedSet)+length*sizeof(T);
    size-=sizeof(T);

    return ALLOC_KNOWN(size,"SharedSet");
  }

  size_t _size;
  T _items[1];


  static bool equals(T* arr1, T* arr2, size_t len)
  {
    CALL("SharedSet::equals(T*,T*,size_t)");

    T* arr1e=arr1+len;
    while(arr1!=arr1e) {
      if(*arr1!=*arr2) {
	return false;
      }
      arr1++;
      arr2++;
    }
    return true;
  }
  static unsigned hash(T* arr, size_t len)
  {
    CALL("SharedSet::hash(T*,size_t)");

    unsigned res=1234567890; //arbitrary number, hopefully won't cause problems:)
    T* arre=arr+len;
    while(arr!=arre) {
      res=Hash::hash(*arr,res);
      arr++;
    }
    return res;
  }

  static SharedSet* create(const ItemStack& is)
  {
    CALL("SharedSet::create");

    size_t sz=is->size();

    if(!sz) {
      return getEmpty();
    }

    SharedSet* res;
    if(_sharing.find(is,res)) {
      return res;
    }

    res=new(sz) SharedSet(sz);
    for(size_t i=0;i<sz;i++) {
      res->_items[i]=is[i];
    }

    _sharing.insert(res);
    return res;
  }

public:

  static bool equals(const SharedSet* s1,const SharedSet* s2)
  {
    if(s1->size()!=s2->size()) {
      return false;
    }
    return equals(s1->_items, s2->_items, s1->size());
  }

  static unsigned hash(const SharedSet* s)
  {
    return hash(s->_items, s->size());
  }

  static bool equals(const SharedSet* s1,const ItemStack& is)
  {
    if(s1->size()!=is->size()) {
      return false;
    }
    return equals(s1->_items, is->begin(), s1->size());
  }

  static unsigned hash(const ItemStack& is)
  {
    return hash(is->begin(), is->size());
  }


  static Set<SharedSet> _sharing;

};

}

#endif // __SharedSet__
