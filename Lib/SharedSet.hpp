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
#include "Metaiterators.hpp"
#include "Set.hpp"
#include "Sort.hpp"
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

  inline T operator[] (size_t n) const
  {
    CALL("SharedSet::operator[]");
    ASS_L(n,size());

    return _items[n];
  }

  /**
   * Return value of the item in a singleton set
   */
  inline T sval() const
  {
    CALL("SharedSet::sval");
    ASS_EQ(size(),1);

    return (*this)[0];
  }

  /**
   * Return value of the maximal item in a non-empty set
   */
  inline T maxval() const
  {
    CALL("SharedSet::maxval");
    ASS(!isEmpty());

    return (*this)[size()-1];
  }

  bool member(T val)
  {
    CALL("SharedSet::member");

    size_t l=0;
    size_t r=size();
    while(l<r) {
      size_t m=(l+r)>>1;
      T mv=(*this)[m];
      if(mv==val) {
	return true;
      }
      else if(mv<val) {
	r=m;
      }
      else {
	ASS_G(mv,val);
	l=m+1;
      }
    }
    return false;
  }

  SharedSet* getUnion(SharedSet* s)
  {
    CALL("SharedSet::getUnion");

    static ItemStack acc;
    ASS(acc.isEmpty());

    T* p1=_items;
    T* p2=s->_items;
    T* p1e=p1+size();
    T* p2e=p2+s->size();

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
    CALL("SharedSet::subtract");

    static ItemStack acc;
    ASS(acc.isEmpty());

    T* p1=_items;
    T* p2=s->_items;
    T* p1e=p1+size();
    T* p2e=p2+s->size();

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

  bool hasIntersection(SharedSet* s)
  {
    CALL("SharedSet::hasIntersection");

    T* p1=_items;
    T* p2=s->_items;
    T* p1e=p1+size();
    T* p2e=p2+s->size();

    while(p1!=p1e && p2!=p2e) {
      if(*p1==*p2) {
	return true;
      }
      else if(*p1>*p2) {
	p2++;
      }
      else {
	ASS_L(*p1,*p2);
	p1++;
      }
    }

    return false;
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

  static SharedSet* getFromArray(T* arr, size_t len)
  {
    CALL("SharedSet::getFromArray");

    if(!len) {
      return getEmpty();
    }

    static ItemStack is;
    ASS(is.isEmpty());

    bool sorted=true;
    is.push(arr[0]);
    for(size_t i=1; i<len; i++) {
      is.push(arr[i]);
      if(sorted && arr[i-1]>arr[i]) {
	sorted&=false;
      }
    }
    if(!sorted) {
      sort<DefaultComparator>(is.begin(), is.end());
    }
    SharedSet* res=create(is);
    is.pop();

    return res;
  }

  static SharedSet* getSingleton(T val)
  {
    CALL("SharedSet::getSingleton");

    return getFromArray(&val, 1);
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


  static bool equals(const T* arr1, const T* arr2, size_t len)
  {
    CALL("SharedSet::equals(T*,T*,size_t)");

    const T* arr1e=arr1+len;
    while(arr1!=arr1e) {
      if(*arr1!=*arr2) {
	return false;
      }
      arr1++;
      arr2++;
    }
    return true;
  }
  static unsigned hash(const T* arr, size_t len)
  {
    CALL("SharedSet::hash(T*,size_t)");

    unsigned res=1234567890; //arbitrary number, hopefully won't cause problems:)
    const T* arre=arr+len;
    while(arr!=arre) {
      res=Hash::hash(*arr,res);
      arr++;
    }
    return res;
  }

  static SharedSet* create(const ItemStack& is)
  {
    CALL("SharedSet::create");

    size_t sz=is.size();

    if(!sz) {
      return getEmpty();
    }

    SharedSet* res;
    if(getSStruct().find<const ItemStack&>(is,res)) {
      return res;
    }

    res=new(sz) SharedSet(sz);
    for(size_t i=0;i<sz;i++) {
      res->_items[i]=is[i];
    }

    getSStruct().insert(res);
    return res;
  }

  typedef Set<SharedSet*, SharedSet> SharingStruct;

  static SharingStruct& getSStruct()
  {
    static SharingStruct sstruct;
    return sstruct;
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
    if(s1->size()!=is.size()) {
      return false;
    }
    return equals(s1->_items, is.begin(), s1->size());
  }

  static unsigned hash(const ItemStack& is)
  {
    return hash(is.begin(), is.size());
  }

  class Iterator : public PointerIterator<T>
  {
  public:
    Iterator(const SharedSet* s) : PointerIterator<T>(s->_items, s->_items+s->size()) {}
  };

};

}

#endif // __SharedSet__
