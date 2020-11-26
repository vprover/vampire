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
 * @file Set.hpp
 * Defines class SharedSet.
 */

#ifndef __SharedSet__
#define __SharedSet__

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Allocator.hpp"
#include "Metaiterators.hpp"
#include "Set.hpp"
#include "Sort.hpp"
#include "Stack.hpp"
#include "VString.hpp"

namespace Lib {

using namespace std;

template<typename T>
class SharedSet {

  typedef Stack<T> ItemStack;

public:
  DECL_ELEMENT_TYPE(T);

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

  bool member(T val) const
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
	l=m+1;
      }
      else {
	ASS_G(mv,val);
	r=m;
      }
    }
    return false;
  }

  const SharedSet* getUnion(const SharedSet* s) const
  {
    CALL("SharedSet::getUnion");
    ASS(s);

    if(s==this || s->isEmpty()) {
      return this;
    }
    if(isEmpty()) {
      return s;
    }

    bool p1Superset = true;
    bool p2Superset = true;

    static ItemStack acc;
    acc.reset();

    const T* p1=_items;
    const T* p2=s->_items;
    const T* p1e=p1+size();
    const T* p2e=p2+s->size();

    while(p1!=p1e && p2!=p2e) {
      if(*p1==*p2) {
	acc.push(*p1);
	p1++;
	p2++;
      }
      else if(*p1>*p2) {
	acc.push(*p2);
	p2++;
	p1Superset = false;
      }
      else {
	ASS_L(*p1,*p2);
	acc.push(*p1);
	p1++;
	p2Superset = false;
      }
    }

    while(p1!=p1e) {
      acc.push(*p1);
      p1++;
      p2Superset = false;
    }
    while(p2!=p2e) {
      acc.push(*p2);
      p2++;
      p1Superset = false;
    }

    ASS(!p1Superset || !p2Superset);
    if(p1Superset) {
      return this;
    }
    if(p2Superset) {
      return s;
    }

    const SharedSet* res=create(acc);
    return res;
  }

  const SharedSet* getIntersection(const SharedSet* s) const
  {
    CALL("SharedSet::getIntersection");
    ASS(s);

    if(s==this) {
      return this;
    }

    static ItemStack acc;
    ASS(acc.isEmpty());

    const T* p1=_items;
    const T* p2=s->_items;
    const T* p1e=p1+size();
    const T* p2e=p2+s->size();

    while(p1!=p1e && p2!=p2e) {
      if(*p1==*p2) {
	acc.push(*p1);
	p1++;
	p2++;
      }
      else if(*p1>*p2) {
	p2++;
      }
      else {
	ASS_L(*p1,*p2);
	p1++;
      }
    }

    const SharedSet* res=create(acc);
    acc.reset();
    return res;
  }


  /**
   * Subtract a set @b s from the current set and return the result
   */
  const SharedSet* subtract(const SharedSet* s) const
  {
    CALL("SharedSet::subtract");
    ASS(s);

    if(s==this) {
      return getEmpty();
    }

    static ItemStack acc;
    ASS(acc.isEmpty());

    const T* p1=_items;
    const T* p2=s->_items;
    const T* p1e=p1+size();
    const T* p2e=p2+s->size();

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

    const SharedSet* res=create(acc);
    acc.reset();
    return res;
  }

  bool hasIntersection(const SharedSet* s) const
  {
    CALL("SharedSet::hasIntersection");
    ASS(s);

    const T* p1=_items;
    const T* p2=s->_items;
    const T* p1e=p1+size();
    const T* p2e=p2+s->size();

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

  bool isSubsetOf(const SharedSet* s) const
  {
    CALL("SharedSet::isSubsetOf");
    ASS(s);

    if(s->size()<size()) {
      return false;
    }
    if(s==this) {
      return true;
    }

    const T* p1=_items;
    const T* p2=s->_items;
    const T* p1e=p1+size();
    const T* p2e=p2+s->size();

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
	return false;
      }
    }
    if(p2==p2e && p1!=p1e) {
      return false;
    }

    return true;
  }


  vstring toString() const
  {
    CALL("SharedSet::toString");

    vostringstream res;
    res<<(*this);
    return res.str();
  }

  static const SharedSet* getEmpty()
  {
    CALL("SharedSet::getEmpty");

    static SharedSet empty(0);    
    
    return &empty;
  }

  static const SharedSet* getRange(T first, T afterLast)
  {
    CALL("SharedSet::getRange");

    static ItemStack is;
    ASS(is.isEmpty());

    for(T itm=first;itm!=afterLast;itm++) {
      is.push(itm);
    }

    const SharedSet* res=create(is);
    is.reset();

    return res;
  }

  template<class It>
  static const SharedSet* getFromIterator(It it)
  {
    static ItemStack is;
    is.reset();
    is.loadFromIterator(it);
    return getFromArray(is.begin(), is.length());
  }

  static const SharedSet* getFromArray(T* arr, size_t len)
  {
    CALL("SharedSet::getFromArray");

    if(!len) {
      return getEmpty();
    }

    static ItemStack is;
    ASS(is.isEmpty());

    bool sorted=true;
    bool unique=true;
    is.push(arr[0]);
    for(size_t i=1; i<len; i++) {
      is.push(arr[i]);
      if(arr[i-1]>arr[i]) {
	sorted = false;
      }
      else if(arr[i-1]==arr[i]) {
	unique = false;
      }
    }
    if(!sorted) {
      sort<DefaultComparator>(is.begin(), is.end());
      unique = false; //maybe they are unique, we just need to check
    }
    if(!unique) {
      typename ItemStack::StableDelIterator uit(is);
      ALWAYS(uit.hasNext());
      T prev = uit.next();
      while(uit.hasNext()) {
	T curr = uit.next();
	if(curr==prev) {
	  uit.del();
	}
	else {
	  prev = curr;
	}
      }
    }

    const SharedSet* res=create(is);
    is.reset();

    return res;
  }

  static const SharedSet* getSingleton(T val)
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
  
  void operator delete (void* obj)
  {
    CALL("SharedSet::operator delete");
    
    SharedSet* ss = static_cast<SharedSet*>(obj);
    
    // calculate the same thing as in operator new
    size_t size=sizeof(SharedSet)+ss->_size*sizeof(T);
    size-=sizeof(T);
  
    DEALLOC_KNOWN(obj, size,"SharedSet");
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

  static const SharedSet* create(const ItemStack& is)
  {
    CALL("SharedSet::create");

    size_t sz=is.size();

    if(!sz) {
      return getEmpty();
    }

    SharedSet* res;
    if(getSStruct().find(is,res)) {
      return res;
    }

    res=new(sz) SharedSet(sz);
    for(size_t i=0;i<sz;i++) {
      ASS(i==0 || is[i-1]<is[i]);
      res->_items[i]=is[i];
    }

    getSStruct().insert(res);
    return res;
  }

  class SharingStruct {
    typedef Set<SharedSet*, SharedSet> InternalSharingSet;
    
    /* starts empty */ 
    InternalSharingSet _data;
  
  public:
    /* forward find */
    bool find(const ItemStack& key,SharedSet*& result) {
      return _data.find(key,result);
    }
    
    /* forward insert */
    void insert(SharedSet* val) {
      _data.insert(val);
    }
    
    /* delete all stored items */
    ~SharingStruct() {
      typename InternalSharingSet::Iterator it(_data);
      while(it.hasNext())
        delete it.next();    
    }
  };

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
    Iterator(const SharedSet& s) : PointerIterator<T>(s._items, s._items+s.size()) {}
  };

};

template<typename T>
std::ostream& operator<< (ostream& out, const SharedSet<T>& s )
{
  typename SharedSet<T>::Iterator it(s);
  while(it.hasNext()) {
    out<<it.next();
    if(it.hasNext()) {
      out<<", ";
    }
  }
  return out;
}


}

#endif // __SharedSet__
