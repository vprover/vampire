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
 * @file RCPtr.hpp
 * Defines class RCPtr.
 */

#ifndef __RCPtr__
#define __RCPtr__

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Metaiterators.hpp"

namespace Lib {

/**
 * Reference counting pointer
 */
template<class T>
class RCPtr {
public:
  inline
  RCPtr() : _obj(0) {}
  /**
   * Create a smart pointer containing pointer @b obj.
   */
  inline
  explicit RCPtr(T* obj) : _obj(obj)
  {
    if(obj) {
      _obj->incRefCnt();
    }
  }
  inline
  RCPtr(const RCPtr& ptr) : _obj(ptr._obj)
  {
    if(_obj) {
      _obj->incRefCnt();
    }
  }
  inline
  ~RCPtr()
  {
    if(_obj) {
      _obj->decRefCnt();
    }
  }
  RCPtr& operator=(T* newObj)
  {
    CALL("RCPtr::operator=(T*)");

    T* oldObj=_obj;
    _obj=newObj;

    if(_obj) {
      _obj->incRefCnt();
    }

    if(oldObj) {
      oldObj->decRefCnt();
    }
    return *this;
  }
  RCPtr& operator=(const RCPtr& ptr)
  {
    CALL("RCPtr::operator=(const RCPtr&)");

    return (*this)=ptr.ptr();
  }
  bool operator==(const RCPtr& o) const { return ptr()==o.ptr(); }
  bool operator!=(const RCPtr& o) const { return !((*this)==o); }

  inline
  operator bool() const { return _obj; }

  inline
  T* operator->() const { ASS(_obj); return _obj; }
  inline
  T& operator*() const { ASS(_obj); return *_obj; }

  inline
  T* ptr() const { return _obj; }

  inline
  bool isEmpty() const { return !_obj; }

  template<class Target>
  inline
  Target* pcast() const { return static_cast<Target*>(_obj); }

  static List<T*>* unRCList(List<RCPtr>* l)
  {
    CALL("RCPtr::unRCList");

    List<T*>* res = 0;
    typename List<RCPtr>::Iterator it(l);
    while(it.hasNext()) {
      List<T*>::push(it.next().ptr(), res);
    }
    return res;
  }
  static List<RCPtr>* enRCList(List<T*>* l)
  {
    CALL("RCPtr::enRCList");

    List<RCPtr>* res = 0;
    List<RCPtr>::pushFromIterator(getStaticCastIterator<RCPtr>(List<T*>::Iterator(l)), res);
    return res;
  }

  struct UnRCFunctor
  {
    T* operator()(const RCPtr& p) const {
      return p.ptr();
    }
  };
private:
  T* _obj;
};

}

#endif // __RCPtr__
