/**
 * @file Unit.hpp
 * Defines class SmartPtr for smart pointers
 *
 * @since 08/05/2007 Manchester
 */

#ifndef __SmartPtr__
#define __SmartPtr__

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

namespace Lib
{

template<typename T>
class SmartPtr {
public:
  inline
  SmartPtr() : _obj(0), _refCnt(0) {}
  /**
   * Create a smart pointer containing pointer @b obj. If @b nondisposable
   * is true, the object will not be destroyed even after all references to
   * it are gone.
   */
  inline
  explicit SmartPtr(T* obj, bool nondisposable=false)
  : _obj(obj), _refCnt(nondisposable ? 0 : new int(1)) {ASS(obj);}
  inline
  SmartPtr(const SmartPtr& ptr) : _obj(ptr._obj), _refCnt(ptr._refCnt)
  {
    if(_obj && _refCnt) {
      (*_refCnt)++;
    }
  }
  inline
  ~SmartPtr()
  {
    if(!_obj || !_refCnt) {
      return;
    }
    (*_refCnt)--;
    ASS(*_refCnt>=0);
    if(! *_refCnt) {
      checked_delete(_obj);
      delete _refCnt;
    }
  }
  SmartPtr& operator=(const SmartPtr& ptr)
  {
    CALL("SmartPtr::operator=");

    T* oldObj=_obj;
    int* oldCnt=_refCnt;
    _obj=ptr._obj;
    _refCnt=ptr._refCnt;

    if(_obj && _refCnt) {
      (*_refCnt)++;
    }

    if(oldObj && oldCnt) {
      (*oldCnt)--;
      ASS(*oldCnt>=0);
      if(! *oldCnt) {
	checked_delete(oldObj);
	delete oldCnt;
      }
    }
    return *this;
  }

  inline
  operator bool() { return _obj; }

  inline
  T* operator->() { return _obj; }
  inline
  T& operator*() { return *_obj; }

  inline
  T* ptr() { return _obj; }

  inline
  T& ref() { return *_obj; }

  inline
  bool isEmpty() { return !_obj; }

  template<class Target>
  inline
  Target* pcast() { return static_cast<Target*>(_obj); }
private:
  template<typename U> friend class SmartPtr;

  T* _obj;
  int* _refCnt;
};

};

#endif /*__SmartPtr__*/
