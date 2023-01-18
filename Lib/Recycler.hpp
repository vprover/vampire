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
 * @file Recycler.hpp
 *
 * @since 08/05/2007 Manchester
 */

#ifndef __Recycler__
#define __Recycler__

#include "Forwards.hpp"

#include "Stack.hpp"
#include "DArray.hpp"

namespace Lib
{

/** * A class that keeps objects of type T allocated. 
 * This is for example useful for hot functions that will allocate a todo stack whenever they are called. 
 * In order to use less allocation time we can get a pre-allocated stack from the Recycler, and return 
 * it when we don't need it anymore.
 *
 * Best practice is to not use this class directly, but to use the related smart pointer Recycled<T>
 * instead.
 */
class Recycler {
public:
  template<typename T>
  static void get(T*& result)
  {
    Stack<T*>& store=getStore<T>();
    if(store.isNonEmpty()) {
      result=store.pop();
    } else {
      result=new T();
    }
  }

  template<typename T>
  static void get(DArray<T>*& result)
  {
    Stack<DArray<T>*>& store=getStore<DArray<T> >();
    if(store.isNonEmpty()) {
      result=store.pop();
    } else {
      result=new DArray<T>(64);
      result->ensure(0);
    }
  }


  template<typename T>
  static void release(T* obj)
  {
    ASS(obj);

    Stack<T*>& store=getStore<T>();

    store.push(obj);
  }


private:

  /*
  * A Stack which deletes its elements at the end.
  */
  template<typename T> 
  struct OwnedPtrStack : public Stack<T*>
  {  
    inline
    explicit OwnedPtrStack (size_t initialCapacity=0)
      : Stack<T*> (initialCapacity) { }
  
    inline ~OwnedPtrStack() { 
      while (this->isNonEmpty())
        delete (this->pop());
     }
  };

  template<typename T>
  static Stack<T*>& getStore() throw()
  {
    static OwnedPtrStack<T> store(4);
    return store;
  }
};

struct DefaultReset 
{ template<class T> void operator()(T& t) { t.reset(); } };

struct NoReset 
{ template<class T> void operator()(T& t) {  } };



/** A smart that lets you keep memory allocated, and reuse it.
 * Constructs an object of type T on the heap. When the Recycled<T> is destroyed,
 * the object is not returned, but the object is reset using Reset::operator(), 
 * and returned to a pool of pre-allocated objects. When the next Recycled<T> is
 * constructed an object from the pool is returned instead of allocating heap memory.
 */
template<class T, class Reset = DefaultReset>
class Recycled
{
  unique_ptr<T> _ptr;
  Reset _reset;

  static Stack<unique_ptr<T>>& mem() {
    static Stack<unique_ptr<T>> mem;
    return mem;
  }
public: 

  Recycled()
    : _ptr(mem().isNonEmpty() ? mem().pop() : make_unique<T>()) 
    , _reset()
  { }

  Recycled(Recycled&& other) = default;
  Recycled& operator=(Recycled&& other) = default;

  operator bool() 
  { return bool(_ptr); }


  ~Recycled()
  { 
    if (_ptr) {
      _reset(*_ptr);
      mem().push(std::move(_ptr));
    }
  }

  T const& operator* () const { ASS(*this); return  *_ptr; }
  T const* operator->() const { ASS(*this); return &*_ptr; }
  T& operator* () {  ASS(*this); return  *_ptr; }
  T* operator->() {  ASS(*this); return &*_ptr; }

  friend std::ostream& operator<<(std::ostream& out, Recycled const& self)
  { return self._ptr ? out << *self._ptr : out << "Recycled(nullptr)"; }
};

};

#endif /*__Recycler__*/
