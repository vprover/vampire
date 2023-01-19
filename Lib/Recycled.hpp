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
 * @file Recycled.hpp
 */

#ifndef __Recycled__
#define __Recycled__

#include "Forwards.hpp"

#include "Stack.hpp"
#include "DArray.hpp"

namespace Lib
{

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

  operator bool() const
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

#endif /*__Recycled__*/
