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

/** A smart pointer that lets you keep memory allocated, and reuse it.
 * Constructs an object of type T on the heap. When the Recycled<T> is destroyed,
 * the object is not returned, but the object is reset using Reset::operator(),
 * and returned to a pool of pre-allocated objects. When the next Recycled<T> is
 * constructed an object from the pool is returned instead of allocating heap memory.
 *
 * This may be useful if profiling suggests it, but in general you should not need this.
 * If you think you do, there are the following tradeoffs:
 * - more construction overhead than both automatic and (slightly) static storage
 * - extra indirection: Recycled<T> internally holds a pointer to T
 * - shares allocations of type T between all instances of Recycled<T>
 * - safer than static storage due to the Reset mechanism
 * - Recycled<T> is reentrant, whereas static is not
 * - "leaks" memory, retaining the peak number of concurrently-live T objects
 * - implements move semantics where T may not
 * - "destruction" often very cheap because T is never destroyed
 *
 * To summarise:
 * 1. Use automatic storage unless you really have to do something else.
 * 2. If you must, use Recycled<T> by preference to static for safety reasons.
 * 3. If you really must and you are sure of correctness (reentrancy, reset logic),
 *    use static storage.
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
