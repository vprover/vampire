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
#include <initializer_list>
#include "Lib/Reflection.hpp"
#include "Lib/Hash.hpp"

namespace Lib
{

struct DefaultReset
{ template<class T> void operator()(T& t) { t.reset(); } };

struct DefaultKeepRecycled
{ template<class T> bool operator()(T const& t) { return t.keepRecycled(); } };

struct NoReset
{ template<class T> void operator()(T& t) {  } };

template<class T>
struct MaybeAlive
{
  T _self;
  bool* _alive;
  MaybeAlive(T self, bool* alive)
    : _self(std::move(self)), _alive(alive)
  { *_alive = true; }
  ~MaybeAlive() { *_alive = false; }


  T const& operator* () const { return  _self; }
  T const* operator->() const { return &_self; }
  T& operator* () { return  _self; }
  T* operator->() { return &_self; }
};
/** A smart that lets you keep memory allocated, and reuse it.
 * Constructs an object of type T on the heap. When the Recycled<T> is destroyed,
 * the object is not returned, but the object is reset using Reset::operator(),
 * and returned to a pool of pre-allocated objects. When the next Recycled<T> is
 * constructed an object from the pool is returned instead of allocating heap memory.
 */
template<class T, class Reset = DefaultReset, class Keep = DefaultKeepRecycled>
class Recycled
{
  T _ptr;
  Reset _reset;
  Keep _keep;

  static bool alive;
  static Stack<T>& mem() {
    static MaybeAlive<Stack<T>> mem(Stack<T>(), &alive);
    return *mem;
  }
  Recycled(Recycled const&) = delete;
public:

  Recycled()
    : _ptr(mem().isNonEmpty() ? mem().pop() : T())
    , _reset()
    , _keep()
  { }

  template<class Clone>
  Recycled clone(Clone cloneFn) const
  {
    Recycled c;
    T const& from = **this;
    T& to = *c;
    cloneFn(to, from);
    return c;
  }


  auto asTuple() const -> decltype(auto) { return std::tie(_ptr); }
  IMPL_COMPARISONS_FROM_TUPLE(Recycled);
  IMPL_HASH_FROM_TUPLE(Recycled);

  template<class A, class... As>
  Recycled(A a, As... as)
    : _ptr(mem().isNonEmpty() ? mem().pop() : T())
    , _reset()
  {
    _ptr.init(a, as...);
  }

  Recycled(Recycled&& other) = default;
  Recycled& operator=(Recycled&& other) = default;

  ~Recycled()
  {
    if (_keep(_ptr) && alive) {
      _reset(_ptr);
      mem().push(std::move(_ptr));
    }
  }

  T const& operator* () const { return  _ptr; }
  T const* operator->() const { return &_ptr; }
  T& operator* () { return  _ptr; }
  T* operator->() { return &_ptr; }

  friend std::ostream& operator<<(std::ostream& out, Recycled const& self)
  { return out << self._ptr; }
};

template<class T, class Reset, class Keep>
bool Recycled<T, Reset, Keep>::alive = true;

};

#endif /*__Recycled__*/
