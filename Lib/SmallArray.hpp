/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Lib/Coproduct.hpp"
#include <utility>
namespace Lib {

template<class T, unsigned Capacity>
class SmallArray {
  union Inner {
    T stack[Capacity];
    T* heap;
    Inner() : heap{} {}
    ~Inner() {}
  } _conts;
  unsigned _size;

  bool onHeap() const { return _size > Capacity; }

public:

  explicit SmallArray(unsigned size) 
    : _conts(Inner())
    , _size(size) 
  { 
    if (onHeap()) {
      _conts.heap = static_cast<T*>(std::malloc(size * sizeof(T)));
    }
  }

  T const* begin() const { return _size == 0 ? nullptr : onHeap() ?  _conts.heap : &_conts.stack[0]; }
  T      * begin()       { return _size == 0 ? nullptr : onHeap() ?  _conts.heap : &_conts.stack[0]; }
  T const*   end() const { return begin() + _size; }
  T      *   end()       { return begin() + _size; }

  template<class Iter>
  static SmallArray fromIterator(Iter iter) {
    ASS(iter.knowsSize())
    auto out = SmallArray(unsigned(iter.size()));
    auto ptr = out.begin();
    while (iter.hasNext()) {
      new(ptr++) T(iter.next());
    }
    return std::move(out);
  }

  T      & operator[](unsigned i)       { ASS(i < _size); return *(begin() + i); }
  T const& operator[](unsigned i) const { ASS(i < _size); return *(begin() + i); }

  unsigned size() const { return _size; }

  void swap(SmallArray& other) { 
    auto swapStackSmallerBigger = [](auto& smaller, auto& bigger) { 
      ASS(smaller.size() <= bigger.size())
      auto ssize = smaller.size();
      auto bsize = bigger.size();
      unsigned i = 0;
      for (; i < smaller.size(); i++) {
        std::swap(smaller[i], bigger[i]);
      }
      smaller._size = bsize;
      for (; i < bigger.size(); i++) {
        new(&smaller[i]) T(std::move(bigger[i]));
        bigger[i].~T();
      }
      bigger._size = ssize;
    };
    auto swapStackHeap = [](auto& onStack, auto& onHeap) { 
      auto thisHeap = onHeap._conts.heap;
      unsigned i = 0; 
      while (i < onStack.size()) {
        onHeap._conts.stack[i++] = onStack[i];
      }
      onStack._conts.heap = thisHeap;
      std::swap(onHeap._size, onStack._size);
    };
    if (onHeap() && other.onHeap()) {
      std::swap(this->_conts.heap, other._conts.heap);
      std::swap(this->_size      , other._size      );
    } else if (onHeap() && !other.onHeap()) {
      swapStackHeap(other, *this);
    } else if (!onHeap() && other.onHeap()) {
      swapStackHeap(*this, other);
    } else {
      ASS(!onHeap() && !other.onHeap())
      if (size() < other.size()) {
        swapStackSmallerBigger(*this, other);
      } else {
        swapStackSmallerBigger(other, *this);
      }
    }
  }

  SmallArray(SmallArray&& other) : SmallArray(unsigned(0))  { swap(other); }
  SmallArray& operator=(SmallArray&& other) { swap(other); return *this; }
  ~SmallArray() {
    for (auto& x : *this) {
      x.~T();
    }
    if (onHeap())
      std::free(_conts.heap);
  }

};

} // namespace Lib
