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
#include "Lib/Metaiterators.hpp"

#include <utility>
namespace Lib {



template<class T, unsigned InlineCapacity>
class SmallStack {
  static constexpr unsigned MIN_STACK_SIZE = 8;
  union Inner {
    T stack[InlineCapacity];
    T* heap;
    Inner() : heap{} {}
    ~Inner() {}
  } _conts;
  unsigned _size;
  unsigned _capacity;

  bool onHeap() const { return _capacity > InlineCapacity; }

  static constexpr unsigned initialCapacity(unsigned c) {
    unsigned out = 1;
    while (out < c + 1) {
      out <<= 1;
    }
    return out;
  }

  void growTo(unsigned newCapa) {
    T* newHeap = static_cast<T*>(std::malloc(newCapa * sizeof(T)));
    ASS(_capacity >= InlineCapacity)

    for (auto i : range(0, size())) {
      new(&newHeap[i]) T(std::move(rawGet(i)));
      rawGet(i).~T();
    }

    if (onHeap()) {
      std::free(_conts.heap);
    }

    _conts.heap = newHeap;
    _capacity = newCapa;
  }


  void grow() {
    growTo(_capacity == InlineCapacity 
        ? initialCapacity(InlineCapacity)
        : _capacity * 2);
  }

  T      & rawGet(unsigned i)       { return *(begin() + i); }
  T const& rawGet(unsigned i) const { return *(begin() + i); }

public:

  explicit SmallStack() 
    : _conts(Inner())
    , _size(0) 
    , _capacity(InlineCapacity)
  { ASS(!onHeap()) }



  T const* begin() const { return _capacity == 0 ? nullptr : onHeap() ?  _conts.heap : &_conts.stack[0]; }
  T      * begin()       { return _capacity == 0 ? nullptr : onHeap() ?  _conts.heap : &_conts.stack[0]; }
  T const*   end() const { return begin() + _size; }
  T      *   end()       { return begin() + _size; }

  template<class Iter>
  static SmallStack fromIterator(Iter iter) {
    ASS(iter.knowsSize())
    auto out = SmallStack();
    out.growToFit(iter.size());
    auto ptr = out.begin();
    while (iter.hasNext()) {
      new(ptr++) T(iter.next());
    }
    return std::move(out);
  }

  T      & operator[](unsigned i)       { ASS(i < _size); return *(begin() + i); }
  T const& operator[](unsigned i) const { ASS(i < _size); return *(begin() + i); }

  template<class Less = std::less<T>>
  void sort(Less less = std::less<T>{})
  { std::sort(begin(), end(), std::move(less)); }

  unsigned size() const { return _size; }

  void swap(SmallStack& other) { 
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
      for (; i < onStack.size(); i++) {
        onHeap._conts.stack[i] = onStack[i];
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

  explicit SmallStack(SmallStack const& other)
    : SmallStack(other.size())
  {
    auto ptr = begin();
    for (unsigned i = 0; i < other.size(); i++) {
      new(&ptr[i]) T(other[i]);
    }
  }
  SmallStack(SmallStack&& other) : SmallStack(unsigned(0))  { swap(other); }
  SmallStack& operator=(SmallStack&& other) { swap(other); return *this; }
  ~SmallStack() {
    for (auto& x : *this) {
      x.~T();
    }
    if (onHeap())
      std::free(_conts.heap);
  }

  void growToFit(unsigned t) { growTo(initialCapacity(t)); }

  template<class It>
  void loadFromIterator(It it) {
    if (it.knowsSize() && it.size() > size()) {
      growToFit(it.size());
    }
    while(it.hasNext()) {
      push(it.next());
    }
  }

  void push(T elem) {
    if (_capacity == size()) { grow(); }
    ASS(_capacity > size())
    new(&rawGet(_size)) T(std::move(elem));
    _size++;
  }
  

  T pop() {
    _size--;
    auto out = std::move(rawGet(_size)); 
    rawGet(_size).~T();
    return out;
  }

  void pop(unsigned x) {
    for (auto i : range(0,x)) { (void)i; pop();}
  }

  bool isNonEmpty() const { return size() > 0; }

  bool keepRecycled() const { return _capacity > InlineCapacity; }
  void reset() { while (size() > 0) { pop(); } }
  

  auto iter() const { return arrayIter(*this); }
  auto iter()       { return arrayIter(*this); }

  using Self = SmallStack;
  auto asTuple() const { return std::make_tuple(size(), iterContOps(iter())); }
  IMPL_COMPARISONS_FROM_TUPLE(Self);
  IMPL_HASH_FROM_TUPLE(Self);
  friend std::ostream& operator<<(std::ostream& out, SmallStack const& self)
  { return out << "[" << self.iter().output(", ") << "]"; }
};

} // namespace Lib
