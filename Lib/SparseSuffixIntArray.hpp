/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __SparseSuffixIntArray__
#define __SparseSuffixIntArray__

#include "Allocator.hpp"
#include "Lib/Stack.hpp"

#include <cstdint>

namespace Lib {

class SparseSuffixIntArray
{
public:
  SparseSuffixIntArray(const SparseSuffixIntArray&) = delete;
  SparseSuffixIntArray& operator=(const SparseSuffixIntArray&) = delete;
  SparseSuffixIntArray(SparseSuffixIntArray&& other) {
    std::swap(_array, other._array);
  }
  SparseSuffixIntArray& operator=(SparseSuffixIntArray&& other) {
    std::swap(_array, other._array);
    return *this;
  }

  inline SparseSuffixIntArray() = default;

  ~SparseSuffixIntArray() {
    if (_array) {
      size_t size = 1;
      for (; _array[size]; size++) {}
      DEALLOC_KNOWN(_array, size * sizeof(uint64_t),"CodeTree::MatchInfo");
    }
  }

  inline bool isEmpty() const {
    return !_array;
  }

  inline bool containsZero() const {
    return _array && _array[0] & 1UL;
  }

  inline bool hasHigherValuesThan(uint64_t val) const {
    if (isEmpty()) {
      return false;
    }
    if (val < 64) {
      return (_array[0] & ~((1UL << val) - 1)) || _array[1];
    }
    size_t i = 1;
    for (; _array[i] && _array[i] < val; i++) {}
    return _array[i];
  }

  static inline SparseSuffixIntArray singleton(uint64_t first_value) {
    Stack<uint64_t> vals;
    vals.push(0);
    if (first_value < 64) {
      vals[0] = (1UL << first_value);
    } else {
      vals.push(first_value);
    }
    return SparseSuffixIntArray(vals);
  }

  static inline SparseSuffixIntArray merge(const SparseSuffixIntArray& a1, const SparseSuffixIntArray& a2) {
    if (a1.isEmpty()) {
      return copy(a2);
    }
    if (a2.isEmpty()) {
      return copy(a1);
    }
    Stack<uint64_t> res;
    res.push(a1[0] | a2[0]);
    size_t i1 = 1;
    size_t i2 = 1;

    while (a1[i1] && a2[i2]) {
      if (a1[i1] < a2[i2]) {
        res.push(a1[i1++]);
      } else if (a1[i1] > a2[i2]) {
        res.push(a2[i2++]);
      } else {
        res.push(a1[i1++]);
        i2++;
      }
    }
    while (a1[i1]) {
      res.push(a1[i1++]);
    }
    while (a2[i2]) {
      res.push(a2[i2++]);
    }
    return SparseSuffixIntArray(res);
  }

  static inline SparseSuffixIntArray copy(const SparseSuffixIntArray& a) {
    if (a.isEmpty()) {
      return SparseSuffixIntArray();
    }
    Stack<uint64_t> res;
    res.push(a[0]);
    for (size_t i = 1; a[i]; i++) {
      res.push(a[i]);
    }
    return SparseSuffixIntArray(res);
  }

  static inline SparseSuffixIntArray shiftByOne(const SparseSuffixIntArray& a) {
    if (a.isEmpty()) {
      return SparseSuffixIntArray();
    }
    Stack<uint64_t> res;
    res.push(a[0] >> 1UL);
    
    for (size_t i = 1; a[i]; i++) {
      if (a[i] == 64) {
        res[0] = res[0] | (1UL << 63);
      } else {
        res.push(a[i]-1);
      }
    }
    return SparseSuffixIntArray(res);
  }

  friend std::ostream& operator<<(std::ostream& out, const SparseSuffixIntArray& a) {
    if (a.isEmpty()) {
      return out << "<empty>";
    }
    for (size_t i = 0; a[i]; i++) {
      out << a._array[i];
      if (a[i+1]) {
        out << " ";
      }
    }
    return out;
  }

private:
  inline SparseSuffixIntArray(const Stack<uint64_t>& vals) {
    if (vals.isEmpty() || (vals.size() == 1 && !vals[0])) {
      return;
    }
    size_t size = vals.size() + 1;
    void* mem = ALLOC_KNOWN(size * sizeof(uint64_t),"SparseSuffixIntArray");
    _array = array_new<uint64_t>(mem, size);
    _array[vals.size()] = 0;
    for (size_t i = 0; i < vals.size(); i++) {
      _array[i] = vals[i];
    }
  }

  inline uint64_t operator[](unsigned i) const {
    ASS(_array);
    return _array[i];
  }

  uint64_t* _array = nullptr;
};

} // namespace Lib

#endif
