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

namespace Lib {

class SparseSuffixIntArray
{
public:
  SparseSuffixIntArray(const SparseSuffixIntArray&) = delete;
  SparseSuffixIntArray& operator=(const SparseSuffixIntArray&) = delete;

  inline SparseSuffixIntArray(const Stack<uint64_t>& vals) {
    size_t size = vals.size() + 1;
    void* mem = ALLOC_KNOWN(size * sizeof(uint64_t),"SparseSuffixIntArray");
    _array = array_new<uint64_t>(mem, size);
    for (unsigned i = 0; i < vals.size(); i++) {
      _array[i] = vals[i];
    }
    _array[vals.size()] = 0;
  }

  inline uint64_t operator[](unsigned i) const {
    return _array[i];
  }

  inline bool containsZero() const {
    return _array[0] & 1UL;
  }

  inline bool hasHigherValuesThan(uint64_t val) const {
    if (val < 64) {
      return (_array[0] & ~((1UL << val) - 1)) || _array[1];
    }
    size_t i = 1;
    while (_array[i] && _array[i] < val) {
      i++;
    }
    return _array[i];
  }

  inline uint64_t minValue() const {
    if (_array[0]) {
      return std::countr_zero(_array[0]);
    }
    ASS(_array[1]);
    return _array[1];
  }

  static inline SparseSuffixIntArray* singleton(uint64_t first_value) {
    Stack<uint64_t> vals;
    vals.push(0);
    if (first_value < 64) {
      vals[0] = (1UL << first_value);
    } else {
      vals.push(first_value);
    }
    return new SparseSuffixIntArray(vals);
  }

  static inline SparseSuffixIntArray* merge(const SparseSuffixIntArray* p1, const SparseSuffixIntArray* p2)
  {
    if (!p1) {
      return p2 ? copy(*p2) : nullptr;
    }
    if (!p2) {
      return copy(*p1);
    }
    auto& a1 = *p1;
    auto& a2 = *p2;
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
    return new SparseSuffixIntArray(res);
  }

  static inline SparseSuffixIntArray* copy(const SparseSuffixIntArray& a)
  {
    Stack<uint64_t> res;
    res.push(a[0]);
    size_t i = 1;
    while (a[i]) {
      res.push(a[i++]);
    }
    return new SparseSuffixIntArray(res);
  }

  static inline SparseSuffixIntArray* shiftByOne(const SparseSuffixIntArray* p)
  {
    if (!p) {
      return nullptr;
    }
    auto& a = *p;
    Stack<uint64_t> res;
    res.push(a[0] >> 1UL);
    size_t i = 1;

    while (a[i]) {
      if (a[i] == 64) {
        res[0] = res[0] | (1UL << 63);
      } else {
        res.push(a[i]-1);
      }
      i++;
    }
    if (res.size() == 1 && !res[0]) {
      return nullptr;
    }
    return new SparseSuffixIntArray(res);
  }

private:
  uint64_t* _array;
};

} // namespace Lib

#endif
