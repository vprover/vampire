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
 * @file BitUtils.hpp
 * Defines class BitUtils.
 */


#ifndef __BitUtils__
#define __BitUtils__

#include <cstring>

#include "Lib/Portability.hpp"

namespace Lib {

class BitUtils
{
public:
  /**
   * Return the integer part of the base two logarithm of @b v
   *
   * The returned value is actually index of the most significant
   * non-zero bit.
   */
  static unsigned log2(unsigned v)
  {
    // if intrinsics are available, use them
    // compiles to e.g. lzcnt on Intel
#ifdef __GNUC__
    // compatibility with the original: 0 if v == 0 (!)
    // wastes a few cycles, but remove with great care
    if(v == 0)
      return 0;
    // compute number of leading zeros
    // then subtract number of bits plus an off-by-one
    return (sizeof(v) * CHAR_BIT - 1) - __builtin_clz(v);
#else
    // otherwise, this is simple and reasonably efficient
    unsigned bit = 0;
    while(v >>= 1) bit++;
    return bit;
#endif
  }

  /**
   * Return the number of 1-bits in @v
   */
  static unsigned oneBits(unsigned v)
  {
    // if intrinsics are available, use them
    // compiles to e.g. popcnt on Intel
#ifdef __GNUC__
    return __builtin_popcount(v);
#else
    // otherwise, this is simple and reasonably efficient
    unsigned bits = 0;
    while(v) {
      bits += v & 1;
      v >>= 1;
    }
    return bits;
#endif
  }

  // compute a 64-bit mask starting at `lower` and ending just before `upper`
  template<unsigned lower, unsigned upper>
  static constexpr uint64_t bitmask64() {
      static_assert(lower < upper, "empty range");
      static_assert(upper - lower <= 64, "too many bits");
      uint64_t mask = ~0;
      mask >>= lower;
      mask <<= lower;
      mask <<= 64 - upper;
      mask >>= 64 - upper;
      return mask;
  }

  // get the bits of `_content` between `lower` and `upper`
  template<unsigned lower, unsigned upper, class T>
  static uint64_t getBits(const T& t) {
    auto mask = bitmask64<lower, upper>();
    return (t._content & mask) >> lower;
  }

  // set the bits of `_content` between `lower` and `upper` to corresponding bits of `data`
  template<unsigned lower, unsigned upper, class T>
  static void setBits(T& t, uint64_t data) {
    auto mask = bitmask64<lower, upper>();

    // shift `data` into position
    data <<= lower;

    // mask out upper bits of `data`
    // *probably* not strictly necessary if `data` always zero at `upper` and `above`,
    // but doesn't cost us much (~2 instructions) to put this sanity check here
    data &= mask;

    // actually set the bits
    t._content &= ~mask;
    t._content |= data;
  }

};

};

#endif /* __BitUtils__ */
