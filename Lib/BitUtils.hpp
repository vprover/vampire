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

#include <cstdint>
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

  /**
   * The functions below help set up classes containing bitfields
   * and unions in a portable way. For an example @see TermList.
   */

  // get the bits of `bits` between `lower` and `upper`
  template<unsigned lower, unsigned upper>
  static uint64_t getBits(const uint64_t& bits) {
    auto mask = bitmask64<lower, upper>();
    return (bits & mask) >> lower;
  }

  // set `bits` between `lower` and `upper` to corresponding bits of `data`
  template<unsigned lower, unsigned upper>
  static void setBits(uint64_t& bits, uint64_t data) {
    auto mask = bitmask64<lower, upper>();

    // shift `data` into position
    data <<= lower;

    // mask out upper bits of `data`
    // *probably* not strictly necessary if `data` always zero at `upper` and `above`,
    // but doesn't cost us much (~2 instructions) to put this sanity check here
    data &= mask;

    // actually set the bits
    bits &= ~mask;
    bits |= data;
  }

  #define BITFIELD64_GET_AND_SET(type, name, Name, NAME) \
    type _##name() const { return Lib::BitUtils::getBits<NAME##_BITS_START, NAME##_BITS_END>(this->_content); } \
    void _set##Name(type val) { Lib::BitUtils::setBits<NAME##_BITS_START, NAME##_BITS_END>(this->_content, val); }

  #define BITFIELD64_GET_AND_SET_PTR(type, name, Name, NAME) \
    type _##name() const { return reinterpret_cast<type>(Lib::BitUtils::getBits<NAME##_BITS_START, NAME##_BITS_END>(this->_content)); } \
    void _set##Name(type val) { Lib::BitUtils::setBits<NAME##_BITS_START, NAME##_BITS_END>(this->_content, reinterpret_cast<uint64_t>(val)); }
};

};

#endif /* __BitUtils__ */
