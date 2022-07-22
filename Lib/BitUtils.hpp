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
};

};

#endif /* __BitUtils__ */
