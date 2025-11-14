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

#include "Debug/Assertion.hpp"
#include <climits>

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
    IGNORE_MAYBE_UNINITIALIZED(
    bits &= ~mask;
    )
    bits |= data;
  }
};

};

/*
 * Following macros allow defining a bitfield with a specific layout.
 * Normal bitfields like
 * struct {
 *  bool foo: 1
 *  unsigned bar: 2
 * }
 * have no defined order of bits, so `foo` might end up above or below `bar`.
 *
 * This is fine (and preferred) if you just want to stuff bits into a structure somehow,
 * but if you care abut the order, you need to bit-twiddle manually.
 *
 * You might care about the order to achieve pointer tagging,
 * where the lower bits of an aligned pointer (i.e. always zero)
 * are used to encode information, masking it out when the original pointer is needed.
 */

// base case for the end of a bitfield: read as a pair (0, <empty code>)
#define END_BITFIELD 0,

/*
 * Defines a bitfield member. Only useful in the context of BITFIELD.
 * Takes five (!) parameters:
 * 1. The type of the member.
 * 2. getter name.
 * 3. setter name.
 * 4. The number of bits the field should occupy.
 * 5. The rest of the bitfield - this looks a bit weird, but it's necessary for the macro to work.
 *
 * The implementation is a bit odd - try implementing one yourself to see why!
 * Each invocation of BITFIELD_MEMBER (and END_BITFIELD) expands to a _pair_:
 * - the width in bits of the member and the rest, taken together
 * - the code required for the bitfield
 * These pairs are projected out using the CAR/CDR macros.
 */
#define BITFIELD_MEMBER(type, getter, setter, width, rest) width + CAR(rest),\
  type getter() const { return BitUtils::getBits<CAR(rest), CAR(rest) + width>(this->_content); }\
  void setter(type val) { BitUtils::setBits<CAR(rest), CAR(rest) + width>(this->_content, val); }\
  CDR(rest)

/*
 * Generate a bitfield inside a structure.
 * See Kernel/Term.hpp for example usage.
 *
 * It assumes an unsigned field `_content` of `bits` bits.
 * For each BITFIELD_MEMBER 'foo' of type T (typically unsigned/bool), it generates two methods:
 * T _foo() const;
 * void _setFoo(T val);
 */
#define BITFIELD(bits, members)\
  static_assert(bits >= CAR(members), "bitfield must have less than " #bits "bits");\
  CDR(members)

// generate code treating a whole bitfield as a pointer, masking out lower `mask` bits
#define BITFIELD_PTR_GET(type, getter, mask) \
  type *getter() const { return reinterpret_cast<type *>(BitUtils::getBits<mask, CHAR_BIT * sizeof(type *)>(this->_content)); }
#define BITFIELD_PTR_SET(type, setter, mask) \
  void setter(const type *val) { BitUtils::setBits<mask, CHAR_BIT * sizeof(type *)>(this->_content, reinterpret_cast<uint64_t>(val)); }

#endif /* __BitUtils__ */
