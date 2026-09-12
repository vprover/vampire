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
 * @file Hash.hpp
 * Defines hash functions for various types.
 */

#ifndef __Hash__
#define __Hash__

#include <utility>
#include <functional>
#include <type_traits>
#include <cstdint>

#include "Forwards.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/Option.hpp"

// the 32-bit FNV prime
static const unsigned FNV32_PRIME = 16777619;
// the 32-bit FNV offset basis
static const unsigned FNV32_OFFSET_BASIS = 2166136261;

namespace Lib {

struct HashUtils
{
  /**
   * Combine two hashes into one
   *
   * Code from
   * http://www.boost.org/doc/libs/1_35_0/doc/html/boost/hash_combine_id241013.html
   */
  static unsigned combine(unsigned h1, unsigned h2) { return h1 ^ (h2 + 0x9e3779b9 + (h1 << 6) + (h1 >> 2)); }

  /** auxiliary functions to be able to use combine with arbitrary arity */
  static unsigned combine(unsigned h1) { return h1; }
  static unsigned combine() { return combine(0, 1); }

  /** 
   * Combine n hashes for n > 2.
   * Since 11/08/2020
   */
  template<class... Ts> static unsigned combine(unsigned h1, unsigned h2, unsigned h3, Ts... ts) 
  { return combine(h1, combine(h2, h3, ts...)); }
};

// the identity hash
// not a great idea in general: things usually distribute badly in some way
// for example, pointers are usually aligned to e.g. multiples of 4
// however, for e.g. variables (evenly distributed close to 0) it's very effective
// also OK for secondary hashes in some cases
struct IdentityHash
{
  template<typename T>
  static bool equals(T o1, T o2)
  { return o1 == o2; }

  template<typename T>
  static unsigned hash(T val)
  { return static_cast<unsigned>(val); }
};

/**
 * FNV-1a for types where hashing the underlying bytes is sensible:
 * arithmetic and enumeration types, pointers (by address, no dereference)
 * and strings (by character).
 * Caveat: this implements the 32-bit variant of FNV-1a
 * Therefore it assumes (incorrectly) that `unsigned` is always 32 bits in size
 * Nothing terrible will happen, but it's not going to win any hashing competitions
 */
struct FnvHash
{
  template<typename T>
  static bool equals(const T &o1, const T &o2)
  { return o1 == o2; }

  /**
   * FNV-1a with initial value @b hash.
   * @since 31/03/2006
   */
  static unsigned hashBytes(
    const unsigned char *val,
    size_t size,
    unsigned hash = FNV32_OFFSET_BASIS
  ) {
    for (size_t i = 0; i < size; i++) {
      hash = (hash ^ val[i]) * FNV32_PRIME;
    }
    return hash;
  }

  /**
   * FNV-1a applied to a NUL-terminated C-style string
   */
  static unsigned hashNulTerminated(const char* val) {
    unsigned hash = FNV32_OFFSET_BASIS;
    while (*val) {
      hash = (hash ^ *val) * FNV32_PRIME;
      val++;
    }
    return hash;
  }

  template<class Iter>
  static unsigned hashIter(
      Iter iter,
      unsigned hash = FNV32_OFFSET_BASIS
      ) {
    while (iter.hasNext()) {
      hash = (hash ^ iter.next()) * FNV32_PRIME;
    }
    return hash;
  }

  // arithmetic and enumeration types are hashed as bytes
  template<typename T>
  static unsigned hash(T val, unsigned hash = FNV32_OFFSET_BASIS) {
    static_assert(
      std::is_arithmetic<T>::value || std::is_enum<T>::value,
      "FnvHash::hash(T) hashes the bytes of a scalar: supply a suitable hash for other types");
    return hashBytes(
      reinterpret_cast<const unsigned char *>(&val),
      sizeof(val),
      hash
    );
  }

  // pointers are hashed as bytes without dereference
  // if this isn't what you want, consider DerefPtrHash, or UnitHash for Units
  template<typename T>
  static unsigned hash(T* ptr, unsigned hash = FNV32_OFFSET_BASIS) {
    static_assert(
      !std::is_base_of<Kernel::Unit, T>::value,
      "Units are hashed by their number: use UnitHash or UnitNumberHash");
    return hashBytes(
      reinterpret_cast<const unsigned char*>(&ptr),
      sizeof(ptr),
      hash
    );
  }

  // strings hash the underlying C-style string
  static unsigned hash(const std::string& str)
  { return hashNulTerminated(str.c_str()); }
};

// hash a Unit (or descendant, e.g. Clause) by FNV-1a of its unique incrementing number
struct UnitHash
{
  static bool equals(const Kernel::Unit* o1, const Kernel::Unit* o2)
  { return o1 == o2; }

  static unsigned hash(const Kernel::Unit* unit)
  { return FnvHash::hash(unit ? unit->number() : 0); }
};

// hash a Unit (or descendant, e.g. Clause) by its unique incrementing number directly:
// cheap secondary hash
struct UnitNumberHash
{
  static unsigned hash(const Kernel::Unit* unit)
  { return unit ? unit->number() : 0; }
};

// hash a pointer by its address cast to unsigned: cheap secondary hash
// not great as a primary hash, since pointers are usually aligned to e.g. multiples of 4
struct PtrIdentityHash
{
  template<typename T>
  static unsigned hash(T* ptr) {
    static_assert(
      !std::is_base_of<Kernel::Unit, T>::value,
      "Units are hashed by their number: use UnitHash or UnitNumberHash");
    return static_cast<unsigned>(reinterpret_cast<std::uintptr_t>(ptr));
  }
};

// hash strings and containers by their length: cheap secondary hash
struct LengthHash
{
  template<typename T>
  static unsigned hash(const T& val)
  { return val.length(); }
};

// wrapper around std::hash
struct StlHash {
  template<class T>
  static bool equals(const T& lhs, const T& rhs) 
  { return lhs == rhs; }

  template<class T>
  static unsigned hash(const T& self)
  { return std::hash<T>{}(self); }
};

// dereference a pointer and apply InnerHash
template<class InnerHash>
struct DerefPtrHash {
  template<class T>
  static bool equals(const T* lhs, const T* rhs)
  { return InnerHash::equals(*lhs, *rhs); }

  template<class T>
  static unsigned hash(const T* self) 
  { return InnerHash::hash(*self); }
};

// a hash for Stack<T>, applying ElementHash to each item
template<class ElementHash>
struct StackHash {
  // TODO equals()?
  template<typename T>
  static unsigned hash(const Stack<T>& s, unsigned hash = FNV32_OFFSET_BASIS) {
    for (auto& x : s) {
      hash = HashUtils::combine(hash, ElementHash::hash(x));
    }
    return hash;
  }
};

// a hash for Vector<T>, applying ElementHash to each item
template<class ElementHash>
struct VectorHash {
  // TODO equals()?
  template<typename T>
  static unsigned hash(const Vector<T>& s) {
    unsigned res = FNV32_OFFSET_BASIS;
    for (unsigned i = 0; i < s.length(); i++) {
      res = HashUtils::combine(res, ElementHash::hash(s[i]));
    }
    return res;
  }
};

// combine the hashes of a tuple's elements, one functor per element
template<class... ElementHashes>
struct TupleHash
{
  template<typename... T>
  static bool equals(std::tuple<T...> const& o1, std::tuple<T...> const& o2)
  { return o1 == o2; }

  template<typename... T>
  static unsigned hash(std::tuple<T...> const& s)
  {
    static_assert(sizeof...(ElementHashes) == sizeof...(T),
      "TupleHash takes one hash functor per tuple element");
    return std::apply([](T... args) { return HashUtils::combine(ElementHashes::hash(args)...); }, s);
  }
};

// combine HashFst of the first and HashSnd of the second element of a pair
template<class HashFst, class HashSnd>
struct PairHash
{
  template<typename T, typename U>
  static bool equals(const std::pair<T,U>& o1, const std::pair<T,U>& o2)
  { return o1 == o2; }

  template<typename T, typename U>
  static unsigned hash(const std::pair<T,U>& pp) {
    return HashUtils::combine(
      HashFst::hash(pp.first),
      HashSnd::hash(pp.second)
    );
  }
};

} // namespace Lib

namespace std {

template<class T> struct hash<Lib::Stack<T>> 
{
  size_t operator()(Lib::Stack<T> const& s) const 
  { return Lib::StackHash<Lib::StlHash>::hash(s); }
};

} // std

#endif
