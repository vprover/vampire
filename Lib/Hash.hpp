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

#include "Forwards.hpp"
#include "VString.hpp"
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

template<class InnerHash> 
struct TupleHash {

  template <std::size_t Index, typename... Ts>
  static inline typename std::enable_if<Index == sizeof...(Ts), unsigned>::type
  tuple_hash_impl(const std::tuple<Ts...> &t) { return 0; }

  template <std::size_t Index, typename... Ts>
  static inline typename std::enable_if<Index < sizeof...(Ts), unsigned>::type
  tuple_hash_impl(const std::tuple<Ts...> &t) 
  { return Lib::HashUtils::combine(tuple_hash_impl<Index + 1>(t), InnerHash::hash(std::get<Index>(t))); }


  template<typename... T>
  static unsigned hash(tuple<T...> const& s) {
    //C++17: repace with std::apply:
    // return std::apply(s, [](auto... args) { return HashUtils::combine(hash(args)...); });
    return tuple_hash_impl<0>(s);
  }
};

/**
 * The default hash function (FNV-1a), overloaded for various types
 * Caveat: this implements the 32-bit variant of FNV-1a
 * Therefore it assumes (incorrectly) that `unsigned` is always 32 bits in size
 * Nothing terrible will happen, but it's not going to win any hashing competitions
 */
class DefaultHash
{
public:
  // dispatch to operator==(const T&, const T&)
  template<typename T>
  static bool equals(const T &o1, const T &o2)
  { return o1 == o2; }

  // if T has a unsigned defaultHash() method, invoke that
  template<typename T>
  static typename std::enable_if<
    std::is_same<
      //C++17: repace with std::invoke_result
      typename std::result_of<decltype(&T::defaultHash)(T)>::type,
      unsigned
    >::value,
    unsigned
  >::type hash(const T &ref) {
    return ref.defaultHash();
  }

  // special-case for Units (and their descendants) as they have a unique incrementing identifier  
  template<typename T>
  static typename std::enable_if<
    std::is_base_of<Kernel::Unit, T>::value,
    unsigned
  >::type hash(T *unit) 
  { return hash(unit ? unit->number() : 0); }

  // other pointers are hashed as bytes without dereference
  // if this isn't what you want, consider using DerefPtrHash
  template<typename T>
  static typename std::enable_if<
    !std::is_base_of<Kernel::Unit, T>::value,
    unsigned
  >::type hash(T* ptr, unsigned hash = FNV32_OFFSET_BASIS) {
    return hashBytes(
      reinterpret_cast<const unsigned char*>(&ptr),
      sizeof(ptr),
      hash
    );
  }

  // arithmetic and enumeration types are hashed as bytes
  template<typename T>
  static typename std::enable_if<
    std::is_arithmetic<T>::value || std::is_enum<T>::value,
    unsigned
  >::type hash(T val, unsigned hash = FNV32_OFFSET_BASIS) {
    return hashBytes(
      reinterpret_cast<const unsigned char *>(&val),
      sizeof(val),
      hash
    );
  }

  // vstrings hash the underlying C-style string
  static unsigned hash(const vstring& str)
  { return DefaultHash::hashNulTerminated(str.c_str()); }

  // dispatch to VectorHash<DefaultHash>
  template<typename T>
  static unsigned hash(const Vector<T> &obj)
  { return VectorHash<DefaultHash>::hash(obj); }

  // dispatch to StackHash<DefaultHash>
  template<typename T>
  static unsigned hash(const Stack<T> &obj, unsigned hash = FNV32_OFFSET_BASIS)
  { return StackHash<DefaultHash>::hash(obj, hash); }

  // std::pair combines default hashes of first and second
  template<typename T, typename U>
  static unsigned hash(const std::pair<T,U> &obj) {
    return HashUtils::combine(
      DefaultHash::hash(obj.first),
      DefaultHash::hash(obj.second)
    );
  }


  /**
   * FNV-1a with initial value @b hash.
   * @since 31/03/2006
   */
  static unsigned hashBytes(
    const unsigned char *val,
    size_t size,
    unsigned hash = FNV32_OFFSET_BASIS
  ) {
    CALL("DefaultHash::hashBytes");
    for (size_t i = 0; i < size; i++) {
      hash = (hash ^ val[i]) * FNV32_PRIME;
    }
    return hash;
  }

  /**
   * FNV-1a applied to a NUL-terminated C-style string
   */
  static unsigned hashNulTerminated(const char* val) {
    CALL("Hash::hash(const char *)");

    unsigned hash = FNV32_OFFSET_BASIS;
    while (*val) {
      hash = (hash ^ *val) * FNV32_PRIME;
      val++;
    }
    return hash;
  }



  template<typename... T>
  static unsigned hash(tuple<T...> const& s) 
  { return TupleHash<DefaultHash>::hash(s); }

  template<typename T>
  static unsigned hash(Lib::Option<T> const& o) 
  { return o.isSome() ? o->defaultHash()
                      : Lib::DefaultHash::hash(typeid(T).hash_code()); }
};

// a default secondary hash for doubly-hashed containers
// these hash functions should be cheap and not worry too much about distribution
// NB: should not be the same as the first hash!
class DefaultHash2 {
public:
  // if T has a unsigned defaultHash2() method, invoke that
  template<typename T>
  static typename std::enable_if<
    std::is_same<
      //C++17: repace with std::invoke_result
      typename std::result_of<decltype(&T::defaultHash2)(T)>::type,
      unsigned
    >::value,
    unsigned
  >::type hash(const T &ref) {
    return ref.defaultHash2();
  }

  // special-case for Units (and their descendants) as they have a unique incrementing identifier  
  template<typename T>
  static typename std::enable_if<
    std::is_base_of<Kernel::Unit, T>::value,
    unsigned
  >::type hash(T *unit) 
  { return unit ? unit->number() : 0; }

  // other pointer types are cast to unsigned
  template<typename T>
  static typename std::enable_if<
    !std::is_base_of<Kernel::Unit, T>::value,
    unsigned
  >::type hash(T* ptr) {
    return static_cast<unsigned>(reinterpret_cast<uintptr_t>(ptr));
  }

  // arithmetic and enumeration types are cast to unsigned
  template<typename T> static typename std::enable_if<
    std::is_fundamental<T>::value || std::is_enum<T>::value,
    unsigned
  >::type hash(T val) {
    return static_cast<unsigned>(val);
  }

  // vstrings use their length
  static unsigned hash(const vstring &str) {
    return str.length();
  }

  // containers use their length
  template<typename T> static unsigned hash(const Stack<T> &stack) {
    return stack.length();
  }

  // containers use their length
  template<typename T> static unsigned hash(const Vector<T> &vector) {
    return vector.length();
  }

  // std::pair combines default secondary hashes of first and second
  template<typename T, typename U>
  static unsigned hash(const std::pair<T, U> &pp) {
    return HashUtils::combine(
      DefaultHash2::hash(pp.first),
      DefaultHash2::hash(pp.second)
    );
  }
  template<typename... T>
  static unsigned hash(tuple<T...> const& s) 
  { return TupleHash<DefaultHash2>::hash(s); }

  template<typename T>
  static unsigned hash(Lib::Option<T> const& o) 
  { return o.isSome() ? o->defaultHash2()
                      : Lib::DefaultHash2::hash(typeid(T).hash_code()); }
};

} // namespace Lib

namespace std {

template<class T> struct hash<Lib::Stack<T>> 
{
  size_t operator()(Lib::Stack<T> const& s) const 
  { return Lib::StackHash<Lib::StlHash>::hash(s); }
};


template<class... T> struct hash<tuple<T...>> 
{
  size_t operator()(tuple<T...> const& s) const 
  { return Lib::DefaultHash::hash(s); }
};
} // std

#endif
