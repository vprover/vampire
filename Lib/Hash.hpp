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

// the 32-bit FNV prime
static const unsigned FNV32_PRIME = 16777619;
// the 32-bit FNV offset basis
static const unsigned FNV32_OFFSET_BASIS = 2166136261;

namespace Lib {

// C++17: has_unique_object_representation
template<typename T, typename=void> struct is_safely_hashable {
  static constexpr bool value = false;
};
// fundamental types are safely hashable (?)
template<typename T>
struct is_safely_hashable<T, typename std::enable_if<std::is_fundamental<T>::value>::type> {
  static constexpr bool value = true;
};
// enumerations are safely hashable (?)
template<typename T>
struct is_safely_hashable<T, typename std::enable_if<std::is_enum<T>::value>::type> {
  static constexpr bool value = true;
};

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


  template<unsigned i, class Hash, class... TsCntr>
  struct __HashTuple;
  template<unsigned i, class Hash, class T, class... TsCntr>

  struct __HashTuple<i, Hash, T, TsCntr...>
  {
    template<class... Ts>
    size_t operator()(std::tuple<Ts...> const& ts) 
    { 
      static_assert(std::is_same<decltype(std::get<i>(ts)), T const&>::value, "something wrong with tuple indices");
      return HashUtils::combine(
        Hash::hash(std::get<i>(ts)), 
        __HashTuple<i + 1, Hash, TsCntr...>{}(ts)); }
  };


  template<unsigned i, class Hash> 
  struct __HashTuple<i, Hash>
  {
    template<class... Ts>
    size_t operator()(std::tuple<Ts...> const& ts) 
    { return 0; }
  };

  template<class Hash, class... Ts> 
  static unsigned hashTuple(std::tuple<Ts...> const& ts) 
  { return __HashTuple<0, Hash, Ts...>{}(ts); }

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

template<class T>
size_t stlHash(const T& self)
{ return std::hash<T>{}(self); }

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
  static unsigned hash(const Stack<T>& s) {
    unsigned res = FNV32_OFFSET_BASIS;
    typename Stack<T>::ConstIterator it(s);
    while(it.hasNext()) {
      res = HashUtils::combine(res, ElementHash::hash(it.next()));
    }
    return res;
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

/**
 * The default hash function (FNV-1a), overloaded for various types
 * Caveat: this implements the 32-bit variant of FNV-1a
 * Therefore it assumes (incorrectly) that `unsigned` is always 32 bits in size
 * Nothing terrible will happen, but it's not going to win any hashing competitions
 */
class Hash
{
public:

  /** Return true if the two objects coincide. */
  template<typename T>
  static bool equals(T o1, T o2)
  { return o1 == o2; }

  // special-case for Units as they have a unique incrementing identifier
  static unsigned hash(Kernel::Unit* u)
  { return u ? u->number() + 1 : 0; }

  // containers hash their contents
  static unsigned hash(const vstring& str)
  { return hash(str.c_str()); }

  template<typename T>
  static unsigned hash(const Vector<T> &obj)
  { return VectorHash<Hash>::hash(obj); }

  template<typename T>
  static unsigned hash(const Stack<T> &obj)
  { return StackHash<Hash>::hash(obj); }

  // pointers are hashed as bytes without dereference
  // if this isn't what you want, consider using DerefPtrHash
  template<typename T>
  static unsigned hash(T* ptr) {
    return hash(reinterpret_cast<const unsigned char*>(&ptr),sizeof(ptr));
  }

  // types that can be safely hashed as their bytes, see is_safely_hashable
  template<typename T>
  static typename std::enable_if<is_safely_hashable<T>::value, unsigned>::type hash(T obj) {
    return hash(reinterpret_cast<const unsigned char*>(&obj),sizeof(obj));
  }

  // overload for types with a content() method to get a hashable representation of the type
  // e.g. TermList, SATLiteral
  // hashes the result of content()
  template<typename T>
  static typename std::enable_if<
    !is_safely_hashable<T>::value &&
    is_safely_hashable<typename std::result_of<decltype(&T::content)(T)>::type>::value,
    unsigned
  >::type hash(const T &obj) {
    return hash(obj.content());
  }

  // std::pair
  template<typename T, typename U>
  static unsigned hash(std::pair<T,U> obj)
  { return HashUtils::combine(hash(obj.first), hash(obj.second)); }

  /**
   * The FNV-hashing.
   * @since 31/03/2006
   */
  static unsigned hash(const char* val) {
    CALL("Hash::hash(const char *)");

    unsigned hash = FNV32_OFFSET_BASIS;
    while (*val) {
      hash = (hash ^ *val) * FNV32_PRIME;
      val++;
    }
    return hash;
  }

  /**
   * The FNV-hashing.
   * @since 31/03/2006
   */
  static unsigned hash(const unsigned char *val, size_t size)
  { return hash(val, size, FNV32_OFFSET_BASIS); }

  /**
   * The FNV-hashing where the initial value for hashing is @b hash.
   * Useful for computing hash value of anything consisting of several
   * parts: first the first part is hashed and then the hashing continues
   * on the remaining parts but using the previously computed value as
   * @b hash.
   * @since 31/03/2006
   */
  static unsigned hash(const unsigned char *val, size_t size, unsigned hash) {
    CALL("Hash::hash(const unsigned char *, size_t, unsigned)");
    ASS(size > 0);

    for (size_t i = 0; i < size; i++) {
      hash = (hash ^ val[i]) * FNV32_PRIME;
    }
    return hash;
  }
};

// template specializations for SecondaryHash
// used to fill out default template parameters for DH{Map,Set} in Forwards.hpp
// these hash functions should be cheap and not worry too much about distribution
// NB: should not be the same as the first hash!

template<typename T>
struct SecondaryHash<
  T,
  typename std::enable_if<
    std::is_fundamental<T>::value ||
    std::is_enum<T>::value
  >::type
> {
  typedef IdentityHash Type;
};

template<typename T>
struct SecondaryHash<T*> {
  struct Type {
    static unsigned hash(const T* ptr) {
      return static_cast<unsigned>(reinterpret_cast<uintptr_t>(ptr));
    }
  };
};

template<>
struct SecondaryHash<vstring> {
  struct Type {
    static unsigned hash(const vstring &str) {
      return str.length();
    }
  };
};

template<typename T, typename U>
struct SecondaryHash<std::pair<T,U> > {
  struct Type {
    static unsigned hash(const std::pair<T,U> &pp) {
      unsigned h1=SecondaryHash<T>::Type::hash(pp.first);
      unsigned h2=SecondaryHash<U>::Type::hash(pp.second);
      return HashUtils::combine(h1, h2);
    }
  };
};

} // namespace Lib

namespace std {

template<class T> struct hash<Lib::Stack<T>> 
{
  size_t operator()(Lib::Stack<T> const& s) const 
  { return Lib::StackHash<Lib::StlHash>::hash(s); }
};

}

#endif
