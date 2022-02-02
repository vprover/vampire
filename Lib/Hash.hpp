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

#include "Forwards.hpp"
#include "VString.hpp"

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

template<class ElementHash>
struct StackHash {
  template<typename T>
  static unsigned hash(const Stack<T>& s) {
    unsigned res = 2166136261u;
    typename Stack<T>::ConstIterator it(s);
    while(it.hasNext()) {
      res = HashUtils::combine(res, ElementHash::hash(it.next()));
    }
    return res;
  }
};

template<class T>
struct StlHash {
  static unsigned hash(const T& self) 
  { return std::hash<T>{}(self); }

  static bool equals(const T& lhs, const T& rhs) 
  { return lhs == rhs; }
};

template<class T, class Hash = StlHash<T>>
struct DerefPtrHash {
  static unsigned hash(const T* self) 
  { return Hash::hash(*self); }

  static bool equals(const T* lhs, const T* rhs) 
  { return Hash::equals(*lhs, *rhs); 
  }
};

template<class T>
size_t stlHash(const T& self) 
{ return std::hash<T>{}(self); }

template<class ElementHash>
struct VectorHash {
  template<typename T>
  static unsigned hash(const Vector<T>& s) {
    unsigned res = 2166136261u;
    for (unsigned i = 0; i < s.length(); i++) {
      res = HashUtils::combine(res, ElementHash::hash(s[i]));
    }
    return res;
  }
};

/**
 * Hash functions for various types.
 */
class Hash
{
public:

  /** Return true if the two objects coincide. */
  template<typename T>
  static bool equals(T o1, T o2)
  { return o1 == o2; }

  static unsigned hash(const char* str);
  /** Hash function for strings */
  static unsigned hash(const vstring& str)
  { return hash(str.c_str()); }

  static unsigned hash(Kernel::Unit* u);

  template<typename T>
  static unsigned hash(Stack<T> obj)
  { return StackHash<Hash>::hash(obj); }

  template<typename T>
  static unsigned hash(Vector<T>& obj)
  { return VectorHash<Hash>::hash(obj); }

  // Careful: using this default on structs may cause big trouble!
  // Even when all fields are properly initialized, there can remain "holes"
  // within the "sizeof" bytes containing garbage, due to alignment politics!
  template<typename T>
  static unsigned hash(T obj)
  { return hash(reinterpret_cast<const unsigned char*>(&obj),sizeof(obj)); }

  template<typename T, typename U>
  static unsigned hash(std::pair<T,U> obj)
  {
    unsigned h[2];
    h[0]=hash(obj.first);
    h[1]=hash(obj.second);
    return hash(reinterpret_cast<const unsigned char*>(h), 2*sizeof(unsigned));
  }

  template<typename T>
  static unsigned hash(T obj, unsigned begin)
  { return hash(reinterpret_cast<const unsigned char*>(&obj),sizeof(obj), begin); }

  static unsigned hash(const unsigned char*,size_t length);
  static unsigned hash(const unsigned char*,size_t length,unsigned begin);
  
  static unsigned combineHashes(unsigned h1, unsigned h2);
};

class PointerDereferencingHash {
public:
  template<typename T>
  static bool equals(T o1, T o2)
  { return (*o1) == (*o2); }

  template<typename T>
  static unsigned hash(T o1)
  { return Hash::hash(*o1); }
};

struct IdentityHash
{
  template<typename T>
  static bool equals(T o1, T o2)
  { return o1 == o2; }

  template<typename T>
  static unsigned hash(T val)
  { return static_cast<unsigned>(val); }
};

struct PtrIdentityHash
{
  static unsigned hash(const void* ptr) {
    return static_cast<unsigned>(reinterpret_cast<size_t>(ptr));
  }
};

struct PtrPairSimpleHash {
  template<typename T>
  static unsigned hash(T pp) {
    return static_cast<unsigned>(reinterpret_cast<size_t>(pp.first)^reinterpret_cast<size_t>(pp.second)^
	    (reinterpret_cast<size_t>(pp.first)>>3)^(reinterpret_cast<size_t>(pp.second)>>4));
  }
};

struct IntPairSimpleHash {
  template<typename T>
  static unsigned hash(T pp) {
    return static_cast<unsigned>(pp.first^pp.second^(pp.first<<1));
  }
};

template<class ElHash>
struct ContainerHash {
  template<typename T>
  static unsigned hash(const T& cont) {
    unsigned res = 2166136261u; //the FNV prime, don't know wheher it works well here:)
    size_t sz = cont.size();
    for(size_t i=0; i!=sz; i++) {
      res = Hash::combineHashes(res, ElHash::hash(cont[i]));
    }
    return res;
  }
};


template<typename T>
struct FirstHashTypeInfo {
  typedef Hash Type;
};

struct GeneralPairSimpleHash {
  template<typename T, typename U>
  static unsigned hash(std::pair<T,U> pp) {
    unsigned h1=FirstHashTypeInfo<T>::Type::hash(pp.first);
    unsigned h2=FirstHashTypeInfo<U>::Type::hash(pp.second);
    return static_cast<unsigned>(h1^h2^(h1<<1));
  }
};


template<typename T>
struct FirstHashTypeInfo<T*> {
  typedef PtrIdentityHash Type;
};

template<>
struct FirstHashTypeInfo<int> {
  typedef IdentityHash Type;
};
template<>
struct FirstHashTypeInfo<unsigned> {
  typedef IdentityHash Type;
};
#if ARCH_X64
template<>
struct FirstHashTypeInfo<size_t> {
  typedef IdentityHash Type;
};
#endif
template<>
struct FirstHashTypeInfo<char> {
  typedef IdentityHash Type;
};

template<>
struct FirstHashTypeInfo<std::pair<int,int> > {
  typedef IntPairSimpleHash Type;
};
template<>
struct FirstHashTypeInfo<std::pair<unsigned,unsigned> > {
  typedef IntPairSimpleHash Type;
};
template<typename T, typename U>
struct FirstHashTypeInfo<std::pair<T,U> > {
  typedef GeneralPairSimpleHash Type;
};

template<typename T>
struct FirstHashTypeInfo<Stack<T> > {
  typedef StackHash< typename FirstHashTypeInfo<T>::Type > Type;
};


} // namespace Lib

namespace std {

template<class T> struct hash<Lib::Stack<T>> 
{
  size_t operator()(Lib::Stack<T> const& s) const 
  { return Lib::StackHash<Lib::StlHash<T>>::hash(s); }
};

}

#endif
