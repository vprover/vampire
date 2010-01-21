/**
 * @file Hash.hpp
 * Defines hash functions for various types.
 */

#ifndef __Hash__
#define __Hash__

#include <string>
#include <utility>

namespace Lib {

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
  static unsigned hash(const std::string& str)
  { return hash(str.c_str()); }

  template<typename T>
  static unsigned hash(T obj)
  { return hash(reinterpret_cast<const unsigned char*>(&obj),sizeof(obj)); }

  template<typename T>
  static unsigned hash(T obj, unsigned begin)
  { return hash(reinterpret_cast<const unsigned char*>(&obj),sizeof(obj), begin); }

  static unsigned hash(const unsigned char*,size_t length);
  static unsigned hash(const unsigned char*,size_t length,unsigned begin);
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


template<typename T>
struct FirstHashTypeInfo {
  typedef Hash Type;
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

}

#endif
