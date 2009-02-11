/**
 * @file Hash.hpp
 * Defines hash functions for various types.
 * @since 26/02/2006 Bellevue
 * @since 31/03/2006 Redmond, reimplemented usig FNV hashing
 */

#ifndef __Hash__
#define __Hash__

#include <string>

namespace Lib {

/**
 * Hash functions for various types.
 */
class Hash
{
public:

  template<typename T>
  static bool equals(T o1, T o2)
  { return o1 == o2; }

#if 0
  /** Return true if the two pointers coincide. Useful for any Set
   * class storing pointers. */
  inline static bool equals(void* p1,void* p2)
  { return p1 == p2; }
  /** Return true if the two integers coincide. Useful for any Set
   * class storing pointers. */
  inline static bool equals(int p1,int p2)
  { return p1 == p2; }
#endif

  static unsigned hash(const char* str);
  /** Hash function for strings */
  static unsigned hash(const std::string& str)
  { return hash(str.c_str()); }

  template<typename T>
  static unsigned hash(T obj)
  { return hashFNV(reinterpret_cast<const unsigned char*>(&obj),sizeof(obj)); }

#if 0
  /** Hash function for pointers */
  static unsigned hash(const void* ptr)
  { return hashFNV(reinterpret_cast<const unsigned char*>(&ptr),sizeof(ptr)); }

  /** hash function for integers */
  static unsigned hash(int i)
  { return hashFNV(reinterpret_cast<const unsigned char*>(&i),sizeof(int)); }

  /** hash function for unsigned integers */
  static unsigned hash(unsigned i)
  { return hashFNV(reinterpret_cast<const unsigned char*>(&i),sizeof(unsigned)); }

  /** hash function for floats */
  static unsigned hash(float f)
  { return hashFNV(reinterpret_cast<const unsigned char*>(&f),sizeof(float)); }

  /** hash function for doubles */
  static unsigned hash(double d)
  { return hashFNV(reinterpret_cast<const unsigned char*>(&d),sizeof(double)); }
#endif

  static unsigned hashFNV(const unsigned char*,size_t length);
  static unsigned hashFNV(const unsigned char*,size_t length,unsigned begin);
};


template<typename T>
class IdentityHash
{
public:
  static bool equals(T o1, T o2)
  { return o1 == o2; }
 static unsigned hash(T val)
 { return static_cast<unsigned>(val); }
};

struct PtrIdentityHash {
  static unsigned hash(void* ptr) {
    return static_cast<unsigned>(reinterpret_cast<size_t>(ptr));
  }
};


}

#endif
