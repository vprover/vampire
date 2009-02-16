/**
 * @file Hash.hpp
 * Defines hash functions for various types.
 */

#ifndef __Hash__
#define __Hash__

#include <string>

/**
 * Determines, whether to use FNV or lookup3 method for hashing.
 */
#define USE_LOOKUP3_HASH 1

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

#if USE_LOOKUP3_HASH

  template<typename T>
  static unsigned hash(T obj);
  static unsigned hashWords(const unsigned* data, size_t length);

#else //USE_LOOKUP3_HASH

  template<typename T>
  static unsigned hash(T obj)
  { return hash(reinterpret_cast<const unsigned char*>(&obj),sizeof(obj)); }

#endif

  static unsigned hash(const unsigned char*,size_t length);
  static unsigned hash(const unsigned char*,size_t length,unsigned begin);
};

#if USE_LOOKUP3_HASH
template<size_t LengthMod4>
struct HashByLength {
  static unsigned hash(const unsigned char* data, size_t length)
  {
    return Hash::hash(data,length);
  }
};
template<>
struct HashByLength<0> {
  static unsigned hash(const unsigned char* data, size_t length)
  {
    return Hash::hashWords(reinterpret_cast<const unsigned*>(data),length/4);
  }
};

template<typename T>
unsigned Hash::hash(T obj)
{
  return HashByLength<sizeof(obj)%4>::hash(reinterpret_cast<const unsigned char*>(&obj),sizeof(obj));
}

#endif

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
