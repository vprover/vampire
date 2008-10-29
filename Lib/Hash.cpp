/**
 * @file Hash.cpp
 * Implements the class Hash for various hash functions.
 * @since 31/03/2006 Redmond
 */

#include "../Debug/Assertion.hpp"
#include "../Debug/Tracer.hpp"

#include "Hash.hpp"

using namespace std;
using namespace Lib;

/**
 * The FNV-hashing.
 * @since 31/03/2006
 */
unsigned Hash::hashFNV (const unsigned char* val,size_t size)
{
  CALL("Hash::hashFNV/1");
  ASS(size > 0);

  unsigned hash = 2166136261u;
  for (int i = size-1;i >= 0;i--) {
    hash = (hash ^ val[i]) * 16777619u;
  }
  return hash;
} // Hash::hashFNV(const char* str)

/**
 * The FNV-hashing where the initial value for hashing is @b hash.
 * Useful for computing hash value of anything consisting of several
 * parts: first the first part is hashed and then the hashing continues
 * on the remaining parts but using the previously computed value as
 * @b hash.
 * @since 31/03/2006
 */
unsigned Hash::hashFNV (const unsigned char* val,size_t size,unsigned hash)
{
  CALL("Hash::hashFNV/0");
  ASS(size > 0);

  for (int i = size-1;i >= 0;i--) {
    hash = (hash ^ val[i]) * 16777619u;
  }
  return hash;
} // Hash::hashFNV(const char* str)

/**
 * The FNV-hashing.
 * @since 31/03/2006
 */
unsigned Hash::hash (const char* val)
{
  CALL("Hash::hashFNV/2");

  unsigned hash = 2166136261u;
  while (*val) {
    hash = (hash ^ *val) * 16777619u;
    val++;
  }
  return hash;
} // Hash::hash(const char* val)

