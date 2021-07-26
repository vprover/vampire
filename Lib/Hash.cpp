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
 * @file Hash.cpp
 * Implements the class Hash for various hash functions.
 * @since 31/03/2006 Redmond
 */

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Kernel/Unit.hpp"
#include "Kernel/InferenceStore.hpp"

#include "Portability.hpp"

#include "Hash.hpp"


namespace Lib
{

using namespace std;

unsigned Hash::hash(Kernel::Unit* u)
{
  if(!u) {
    return 75663234u; //an arbitrary number as a has for a null unit pointer
  }
  return hash(u->number());
}

/**
 * The FNV-hashing.
 * @since 31/03/2006
 */
unsigned Hash::hash (const char* val)
{
  CALL("Hash::hash/2");

  unsigned hash = 2166136261u;
  while (*val) {
    hash = (hash ^ *val) * 16777619u;
    val++;
  }
  return hash;
} // Hash::hash(const char* val)

/**
 * The FNV-hashing.
 * @since 31/03/2006
 */
unsigned Hash::hash (const unsigned char* val,size_t size)
{
  CALL("Hash::hash/1");
  ASS(size > 0);

  unsigned hash = 2166136261u;
  for (int i = size-1;i >= 0;i--) {
    hash = (hash ^ val[i]) * 16777619u;
  }
  return hash;
} // Hash::hash(const char* str)

/**
 * The FNV-hashing where the initial value for hashing is @b hash.
 * Useful for computing hash value of anything consisting of several
 * parts: first the first part is hashed and then the hashing continues
 * on the remaining parts but using the previously computed value as
 * @b hash.
 * @since 31/03/2006
 */
unsigned Hash::hash (const unsigned char* val,size_t size,unsigned hash)
{
  CALL("Hash::hash/0");
  ASS(size > 0);

  for (int i = size-1;i >= 0;i--) {
    hash = (hash ^ val[i]) * 16777619u;
  }
  return hash;
} // Hash::hash(const char* str)

unsigned Hash::combineHashes(unsigned h1, unsigned h2){
  CALL("Hash::combineHashes");
  //not sure how well it behaves, just took the two FNV primes and
  //did something with them:)
  return (h1* 16777619u) ^ ( h2 + 2166136261u);
}

}
