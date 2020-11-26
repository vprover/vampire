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
 * @file IntegerSet.cpp
 * Implements class IntegerSet for sets of nonnegative integers.
 *
 * @since 16/06/2005 Manchester
 */

#include <new>

#include "Debug/Assertion.hpp"
#include "Allocator.hpp"
#include "IntegerSet.hpp"

using namespace Lib;

/**
 * True if n is a member of the set.
 * @since 16/06/2005 Manchester
 */
bool IntegerSet::member (int n) const
{
  ASS(n >= 0);
  int index = n/BITS_PER_INT;
  if (index >= _words) {
    return false;
  }
  return _set[index] & (1u << (n % BITS_PER_INT));
} // IntegerSet::member


/**
 * Delete n from the set.
 * @since 16/06/2005 Manchester
 */
void IntegerSet::remove (int n)
{
  ASS(n >= 0);

  int index = n/BITS_PER_INT;
  if (index >= _words) {
    return;
  }
  _set[index] &= ~(1u << (n % BITS_PER_INT));
} // IntegerSet::remove


/**
 * Insert n into the set.
 * @since 16/06/2005 Manchester
 */
void IntegerSet::insert (int n)
{
  ASS(n >= 0);

  int index = n/BITS_PER_INT;
  if (index >= _words) { // needs expansion
    int words = _words*2;
    if (words < index+1) {
      words = index+1;
    }
    void* mem = ALLOC_KNOWN(sizeof(unsigned)*words,"IntegerSet");
    unsigned int* set = array_new<unsigned>(mem, words);
    for (int i = _words-1;i >= 0;i--) {
      set[i] = _set[i];
    }
    for (int j = _words;j < words;j++) {
      set[j] = 0u;
    }
    if (_set) {
      array_delete(_set, _words);
      DEALLOC_KNOWN(_set,sizeof(unsigned)*_words,"IntegerSet");
    }
    _set = set;
    _words = words;
  }
  _set[index] |= (1u << (n % BITS_PER_INT));
} // IntegerSet::remove

/**
 * Deallocate the array.
 * @since 13/01/2008 Manchester
 */
IntegerSet::~IntegerSet()
{
  if (_set) {
    array_delete(_set, _words);
    DEALLOC_KNOWN(_set,sizeof(unsigned)*_words,"IntegerSet");
  }
} // IntegerSet::~IntegerSet
