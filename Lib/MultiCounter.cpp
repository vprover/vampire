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
 * @file MultiCounter.cpp
 * Implements class MultiCounter that counts the number of occurrences of
 * variables.
 *
 * @since 06/01/2004, Manchester
 */

#include "Debug/Tracer.hpp"

#include "MultiCounter.hpp"
#include "Int.hpp"
#include "Allocator.hpp"
#include "Exception.hpp"

using namespace Lib;

/**
 * Expand the array to fit at least the variable w
 * @since 06/01/2004 Manchester
 * @since 16/01/2004 Manchester changed to treat bound variables
 */
void MultiCounter::expandToFit (int v)
{
  CALL("MultiCounter::expandToFit");

  // calculate the new capacity
  int newTop = max(_top*2,v+1);

  // allocate the new array
  void* mem = ALLOC_KNOWN(newTop*sizeof(int),"MultiCounter");
  int* newCounts = array_new<int>(mem, newTop);
  // copy the old values for the counter
  for (int i = 0;i < _top;i++) {
    newCounts[i] = _counts[i];
  }
  for (int k = _top;k < newTop;k++) {
    newCounts[k] = 0;
  }
  if (_counts) {
    array_delete(_counts,_top);
    DEALLOC_KNOWN(_counts,_top*sizeof(int),"MultiCounter");
  }
  _counts = newCounts;
  _top = newTop;
} // MultiCounter::expandToFit


/**
 * Destroy a MultiCounter
 * @since 06/01/2004 Manchester
 */
MultiCounter::~MultiCounter()
{
  if (_counts) {
    array_delete(_counts, _top);
    DEALLOC_KNOWN(_counts,_top*sizeof(int),"MultiCounter");
  }
} // MultiCounter::~MultiCounter
