/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#include "Test/UnitTesting.hpp"
#include "Lib/Allocator.hpp"

using namespace Lib;

TEST_FUN(test_fixed_size_array_allocator_aligned)
{
  FixedSizeArrayAllocator<10> allocator;
  auto ptr = ALLOC_KNOWN2(sizeof(void*), "class", allocator);
  DEALLOC_KNOWN2(ptr, sizeof(void*), "class", allocator);
}

TEST_FUN(test_fixed_size_array_allocator_misaligned)
{
  FixedSizeArrayAllocator<10> allocator;
  auto ptr = ALLOC_KNOWN2(1, "class", allocator);
  DEALLOC_KNOWN2(ptr, 1, "class", allocator);
}

TEST_FUN(test_fixed_size_array_allocator_oversized)
{
  FixedSizeArrayAllocator<10> allocator;
  auto ptr = ALLOC_KNOWN2(1000*sizeof(void*), "class", allocator);
  DEALLOC_KNOWN2(ptr, 1000*sizeof(void*), "class", allocator);
}
