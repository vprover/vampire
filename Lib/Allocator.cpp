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
 * @file Allocator.cpp
 * Defines allocation procedures for all preprocessor classes.
 *
 * @since 02/12/2003, Manchester, replaces the file Memory.hpp
 * @since 10/01/2008 Manchester, reimplemented
 * @since 24/07/2023, mostly replaced by a small-object allocator
 */

#include "Allocator.hpp"
#include "Lib/Timer.hpp"

#ifndef INDIVIDUAL_ALLOCATIONS
Lib::SmallObjectAllocator Lib::GLOBAL_SMALL_OBJECT_ALLOCATOR;
#endif

static size_t ALLOCATED = 0;
// set by main very soon after launch
static size_t LIMIT = std::numeric_limits<size_t>::max();

size_t Lib::getUsedMemory() { return ALLOCATED; }
size_t Lib::getMemoryLimit() { return LIMIT; }
void Lib::setMemoryLimit(size_t limit) { LIMIT = limit; }

// override global allocators to keep track of allocated memory, doing very little else
// TODO does not support get_new_handler/set_new_handler as we don't use it, but we could
void *operator new(size_t size, std::align_val_t align_val) {
  size_t align = static_cast<size_t>(align_val);
  // standard says `size` must be an integer multiple of `align`
  ASS_EQ(size % align, 0)

  if(ALLOCATED + size > LIMIT)
    throw std::bad_alloc();
  ALLOCATED += size;
  {
    Lib::TimeoutProtector tp;
    if (static_cast<size_t>(align_val) > 1) {
      if(void *ptr = std::aligned_alloc(align, size))
        return ptr;
    } else {
      if(void *ptr = std::malloc(size))
        return ptr;
    }
  }
  throw std::bad_alloc();
}

// a version of the above operator-new without alignment information
void *operator new(size_t size) {
  if(ALLOCATED + size > LIMIT)
    throw std::bad_alloc();
  ALLOCATED += size;
  {
    Lib::TimeoutProtector tp;
    if(void *ptr = std::malloc(size))
      return ptr;
  }
  throw std::bad_alloc();
}

// normal delete, just decrements `ALLOCATED` and calls free()
void operator delete(void *ptr, size_t size) noexcept {
  ASS_GE(ALLOCATED, size)
  ALLOCATED -= size;
  Lib::TimeoutProtector tp;
  std::free(ptr);
}

// aligned-and-sized delete
// forwards to the sized delete as we don't use the alignment information
void operator delete(void *ptr, size_t size, std::align_val_t align) noexcept {
  operator delete(ptr, size);
}

// unsized (and unaligned) delete
// called if we don't know the size of the deallocated object somehow,
// occurs very rarely and usually from deep in the bowels of the standard library
// TODO does cause us to slightly over-report allocated memory
void operator delete(void *ptr) noexcept {
  Lib::TimeoutProtector tp;
  std::free(ptr);
}
