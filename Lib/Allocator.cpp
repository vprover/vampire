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
 * @since 24/07/2023, largely obsolete
 */

#include "Allocator.hpp"
#include "Lib/Timer.hpp"

#ifndef USE_SYSTEM_ALLOCATION
Lib::SmallObjectAllocator Lib::GLOBAL_SMALL_OBJECT_ALLOCATOR;
#endif

static size_t ALLOCATED = 0;
// TODO why this initial number?
static size_t LIMIT = 300000000;

size_t Lib::getUsedMemory() { return ALLOCATED; }
size_t Lib::getMemoryLimit() { return LIMIT; }
void Lib::setMemoryLimit(size_t limit) { LIMIT = limit; }

void* protectedStdMalloc(std::size_t size) {
  Lib::TimeoutProtector tp;
  return std::malloc(size);
}

void* protectedStdRealloc(void* ptr, std::size_t new_size) {
  Lib::TimeoutProtector tp;
  return std::realloc(ptr, new_size);
}

void protectedStdFree(void* ptr) {
  Lib::TimeoutProtector tp;
  std::free(ptr);
}

// override global allocators to keep track of allocated memory, doing very little else
// TODO does not support get_new_handler/set_new_handler as we don't use it, but we could
void *operator new(size_t size) {
  Lib::TimeoutProtector tp;

  if(ALLOCATED + size > LIMIT)
    throw std::bad_alloc();

  ALLOCATED += size;
  if(void *ptr = std::malloc(size))
    return ptr;

  throw std::bad_alloc();
}

// called if we don't know the size of the deallocated object somehow,
// occurs very rarely and usually from deep in the bowels of the standard library
// TODO does cause us to slightly over-report allocated memory
void operator delete(void *ptr) noexcept {
  Lib::TimeoutProtector tp;

  std::free(ptr);
}

// normal delete, just decrements `ALLOCATED` and calls free()
void operator delete(void *ptr, size_t size) noexcept {
  Lib::TimeoutProtector tp;

  ASS_GE(ALLOCATED, size)
  ALLOCATED -= size;
  std::free(ptr);
}
