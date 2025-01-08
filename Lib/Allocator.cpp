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

#include <cstdio>
#include <cerrno>

#include "Allocator.hpp"

#ifndef INDIVIDUAL_ALLOCATIONS
Lib::SmallObjectAllocator Lib::GLOBAL_SMALL_OBJECT_ALLOCATOR;
#endif

#if __has_include(<sys/resource.h>)
#include <sys/resource.h>
#define HAVE_RLIMIT
#endif

const size_t MIN_MEMORY = 20971520;

void Lib::setMemoryLimit(size_t limit) {
  // if limit is less than floor, ignore it
  if(limit < MIN_MEMORY)
    return;

#ifdef HAVE_RLIMIT
  struct rlimit rlimit;
  rlimit.rlim_cur = rlimit.rlim_max = limit;
  if (setrlimit(RLIMIT_DATA, &rlimit) != 0) {
#if defined(__APPLE__) && defined(__MACH__)
    if (errno != EINVAL) // silence buggy failure on OSX
#endif
      std::perror("memory limiting failed");
  }

#else
  // TODO should we warn here?
#endif
}

long Lib::peakMemoryUsage() {
#ifdef HAVE_RLIMIT
  struct rusage usage;
    if (getrusage(RUSAGE_SELF, &usage) == 0) {
      return usage.ru_maxrss;
    }
#endif

  return 0;
}
