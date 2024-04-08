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
 * @file Allocator.hpp
 * Defines some memory allocation routines.
 *
 * @since 13/12/2005 Redmond, made from the Shell Allocator.
 * @since 10/01/2008 Manchester, reimplemented
 * @since 24/07/2023, mostly replaced by a small-object allocator
 */


#ifndef __Allocator__
#define __Allocator__

#include <cstddef>
#include <new>

#include "Debug/Assertion.hpp"
#include "Portability.hpp"

/*
 * uncomment the following to use Valgrind more profitably
 * if defined, we call a system allocation function for each allocation,
 * which can make e.g. finding memory leaks easier, but is slower
 */
// #define INDIVIDUAL_ALLOCATIONS

namespace Lib {

// get the amount of memory used by global operator new so far
size_t getUsedMemory();

// get the memory limit for global operator new
size_t getMemoryLimit();
// set the memory limit for global operator new
void setMemoryLimit(size_t bytes);

}

#ifdef INDIVIDUAL_ALLOCATIONS
namespace Lib {
inline void *alloc(size_t size, size_t align = alignof(std::max_align_t)) {
  return ::operator new(size, (std::max_align_t)align);
}

inline void free(void *pointer, size_t size, size_t align = alignof(std::max_align_t)) {
  ::operator delete(pointer);
}
} // namespace Lib
#define USE_GLOBAL_SMALL_OBJECT_ALLOCATOR(C)

// do some of our own allocation
#else // INDIVIDUAL_ALLOCATIONS

namespace Lib {

/*
 * A simple fixed-size allocator.
 * Allocates largish blocks of memory (`COUNT * SIZE` bytes) from the system,
 * chopping it into smaller fixed-size chunks for fast allocation/deallocation.
 * Chunks are `SIZE` bytes long, aligned to the greatest common divisor of `SIZE` and `alignof(std::max_align_t)`.
 *
 * The allocator never releases memory to the system, instead retaining it in a free list for reallocation.
 * This fits Vampire's generally-growing allocation pattern reasonably well in practice.
 */
template<size_t SIZE>
class FixedSizeAllocator {
  // number of chunks (of size `SIZE`) to allocate at a time from the system
  static const size_t COUNT = 1024;

  // to allow for a sneaky implementation hack, we cannot allocate anything smaller than sizeof(void *)
  static_assert(SIZE >= sizeof(void *), "need to store void * in the allocation to keep the free list");

  // An allocated block of memory from the system
  struct Block {
    /**
     * The block allocated from the system, that we chop up into little bits.
     * Leaked by design to clean up quickly at program exit.
     * NB: if deleted, must happen _after_ all its allocations are freed - tricky for the global allocator!
     *
     * TODO if we want to use Valgrind or similar tools, this will be reported as leaked.
     * This can be fixed by either
     * 1. Calling the system allocator if `RUNNING_ON_VALGRIND`, see https://valgrind.org/docs/manual/manual-core-adv.html
     * 2. Cleaning up after ourselves. This works but is hazardous and less fine-grained, prefer (1) if possible.
     **/
    char *bytes = nullptr;
    // the number of _bytes_ remaining in the block - when 0 we need a new block
    size_t remaining = 0;

    // hand out a single chunk
    void *alloc() {
      ASS_GE(remaining, SIZE);
      remaining -= SIZE;
      return static_cast<void *>(bytes + remaining);
    }
  };

  // the current block - old blocks are leaked
  Block current;
  /*
   * The free list.
   *
   * This uses the block itself to store the free list.
   * If `ptr` is freed, then free_list is updated to point to `ptr`,
   * while `*ptr` points to the previous value of `free_list`.
   */
  void **free_list = nullptr;

public:
  // allocate a single chunk
  void *alloc() {
    // first look if there's anything in the free list
    if(free_list) {
      void *recycled = free_list;
      free_list = static_cast<void **>(*free_list);
      return recycled;
    }

    // then check if the current block has space
    if(current.remaining)
      return current.alloc();

    // current block full, get a new one
    current.bytes = static_cast<char *>(::operator new(COUNT * SIZE));
    current.remaining = COUNT * SIZE;
    return current.alloc();
  }

  // move a chunk to the free list for reallocation
  // NB `ptr` must have been allocated from this allocator
  void free(void *ptr) {
    void **head = static_cast<void **>(ptr);
    *head = free_list;
    free_list = head;
  }
};

/*
 * An allocator tuned for small objects.
 *
 * Tries one of several `FixedSizeAllocator`s, then falls back to the system allocator.
 */
class SmallObjectAllocator {
public:
  /*
   * Allocate a piece of memory of at least `size`, aligned to at least `align`.
   *
   * Some notes on alignment.
   * Currently we just assert that `align` is no more than `alignof(std::max_align_t)`.
   * There is nothing stopping us supporting over-aligned types in principle,
   * but none of "our" objects have over-alignment requirements (yet).
   *
   * We also assume that size is a multiple of align, see
   * https://stackoverflow.com/questions/46457449/is-it-always-the-case-that-sizeoft-alignoft-for-all-object-types-t
   * Objects without this property would be quite strange, as you couldn't declare e.g. T foo[2];
   *
   * I believe, with these caveats, that returned memory is correctly aligned (MR, July 2023).
   */
  [[gnu::alloc_size(2)]] // implicit `this` argument
  [[gnu::alloc_align(3)]] // implicit `this` argument
  [[gnu::returns_nonnull]]
  [[gnu::malloc]]
  [[nodiscard]]
  inline void *alloc(size_t size, size_t align) {
    ASS_EQ(size % align, 0)
    // no support for overaligned objects yet, but there is nothing stopping it in principle
    ASS_LE(align, alignof(std::max_align_t))

    // this looks very branchy, but in practice either:
    // 1. we have a constant value for `size` and the compiler eliminates them
    // 2. somehow we don't, but out-of-order execution should make this passable
    if(size <= 1 * sizeof(void *))
      return FSA1.alloc();
    if(size <= 2 * sizeof(void *))
      return FSA2.alloc();
    if(size <= 3 * sizeof(void *))
      return FSA3.alloc();
    if(size <= 4 * sizeof(void *))
      return FSA4.alloc();
    if(size <= 6 * sizeof(void *))
      return FSA6.alloc();
    if(size <= 8 * sizeof(void *))
      return FSA8.alloc();

    // fall back to the system allocator for larger allocations
    return ::operator new(size, (std::align_val_t)align);
  }

  // deallocate a `pointer` to a memory chunk of known `size`
  // NB `pointer` must have been allocated from this allocator
  inline void free(void *pointer, size_t size, size_t align) {
    ASS_EQ(size % align, 0)

    if(!pointer)
      return;

    if(size <= 1 * sizeof(void *))
      return FSA1.free(pointer);
    if(size <= 2 * sizeof(void *))
      return FSA2.free(pointer);
    if(size <= 3 * sizeof(void *))
      return FSA3.free(pointer);
    if(size <= 4 * sizeof(void *))
      return FSA4.free(pointer);
    if(size <= 6 * sizeof(void *))
      return FSA6.free(pointer);
    if(size <= 8 * sizeof(void *))
      return FSA8.free(pointer);

    ::operator delete(pointer, size, (std::align_val_t)align);
  }

private:
  // sizes tuned somewhat based on real allocation data, but I don't claim they couldn't be better!
  // when tuning, bear in mind that the larger the gap between sizes, the more memory is wasted
  FixedSizeAllocator<1 * sizeof(void *)> FSA1;
  FixedSizeAllocator<2 * sizeof(void *)> FSA2;
  FixedSizeAllocator<3 * sizeof(void *)> FSA3;
  FixedSizeAllocator<4 * sizeof(void *)> FSA4;
  FixedSizeAllocator<6 * sizeof(void *)> FSA6;
  FixedSizeAllocator<8 * sizeof(void *)> FSA8;
};

/*
 * Global small-object allocator.
 * Falls back to the system allocator for larger allocations.
 *
 * Not always a good idea: if you know your object is (or could be) large,
 * or if you suspect it would be better to have its own allocator (spatial locality?),
 * this probably isn't the best possible allocator for you.
 */
extern SmallObjectAllocator GLOBAL_SMALL_OBJECT_ALLOCATOR;

// Allocate a piece of memory of at least `size`, which must be a multiple of `align`.
// Memory is allocated from `GLOBAL_SMALL_OBJECT_ALLOCATOR`
[[gnu::alloc_size(1)]]
[[gnu::alloc_align(2)]]
[[gnu::returns_nonnull]]
[[gnu::malloc]]
[[nodiscard]]
inline void *alloc(size_t size, size_t align) {
  return GLOBAL_SMALL_OBJECT_ALLOCATOR.alloc(size, align);
}

// Allocate a piece of memory of at least `size`, aligned to `alignof(std::max_align_t)`.
// Memory is allocated from `GLOBAL_SMALL_OBJECT_ALLOCATOR`
// Wasteful as `size` has to be rounded up, do not use in new code.
[[gnu::alloc_size(1)]]
[[gnu::returns_nonnull]]
[[gnu::malloc]]
[[nodiscard]]
inline void *alloc(size_t size) {
  const size_t align = alignof(std::max_align_t);
  // round up to the nearest multiple of align
  size = align * ((size + (align - 1)) / align);
  return alloc(size, align);
}

// Deallocate a `pointer` to a memory chunk of known `size`, which must be a multiple of `align`.
// Memory is returned to `GLOBAL_SMALL_OBJECT_ALLOCATOR`.
inline void free(void *pointer, size_t size, size_t align) {
  GLOBAL_SMALL_OBJECT_ALLOCATOR.free(pointer, size, align);
}

// Deallocate a `pointer` to a memory chunk of known `size` and aligned to `alignof(std::max_align_t)`.
// Memory is returned to `GLOBAL_SMALL_OBJECT_ALLOCATOR`.
// Wasteful as `size` has to be rounded up, do not use in new code.
inline void free(void *pointer, size_t size) {
  const size_t align = alignof(std::max_align_t);
  // round up to the nearest multiple of align
  size = align * ((size + (align - 1)) / align);

  free(pointer, size, align);
}

} // namespace Lib

// overload class-specific operator new to call the global small-object allocator
#define USE_GLOBAL_SMALL_OBJECT_ALLOCATOR(C) \
  void *operator new(size_t size) { return Lib::alloc(size, alignof(C)); }\
  void *operator new(size_t size, std::align_val_t align) { return Lib::alloc(size, (size_t)align); }\
  void operator delete(void *ptr, size_t size) { Lib::free(ptr, size, alignof(C)); } \
  void operator delete(void *ptr, size_t size, std::align_val_t align) { Lib::free(ptr, size, (size_t)align); }

#endif // INDIVIDUAL_ALLOCATIONS's else

// legacy macros, should be removed eventually
#define USE_ALLOCATOR(C) USE_GLOBAL_SMALL_OBJECT_ALLOCATOR(C)
#define ALLOC_KNOWN(size, className) Lib::alloc(size)
#define DEALLOC_KNOWN(ptr, size, className) Lib::free(ptr, size)

// TODO dubious: probably a compiler lint these days?
/**
 * Deletion of incomplete class types causes memory leaks. Using this
 * causes compile error when deleting incomplete classes.
 *
 * (see http://www.boost.org/doc/libs/1_36_0/libs/utility/checked_delete.html )
 */
template<class T> void checked_delete(T * x)
{
    // intentionally complex - simplification causes regressions
    typedef char type_must_be_complete[ sizeof(T)? 1: -1 ];
    (void) sizeof(type_must_be_complete);
    delete x;
}

// TODO dubious: is this just placement new?
// see https://stackoverflow.com/questions/8720425/array-placement-new-requires-unspecified-overhead-in-the-buffer
/**
 * Initialise an array of objects of type @b T that has length @b length
 * starting at @b placement, and return a pointer to its first element
 * (whose value is equal to @b placement). This function is required when
 * we use an allocated piece of memory an array of elements of type @b T -
 * in this case we also have to initialise every array cell by applying
 * the constructor of T.
 * @author Krystof Hoder
 * @author Andrei Voronkov (documentation)
 */
template<typename T>
T* array_new(void* placement, size_t length)
{
  ASS_NEQ(placement,0);
  ASS_G(length,0);

  T* res=static_cast<T*>(placement);
  T* p=res;
  while(length--) {
    ::new(static_cast<void*>(p++)) T();
  }
  return res;
} // array_new

// TODO maybe just inline this?
/**
 * Apply the destructor of T to each element of the array @b array of objects
 * of type @b T and that has length @b length.
 * @see array_new() for more information.
 * @author Krystof Hoder
 * @author Andrei Voronkov (documentation)
 */
template<typename T>
void array_delete(T* array, size_t length)
{
  ASS_NEQ(array,0);
  ASS_G(length,0);

  array+=length;
  while(length--) {
    (--array)->~T();
  }
}

#endif
