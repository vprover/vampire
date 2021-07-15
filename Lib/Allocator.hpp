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
 * Defines the class Allocator plus the global allocator for Vampire.
 *
 * @since 13/12/2005 Redmond, made from the Shell Allocator.
 * @since 10/01/2008 Manchester, reimplemented
 */


#ifndef __Allocator__
#define __Allocator__

#include <cstddef>

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Portability.hpp"

#if VDEBUG
#include <string>
#endif

#define MAKE_CALLS 0

#define USE_PRECISE_CLASS_NAMES 0

/** Page size in bytes */
#define VPAGE_SIZE 131000
/** maximal size of allocated multi-page (in pages) */
//#define MAX_PAGES 4096
//#define MAX_PAGES 8192
#define MAX_PAGES 40000
/** Any memory piece of this or larger size will be allocated as a page
 *  or contiguous sequence of pages */
#define REQUIRES_PAGE (VPAGE_SIZE/2)
/** Maximal allowed number of allocators */
#define MAX_ALLOCATORS 256

/** The largest piece of memory that can be allocated at once */
#define MAXIMAL_ALLOCATION (static_cast<unsigned long long>(VPAGE_SIZE)*MAX_PAGES)

//this macro is undefined at the end of the file
// alloc_size follows C notation, for a C++ method, argument 1 is the pointer to this, so
// the actual allocation size lies in argument 2
#if defined(__GNUC__) && !defined(__ICC) && (__GNUC__ > 4 || __GNUC__ == 4 && __GNUC_MINOR__ > 2)
# define ALLOC_SIZE_ATTR __attribute__((malloc, alloc_size(2)))
#else
# define ALLOC_SIZE_ATTR
#endif

namespace Lib {

class Allocator {
public:
  // Allocator is the only class which we don't allocate using Allocator ;)
  void* operator new (size_t s);
  void operator delete (void* obj);

  Allocator();
  ~Allocator();
  
  /** Return the amount of used memory */
  static size_t getUsedMemory()
  {
    CALLC("Allocator::getUsedMemory",MAKE_CALLS);
    return _usedMemory;
  }
  /** Return the global memory limit (in bytes) */
  static size_t getMemoryLimit()
  {
    CALLC("Allocator::getMemoryLimit",MAKE_CALLS);
    return _memoryLimit;
  }
  /** Set the global memory limit (in bytes) */
  static void setMemoryLimit(size_t size)
  {
    CALLC("Allocator::setMemoryLimit",MAKE_CALLS);
    _memoryLimit = size;
    _tolerated = size + (size/10);
  }
  /** The current allocator
   * - through which allocations by the here defined macros are channelled */
  static Allocator* current;

#if VDEBUG
  void* allocateKnown(size_t size,const char* className) ALLOC_SIZE_ATTR;
  void deallocateKnown(void* obj,size_t size,const char* className);
  void* allocateUnknown(size_t size,const char* className) ALLOC_SIZE_ATTR;
  void* reallocateUnknown(void* obj, size_t newsize,const char* className);
  void deallocateUnknown(void* obj,const char* className);
  static void addressStatus(const void* address);
  static void reportUsageByClasses();
#else
  void* allocateKnown(size_t size) ALLOC_SIZE_ATTR;
  void deallocateKnown(void* obj,size_t size);
  void* allocateUnknown(size_t size) ALLOC_SIZE_ATTR;
  void* reallocateUnknown(void* obj, size_t newsize);
  void deallocateUnknown(void* obj);
#endif

  class Initialiser {
  public:
    /** Initialise the static allocator's methods */
    Initialiser()
    {
      CALLC("Allocator::Initialiser::Initialiser",MAKE_CALLS);

      if (Allocator::_initialised++ == 0) {
	Allocator::initialise();
      }
    } // Initialiser::Initialiser

    ~Initialiser()
    {
      CALLC("Allocator::Initialiser::~Initialiser",MAKE_CALLS);
      if (--Allocator::_initialised == 0) {
	Allocator::cleanup();
      }
    }
  }; // class Allocator::Initialiser

  static Allocator* newAllocator();

private:
  char* allocatePiece(size_t size);
  static void initialise();
  static void cleanup();
  /** Array of Allocators. It is assumed that a small number of Allocators is
   *  available at any given time and Allocator deletions are rare since
   *  a deletion involves a linear lookup in the array and the
   *  size of the array is small (currently, no during runtime deletion supported).
   */
  static Allocator* _all[MAX_ALLOCATORS];
  /** Total number of allocators currently available */
  static int _total;
  /** > 0 if the global page manager has been initialised */
  static int _initialised;

  /**
   * A piece of memory whose size is known by procedures de-allocating
   * this piece. Since the size is known in advance, no bookkeeping of
   * the size is required.
   *
   * Note: the code of Allocator uses sizeof(Known) as a canonical
   * way of describing the size of a general pointer on the current
   * architecture.
   * 
   * This pieces of memory are kept in a free list.
   * @since 10/01/2007 Manchester
   */
  struct Known {
    /** Pointer to the next available piece. Used when kept in a free list. */
    Known* next;
  }; // class Known

  /**
   * A piece of memory whose size is unknown by procedures de-allocating
   * this piece. Since the size is unknown, storing the size is required.
   *
   * This pieces of memory are kept in a list
   * @since 10/01/2007 Manchester
   */
  struct Unknown {
    /** Size, used both when the piece is allocated and when it is kept
     *  in the free list. It is the size of the piece, since the size of
     *  the datastructure using the piece may actually be smaller */
    size_t size;
    /** Pointer to the next available piece. Used when kept in
     *  the list. */
    Unknown* next;
  }; // class Unknown

  static size_t unknownsSize(void* obj) {
    ASS_LE(sizeof(size_t), sizeof(Known)); // because the code all around jumps back by sizeof(Known), but then reads/writes into size_t

    char* mem = reinterpret_cast<char*>(obj) - sizeof(Known);
    Unknown* unknown = reinterpret_cast<Unknown*>(mem);
    return unknown->size - sizeof(Known);
  }

#if VDEBUG
public:
  /** A helper struct used for implementing the BYPASSING_ALLOCATOR macro. */
  struct EnableBypassChecking {
    unsigned _save;
    EnableBypassChecking() { _save = _tolerantZone; _tolerantZone = 0; }
    ~EnableBypassChecking() { _tolerantZone = _save; }
  };

  /** A helper struct used for implementing the BYPASSING_ALLOCATOR macro. */
  struct DisableBypassChecking {
    DisableBypassChecking() { _tolerantZone = 1; }
  };

  /** A helper struct used for implementing the BYPASSING_ALLOCATOR macro. */  
  struct AllowBypassing {
    AllowBypassing() { _tolerantZone++; }
    ~AllowBypassing() { _tolerantZone--; }
  };
  
  /** Descriptor stores information about allocated pieces of memory */
  struct Descriptor
  {
    // Allocator (and its Descriptor) are the only classes which we don't allocate using Allocator
    void* operator new[] (size_t s);
    void operator delete[] (void* obj);

    /** address of a piece of memory */
    const void* address;
    /** class to which it belongs */
    const char* cls;
    /** time when it allocated/deallocated */
    unsigned timestamp;
    /** size in bytes, 0 is unused */
    unsigned size;
    /** true if allocated */
    unsigned allocated : 1;
    /** true if allocated as a known-size object */
    unsigned known : 1;
    /** true if it is a page allocated to store other objects */
    unsigned page : 1;
    Descriptor();

    friend std::ostream& operator<<(std::ostream& out, const Descriptor& d);

    static unsigned hash (const void* addr);
    static Descriptor* find(const void* addr);
    /** map from addresses to memory descriptors */
    static Descriptor* map;
    /** timestamp for (de)allocations */
    static unsigned globalTimestamp;
    /** number of entries in the map of memory descriptors */
    static size_t noOfEntries;
    /** number of entries in the map of memory descriptors */
    static size_t maxEntries;
    /** pointer to after the last descriptor in the table */
    static Descriptor* afterLast;
    /** capacity of the map */
    static size_t capacity;
  };
#endif

private:
  /**
   * A piece of memory whose size is multiple of VPAGE_SIZE. Each page
   * is used in one of the following ways:
   * <ol>
   *  <li>to store a collection of Knowns</li>
   *  <li>to store a collection of Uknowns</li>
   *  <li>to store a single object of size greater than or equal to
   *      REQUIRES_PAGE</li>
   * </ol>
   * @warning @b size should go just before @b content since Vampire
   *             must be able to know the size of both Page and Unknown
   *             before knowing the type (that is, Page or Unknown)
   * @since 10/01/2007 Manchester
   */
  struct Page {
    /** The next page, if any */
    Page* next;
    /** The previous page, if any */
    Page* previous;
    /**  Size of this page, multiple of VPAGE_SIZE */
    size_t size;    
    /** The page content starts here */
    void* content[1];
  }; // class Page

  Page* allocatePages(size_t size);
  void deallocatePages(Page* page);

  /** The global memory limit */
  static size_t _memoryLimit;
  /** 10% over the memory limit. When reached, memory de-fragmentation
   *  should occur */
  static size_t _tolerated;

  // structures used inside the allocator start here
  /** The free list.
   * At index @b i there are a linked list of Knowns of size (i+1)*sizeof(Known)
   * Note that, essentially, sizeof(Known) = sizeof(void*).
   */
  Known* _freeList[REQUIRES_PAGE/4];
  /** All pages allocated by this allocator and not returned to 
   *  the global manager via deallocatePages (doubly linked).  */
  Page* _myPages;
#if ! USE_SYSTEM_ALLOCATION
  /** Number of bytes available on the reserve page */
  size_t _reserveBytesAvailable;
  /** next available known */
  char* _nextAvailableReserve;
#endif // ! USE_SYSTEM_ALLOCATION

  /** Total memory allocated by pages */
  static size_t _usedMemory;
  /** Page allocator array, a.k.a. "the global manager".
   * Each entry is a (singly linked) list */
  static Page* _pages[MAX_PAGES];

  friend class Initialiser;
  
#if VDEBUG  
  /*
   * A tool for marking pieces of code which are allowed to bypass Allocator.
   * See also Allocator::AllowBypassing and the BYPASSING_ALLOCATOR macro.
   */
  static unsigned _tolerantZone;  
  friend void* ::operator new(size_t);
  friend void* ::operator new[](size_t);
  friend void ::operator delete(void*) noexcept;
  friend void ::operator delete[](void*) noexcept;
#endif
}; // class Allocator

/** An initialiser to be included in every compilation unit to ensure
 *  that the memory has been initialised properly.
 */
static Allocator::Initialiser _____;

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
  CALLC("array_new",MAKE_CALLS);
  ASS_NEQ(placement,0);
  ASS_G(length,0);

  T* res=static_cast<T*>(placement);
  T* p=res;
  while(length--) {
    ::new(static_cast<void*>(p++)) T();
  }
  return res;
} // array_new

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
  CALLC("array_delete",MAKE_CALLS);
  ASS_NEQ(array,0);
  ASS_G(length,0);

  array+=length;
  while(length--) {
    (--array)->~T();
  }
}

#define DECLARE_PLACEMENT_NEW                                           \
  void* operator new (size_t, void* buffer) { return buffer; } 		\
  void operator delete (void*, void*) {}


#if VDEBUG

std::ostream& operator<<(std::ostream& out, const Allocator::Descriptor& d);

#define USE_ALLOCATOR_UNK                                            \
  void* operator new (size_t sz)                                       \
  { return Lib::Allocator::current->allocateUnknown(sz,className()); } \
  void operator delete (void* obj)                                  \
  { if (obj) Lib::Allocator::current->deallocateUnknown(obj,className()); }
#define USE_ALLOCATOR(C)                                            \
  void* operator new (size_t sz)                                       \
  { ASS_EQ(sz,sizeof(C)); return Lib::Allocator::current->allocateKnown(sizeof(C),className()); } \
  void operator delete (void* obj)                                  \
  { if (obj) Lib::Allocator::current->deallocateKnown(obj,sizeof(C),className()); }
#define USE_ALLOCATOR_ARRAY \
  void* operator new[] (size_t sz)                                       \
  { return Lib::Allocator::current->allocateUnknown(sz,className()); } \
  void operator delete[] (void* obj)                                  \
  { if (obj) Lib::Allocator::current->deallocateUnknown(obj,className()); }


#if USE_PRECISE_CLASS_NAMES
#  if defined(__GNUC__)

     std::string ___prettyFunToClassName(std::string str);

#    define CLASS_NAME(C) \
       static const char* className () { \
	  static std::string res = ___prettyFunToClassName(std::string(__PRETTY_FUNCTION__)); return res.c_str(); }
#  else
#    define CLASS_NAME(C) \
       static const char* className () { return typeid(C).name(); }
#  endif
#else
#  define CLASS_NAME(C) \
    static const char* className () { return #C; }
#endif

#define ALLOC_KNOWN(size,className)				\
  (Lib::Allocator::current->allocateKnown(size,className))
#define ALLOC_UNKNOWN(size,className)				\
  (Lib::Allocator::current->allocateUnknown(size,className))
#define DEALLOC_KNOWN(obj,size,className)		        \
  (Lib::Allocator::current->deallocateKnown(obj,size,className))
#define REALLOC_UNKNOWN(obj,newsize,className)                    \
    (Lib::Allocator::current->reallocateUnknown(obj,newsize,className))
#define DEALLOC_UNKNOWN(obj,className)		                \
  (Lib::Allocator::current->deallocateUnknown(obj,className))
         
#define BYPASSING_ALLOCATOR_(SEED) Allocator::AllowBypassing _tmpBypass_##SEED;
#define BYPASSING_ALLOCATOR BYPASSING_ALLOCATOR_(__LINE__)

#define START_CHECKING_FOR_BYPASSES(SEED) Allocator::EnableBypassChecking _tmpBypass_##SEED;
#define START_CHECKING_FOR_ALLOCATOR_BYPASSES START_CHECKING_FOR_BYPASSES(__LINE__)

#define STOP_CHECKING_FOR_BYPASSES(SEED) Allocator::DisableBypassChecking _tmpBypass_##SEED;
#define STOP_CHECKING_FOR_ALLOCATOR_BYPASSES STOP_CHECKING_FOR_BYPASSES(__LINE__)

#else

#define CLASS_NAME(name)
#define ALLOC_KNOWN(size,className)				\
  (Lib::Allocator::current->allocateKnown(size))
#define DEALLOC_KNOWN(obj,size,className)		        \
  (Lib::Allocator::current->deallocateKnown(obj,size))
#define USE_ALLOCATOR_UNK                                            \
  inline void* operator new (size_t sz)                                       \
  { return Lib::Allocator::current->allocateUnknown(sz); } \
  inline void operator delete (void* obj)                                  \
  { if (obj) Lib::Allocator::current->deallocateUnknown(obj); }
#define USE_ALLOCATOR(C)                                        \
  inline void* operator new (size_t)                                   \
    { return Lib::Allocator::current->allocateKnown(sizeof(C)); }\
  inline void operator delete (void* obj)                               \
   { if (obj) Lib::Allocator::current->deallocateKnown(obj,sizeof(C)); }
#define USE_ALLOCATOR_ARRAY                                            \
  inline void* operator new[] (size_t sz)                                       \
  { return Lib::Allocator::current->allocateUnknown(sz); } \
  inline void operator delete[] (void* obj)                                  \
  { if (obj) Lib::Allocator::current->deallocateUnknown(obj); }          
#define ALLOC_UNKNOWN(size,className)				\
  (Lib::Allocator::current->allocateUnknown(size))
#define REALLOC_UNKNOWN(obj,newsize,className)                    \
    (Lib::Allocator::current->reallocateUnknown(obj,newsize))
#define DEALLOC_UNKNOWN(obj,className)		         \
  (Lib::Allocator::current->deallocateUnknown(obj))

#define START_CHECKING_FOR_ALLOCATOR_BYPASSES
#define STOP_CHECKING_FOR_ALLOCATOR_BYPASSES
#define BYPASSING_ALLOCATOR
     
#endif

} // namespace Lib

#undef ALLOC_SIZE_ATTR

#endif // __Allocator__
