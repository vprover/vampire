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

#if VDEBUG
#include <string>
#endif

/** Page size in bytes */
#define PAGE_SIZE 131000
/** maximal size of allocated multi-page (in pages) */
//TODO: increased as needed by dis+1_3_bs=off_ep=RST_fsr=off_fde=none_lcm=kinky_nwc=1.2_1200 BOO046-1
//#define MAX_PAGES 4096
#define MAX_PAGES 8192
/** Any memory piece of this or larger size will be allocated as a page
 *  or contiguous sequence of pages */
#define REQUIRES_PAGE (PAGE_SIZE/2)
/** Maximal allowed number of allocators */
#define MAX_ALLOCATORS 256
/** Maximal height of skip lists */
#define MAX_SKIP_HEIGHT 32

namespace Lib {

class Allocator {
public:
  Allocator();
  ~Allocator();

  /** Return the amount of used memory */
  static size_t getUsedMemory()
  {
    return _usedMemory;
  }
  /** Return the global memory limit (in bytes) */
  static size_t getMemoryLimit()
  {
    CALL("Allocator::getMemoryLimit");
    return _memoryLimit;
  }
  /** Set the global memory limit (in bytes) */
  static void setMemoryLimit(size_t size)
  {
    CALL("Allocator::setMemoryLimit");
    _memoryLimit = size;
    _tolerated = size + (size/10);
  }
  /** The current allocator */
  static Allocator* current;

#if VDEBUG
  void* allocateKnown(size_t size,const char* className);
  void deallocateKnown(void* obj,size_t size,const char* className);
  void* allocateUnknown(size_t size,const char* className);
  void deallocateUnknown(void* obj,const char* className);
  static void addressStatus(const void* address);
  static void reportUsageByClasses();
#else
  void* allocateKnown(size_t size);
  void deallocateKnown(void* obj,size_t size);
  void* allocateUnknown(size_t size);
  void deallocateUnknown(void* obj);
#endif

  class Initialiser {
  public:
    /** Initialise the static allocator's methods */
    Initialiser()
    {
      CALL("Allocator::Initialiser::Initialiser");

      if (Allocator::_initialised++ == 0) {
	Allocator::initialise();
      }
    } // Initialiser::Initialiser

    ~Initialiser()
    {
      CALL("Allocator::Initialiser::~Initialiser");
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
   *  size of the array is small.
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
   * This pieces of memory are kept in a skip list
   * @since 10/01/2007 Manchester
   */
  struct Unknown {
    /** Size, used both when the piece is allocated and when it is kept
     *  in the free list. It is the size of the piece, since the size of
     *  the datastructure using the piece may actually be smaller */
    size_t size;
    /** Pointer to the next available piece. Used when kept in
     *  the skip list. */
    Unknown* next;
  }; // class Unknown

#if VDEBUG
public:
  /** Descriptor stores information about allocated pieces of memory */
  struct Descriptor
  {
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

    std::string toString() const;

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
   * A piece of memory whose size is multiple of PAGE_SIZE. Each page
   * is used in one of the following ways:
   * <ol>
   *  <li>to store a collection of Knowns</li>
   *  <li>to store a collection of Uknowns</li>
   *  <li>to store a single object of size greater than or equal to
   *      REQUIRES_PAGE</li>
   * </ol>
   * Available pages are stored by the global manager.
   * @warning @b size should go just before @b content since Vampire
   *             must be able to know the size of both Page and Unknown
   *             before knowing the type (that is, Page or Unknown)
   * @since 10/01/2007 Manchester
   */
  struct Page {
    Page* next;
    /** The previous page, if any */
    Page* previous;
    /**  Size of this page, multiple of PAGE_SIZE */
    size_t size;
    /** The next page, if any, if the page is not usable any more.
     *  If the page is the currently usable page, then it is the
     *  pointer to the last allocated piece.
     */
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
  /** The free list */
  Known* _freeList[REQUIRES_PAGE/4];
  /** All pages allocated by this allocator and not returned to the
   *  global one. The first page is always a reserve page */
  Page* _myPages;
  /** Number of bytes available on the reserve page */
  size_t _reserveBytesAvailable;
  /** next available known */
  char* _nextAvailableReserve;

  /** Total memory allocated by pages */
  static size_t _usedMemory;
  /** Page allocator array */
  static Page* _pages[MAX_PAGES];
//   /** reserve using for allocating pages, allocated 4M at a time  */
//   static char* _pageReserve;

  friend class Initialiser;
}; // class Allocator

/** An initialiser to be included in every compilation unit to ensure
 *  that the memory has been initialised properly.
 */
static Allocator::Initialiser _____;

/**
 * Allocate an array of objects of type @b T that has length @b length
 * starting at @b placement, and return a pointer to its first element
 * (whose value is equal to @b placement)
 */
template<typename T>
T* array_new(void* placement, size_t length)
{
  CALL("array_new");
  ASS_NEQ(placement,0);
  ASS_G(length,0);

  T* res=static_cast<T*>(placement);
  T* p=res;
  while(length--) {
    ::new(static_cast<void*>(p++)) T();
  }
  return res;
}

/**
 * Destroy the array @b array of objects of type @b T and that has length
 * @b length
 */
template<typename T>
void array_delete(T* array, size_t length)
{
  CALL("array_delete");
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
#define CLASS_NAME(name) \
  static const char* className () { return name; }
#define ALLOC_KNOWN(size,className)				\
  (Lib::Allocator::current->allocateKnown(size,className))
#define ALLOC_UNKNOWN(size,className)				\
  (Lib::Allocator::current->allocateUnknown(size,className))
#define DEALLOC_KNOWN(obj,size,className)		        \
  (Lib::Allocator::current->deallocateKnown(obj,size,className))
#define DEALLOC_UNKNOWN(obj,className)		                \
  (Lib::Allocator::current->deallocateUnknown(obj,className))

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
#define ALLOC_UNKNOWN(size,className)				\
  (Lib::Allocator::current->allocateUnknown(size))
#define DEALLOC_UNKNOWN(obj,className)		         \
  (Lib::Allocator::current->deallocateUnknown(obj))

#endif

} // namespace Lib

#endif // __Allocator__
