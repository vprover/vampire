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
 */
#if VDEBUG

#include <sstream>
#include "DHMap.hpp"

#endif

#include <cstring>
#include <cstdlib>
#include "Lib/System.hpp"
#include "Lib/Timer.hpp"
#include "Shell/UIHelper.hpp"

#define SAFE_OUT_OF_MEM_SOLUTION 1

#ifndef USE_SYSTEM_ALLOCATION
/** If the following is set to true the Vampire will use the
 *  C++ new and delete for (de)allocating all data structures.
 */
#define USE_SYSTEM_ALLOCATION 0
#endif

#if USE_SYSTEM_ALLOCATION
# if __APPLE__
#  include <malloc/malloc.h>
# else
#  include <malloc.h>
# endif
#endif

/** set this to 1 to print all allocations/deallocations to stdout -- only with VDEBUG */
#define TRACE_ALLOCATIONS 0

/** Size of a page prefix (part of the page used for bookkeeping the
 * page itself) */
#define PAGE_PREFIX_SIZE (sizeof(Page)-sizeof(void*))

// To watch an address define the following values:
//   WATCH_FIRST     - the first watch point
//   WATCH_LAST      - the last watch point
//   WATCH_ADDRESS   - address to watch, 0 if no watch
// If WATCH_ADDRESS is non-null then any changes made to WATCH_ADDRESS will
// be output, provided they occur at control points between WATCH_FIRST
// and WATCH_LAST
#define WATCH_FIRST 0
#define WATCH_LAST UINT_MAX
// #define WATCH_ADDRESS 0x38001a0
#define WATCH_ADDRESS 0

#if WATCH_ADDRESS
/** becomes true when a page containing the watch point has been allocated */
bool watchPage = false;
/** last value stored in the watched address */
unsigned watchAddressLastValue = 0;
#endif

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Shell/Statistics.hpp"

#include "Exception.hpp"
#include "Environment.hpp"
#include "Allocator.hpp"

#if CHECK_LEAKS
#include "MemoryLeak.hpp"
#endif

using namespace Lib;
using namespace Shell;

int Allocator::_initialised = 0;
int Allocator::_total = 0;
size_t Allocator::_memoryLimit;
size_t Allocator::_tolerated;
Allocator* Allocator::current;
Allocator::Page* Allocator::_pages[MAX_PAGES];
size_t Allocator::_usedMemory = 0;
Allocator* Allocator::_all[MAX_ALLOCATORS];

#if VDEBUG
unsigned Allocator::Descriptor::globalTimestamp;
size_t Allocator::Descriptor::noOfEntries;
size_t Allocator::Descriptor::maxEntries;
size_t Allocator::Descriptor::capacity;
Allocator::Descriptor* Allocator::Descriptor::map;
Allocator::Descriptor* Allocator::Descriptor::afterLast;
unsigned Allocator::_tolerantZone = 1; // starts > 0; we are not checking by default, until we say so with START_CHECKING_FOR_BYPASSES
#endif

#if VDEBUG && USE_PRECISE_CLASS_NAMES && defined(__GNUC__)

/**
 * Function used by a variant of macro CLASS_NAME to obtain a pretty class name
 * from the content of the __PRETTY_FUNCTION__ variable
 */
string Lib::___prettyFunToClassName(std::string str)
{
  CALLC("___prettyFunToClassName",MAKE_CALLS);

  string noPref = str.substr(19);
  size_t fnNamePos = noPref.find("::className()");
  string className = noPref.substr(0,fnNamePos);
  //either empty, or contains one space followed by values of
  //template params
  string templateInfo = noPref.substr(fnNamePos+13);
  return className+templateInfo;
}

#endif

void* Allocator::operator new(size_t s) {
  return malloc(s);
}

void Allocator::operator delete(void* obj) {
  free(obj);
}

/**
 * Create a new allocator.
 * @since 10/01/2008 Manchester
 */
Allocator::Allocator()
{
  CALLC("Allocator::Allocator",MAKE_CALLS);

#if ! USE_SYSTEM_ALLOCATION
  for (int i = REQUIRES_PAGE/4-1;i >= 0;i--) {
    _freeList[i] = 0;
  }
  _reserveBytesAvailable = 0;
  _nextAvailableReserve = 0;
  _myPages = 0;
#endif
} // Allocator::Allocator

/**
 * Returns all pages to the global manager.
 * 
 * @since 18/03/2008 Torrevieja
 */
Lib::Allocator::~Allocator ()
{
  CALLC("Allocator::~Allocator",MAKE_CALLS);

  while (_myPages) {
    deallocatePages(_myPages);
  }
} // Allocator::~allocator

/**
 * Initialise all static structures and create a default allocator.
 * @since 10/01/2008 Manchester
 */
void Allocator::initialise()
{
  CALLC("Allocator::initialise",MAKE_CALLS)

#if VDEBUG
  Descriptor::map = 0;
  Descriptor::afterLast = 0;
#endif

  _memoryLimit = 300000000u;
  _tolerated = 330000000u;

#if ! USE_SYSTEM_ALLOCATION
  current = newAllocator();

  for (int i = MAX_PAGES-1;i >= 0;i--) {
    _pages[i] = 0;
  }
#endif
} // Allocator::initialise

#if VDEBUG
/**
 * Write information about a memory address to cout.
 * @since 30/03/2008 flight Murcia-Manchester
 */
void Allocator::addressStatus(const void* address)
{
  CALLC("Allocator::addressStatus",MAKE_CALLS);

  Descriptor* pg = 0; // page descriptor
  cout << "Status of address " << address << '\n';

  const char* a = static_cast<const char*>(address);
  for (int i = Descriptor::capacity-1;i >= 0;i--) {
    Descriptor& d = Descriptor::map[i];
    const char* addr = static_cast<const char*>(d.address);
    if (addr < a) {
      continue;
    }
    unsigned diff = a - addr;
    if (diff >= d.size) {
      continue;
    }
    if (d.page) {
      pg = &d;
      continue;
    }
    // found
    cout << "Descriptor: " << d << '\n'
	 << "Offset: " << diff << '\n'
	 << "End of status\n";
    return;
  }
  if (pg) {
    cout << "Not found but belongs to allocated page: " << *pg << '\n';
  }
  else {
    cout << "Does not belong to an allocated page\n";
  }
  cout << "End of status\n";
} // Allocator::addressStatus

void Allocator::reportUsageByClasses()
{
  Lib::DHMap<const char*, size_t> summary;
  Lib::DHMap<const char*, size_t> cntSummary;
  for (int i = Descriptor::capacity-1;i >= 0;i--) {
    Descriptor& d = Descriptor::map[i];
    if (!d.address || !d.size || !d.allocated) {
      continue;
    }
    size_t occupied;
    if(summary.find(d.cls, occupied)) {
      summary.set(d.cls, occupied+d.size);
      size_t cnt;
      ALWAYS(cntSummary.find(d.cls, cnt));
      cntSummary.set(d.cls, cnt+1);
    } else {
      summary.set(d.cls, d.size);
      cntSummary.set(d.cls, 1);
    }
  }

  Lib::DHMap<const char*, size_t>::Iterator sit(summary);
  cout<<"class\tcount\tsize"<<endl;
  while(sit.hasNext()) {
    const char* cls;
    size_t occupied, cnt;
    sit.next(cls,occupied);
    ALWAYS(cntSummary.find(cls,cnt));
    cout<<cls<<":\t"<<cnt<<"\t"<<occupied<<endl;
  }
}

#endif

/**
 * Cleanup: do whatever needed after the last use of class Allocator.
 * @since 10/01/2008 Manchester
 */
void Allocator::cleanup()
{
  CALLC("Allocator::cleanup",MAKE_CALLS);
  BYPASSING_ALLOCATOR;

  // delete all allocators
  for (int i = _total-1;i >= 0;i--) {
    delete _all[i];
  }
       
#if CHECK_LEAKS
  if (MemoryLeak::report()) {
    int leaks = 0;
    for (int i = Descriptor::capacity-1;i >= 0;i--) {
      Descriptor& d = Descriptor::map[i];
      if (d.allocated) {
	if (! leaks) {
	  cout << "Memory leaks found!\n";
	}
	cout << ++leaks << ": " << d.cls << " (" << d.address << "), timestamp: "
	     << d.timestamp << "\n";
      }
    }
    if (leaks) {
      cout << "End of memory leak report\n";
    }
  }
#endif

  // release all the pages
  for (int i = MAX_PAGES-1;i >= 0;i--) {
#if VDEBUG && TRACE_ALLOCATIONS
    int cnt = 0;
#endif    
    while (_pages[i]) {
      Page* pg = _pages[i];
      _pages[i] = pg->next;
      
      char* mem = reinterpret_cast<char*>(pg);
      free(mem);
#if VDEBUG && TRACE_ALLOCATIONS
      cnt++;
#endif    
    }
#if VDEBUG && TRACE_ALLOCATIONS    
      if (cnt) {
        cout << "deleted " << cnt << " global page(s) of size " << VPAGE_SIZE*(i+1) << endl;
      }
#endif        
  }
    
#if VDEBUG
  delete[] Descriptor::map;
#endif  
} // Allocator::initialise


/**
 * Deallocate an object whose size is known. It works as follows:
 * if the object size is less then REQUIRES_PAGE, it is put in the
 * corresponding free list. Otherwise, it is deallocated as a large
 * object.
 * @since 10/01/2008 Manchester
 */
#if VDEBUG
void Allocator::deallocateKnown(void* obj,size_t size,const char* className)
#else
void Allocator::deallocateKnown(void* obj,size_t size)
#endif
{
  CALLC("Allocator::deallocateKnown",MAKE_CALLS);
  ASS(obj);

  TimeoutProtector tp;

#if VDEBUG
  Descriptor* desc = Descriptor::find(obj);
  desc->timestamp = ++Descriptor::globalTimestamp;
#if TRACE_ALLOCATIONS
  cout << *desc << ": DK\n" << flush;
#endif
  ASS_EQ(desc->address, obj);
  ASS_STR_EQ(desc->cls,className);
  ASS_EQ(desc->size, size);
  ASS(desc->allocated);
  ASS(desc->known);
  ASS(! desc->page);
#endif

#if USE_SYSTEM_ALLOCATION
#if VDEBUG
  desc->allocated = 0;
#endif
  free(obj);
  return;
#else   // ! USE_SYSTEM_ALLOCATION
  if (size >= REQUIRES_PAGE) {
    char* mem = reinterpret_cast<char*>(obj)-PAGE_PREFIX_SIZE;
    deallocatePages(reinterpret_cast<Page*>(mem));
  }
  else {
    int index = (size-1)/sizeof(Known);
    Known* mem = reinterpret_cast<Known*>(obj);
    mem->next = _freeList[index];
    _freeList[index] = mem;
  }

#if VDEBUG
  desc->allocated = 0;
#endif

#if WATCH_ADDRESS
  unsigned addr = (unsigned)obj;
  unsigned cp = Debug::Tracer::passedControlPoints();
  if (addr <= WATCH_ADDRESS &&
      WATCH_ADDRESS < addr+size &&
      cp >= WATCH_FIRST &&
      cp <= WATCH_LAST) {
    unsigned currentValue = *((unsigned*)WATCH_ADDRESS);
    cout << "Watch! Known-size piece deallocated!\n"
	 << "  Timestamp: " << cp << '\n'
	 << "  Piece addresses: " << (void*)addr << '-'
	 << (void*)(addr+size-1) << '\n';
    if (currentValue != watchAddressLastValue) {
      watchAddressLastValue = currentValue;
      cout << "  Value: " << (void*)watchAddressLastValue << '\n';
    }
    cout << "  " << *desc << '\n'
	 << "Watch! end\n";
  }
#endif
#endif
} // Allocator::deallocateKnown

/**
 * Deallocate an object whose size is unknown. It works similar to
 * deallocateKnow except that an unknown contains an extra word
 * storing the size of the object.
 * @since 13/01/2008 Manchester
 */
#if VDEBUG
void Allocator::deallocateUnknown(void* obj,const char* className)
#else
void Allocator::deallocateUnknown(void* obj)
#endif
{
  CALLC("Allocator::deallocateUnknown",MAKE_CALLS);

  TimeoutProtector tp;

#if VDEBUG
  Descriptor* desc = Descriptor::find(obj);
  desc->timestamp = ++Descriptor::globalTimestamp;
#if TRACE_ALLOCATIONS
  cout << *desc << ": DU\n" << flush;
#endif
  ASS_EQ(desc->address, obj);
  ASS_STR_EQ(desc->cls,className);
  ASS(desc->allocated);
  ASS(! desc->known);
  ASS(! desc->page);
  desc->allocated = 0;
#endif

#if USE_SYSTEM_ALLOCATION
  char* memObj = reinterpret_cast<char*>(obj) - sizeof(Known);
  free(memObj);
  return;
#endif

  char* mem = reinterpret_cast<char*>(obj) - sizeof(Known);
  Unknown* unknown = reinterpret_cast<Unknown*>(mem);
  size_t size = unknown->size;
  ASS_EQ(desc->size, size);

  if (size >= REQUIRES_PAGE) {
    mem = mem-PAGE_PREFIX_SIZE;
    deallocatePages(reinterpret_cast<Page*>(mem));
  }
  else {
    Known* known = reinterpret_cast<Known*>(mem);
    int index = (size-1)/sizeof(Known);
    known->next = _freeList[index];
    _freeList[index] = known;
  }

#if WATCH_ADDRESS
  unsigned addr = (unsigned)(void*)mem;
  unsigned cp = Debug::Tracer::passedControlPoints();
  if (addr <= WATCH_ADDRESS &&
      WATCH_ADDRESS < addr+size &&
      cp >= WATCH_FIRST &&
      cp <= WATCH_LAST) {
    unsigned currentValue = *((unsigned*)WATCH_ADDRESS);
    cout << "Watch! Unknown-size piece deallocated!\n"
	 << "  Timestamp: " << cp << '\n'
	 << "  Piece addresses: " << (void*)addr << '-'
	 << (void*)(addr+size-1) << '\n';
    if (currentValue != watchAddressLastValue) {
      watchAddressLastValue = currentValue;
      cout << "  Value: " << (void*)watchAddressLastValue << '\n';
    }
    cout << "  " << *desc << '\n'
	 << "Watch! end\n";
  }
#endif
} // Allocator::deallocateUnknown

/**
 * Reallocate an object whose size is unknown.
 * The functionality should correspond to the realloc function for the standard library.
 * This means it can be called with (obj == NULL) in which case it simply allocates.
 * If obj points to allocated memory, this memory must have been obtained by calling
 * reallocateUnknown or allocateUnknown.
 * Also, the part of obj which fits into newsize will get copied over.
 *
 * The corresponding "free" function is deallocateUnknown.
 */
#if VDEBUG
void* Allocator::reallocateUnknown(void* obj, size_t newsize, const char* className)
#else
void* Allocator::reallocateUnknown(void* obj, size_t newsize)
#endif
{
  CALLC("Allocator::reallocateUnknown",MAKE_CALLS);

  // cout << "reallocateUnknown " << obj << " newsize " << newsize << endl;

#if VDEBUG
  void* newobj = allocateUnknown(newsize,className);
#else
  void* newobj = allocateUnknown(newsize);
#endif

  if (obj == NULL) {
    return newobj;
  }

  size_t size = unknownsSize(obj);

  ASS_NEQ(size,newsize); // it all works when violated, but a code which wants to reallocate for the same size is suspicious

  if (newsize < size) {
    size = newsize;
  }

  std::memcpy(newobj,obj,size);

#if VDEBUG
  deallocateUnknown(obj,className);
#else
  deallocateUnknown(obj);
#endif

  return newobj;
} // Allocator::reallocateUnknown

/**
 * Create a new allocator.
 * @since 10/01/2008 Manchester
 */
Allocator* Allocator::newAllocator()
{
  CALLC("Allocator::newAllocator",MAKE_CALLS);
  BYPASSING_ALLOCATOR;
  
#if VDEBUG && USE_SYSTEM_ALLOCATION
  ASSERTION_VIOLATION;
#else
  Allocator* result = new Allocator();

  if (_total >= MAX_ALLOCATORS) {
    throw Exception("The maximal number of allocators exceeded.");
  }
  _all[_total++] = result;
  return result;
#endif
} // Allocator::newAllocator

/**
 * Allocate a (multi)page able to store a structure of size @b size
 * @since 12/01/2008 Manchester
 */
Allocator::Page* Allocator::allocatePages(size_t size)
{
  CALLC("Allocator::allocatePages",MAKE_CALLS);
  ASS(size >= 0);

#if VDEBUG && USE_SYSTEM_ALLOCATION
  ASSERTION_VIOLATION;
#else
  size += PAGE_PREFIX_SIZE;

  Page* result;
  size_t index = (size-1)/VPAGE_SIZE;
  size_t realSize = VPAGE_SIZE*(index+1);

  // check if the allocation isn't too big
  if(index>=MAX_PAGES) {
#if SAFE_OUT_OF_MEM_SOLUTION
    env.beginOutput();
    reportSpiderStatus('m');
    env.out() << "Unsupported amount of allocated memory: "<<realSize<<"!\n";
    if(env.statistics) {
      env.statistics->print(env.out());
    }
#if VDEBUG
    Debug::Tracer::printStack(env.out());
#endif
    env.endOutput();
    System::terminateImmediately(1);
#else
    throw Lib::MemoryLimitExceededException();
#endif
  }
  // check if there is a page in the list available
  if (_pages[index]) {
    result = _pages[index];
    _pages[index] = result->next;
  }
  else {
    size_t newSize = _usedMemory+realSize;
    if (_tolerated && newSize > _tolerated) {
      env.statistics->terminationReason = Shell::Statistics::MEMORY_LIMIT;
      //increase the limit, so that the exception can be handled properly.
      _tolerated=newSize+1000000;

#if SAFE_OUT_OF_MEM_SOLUTION
      env.beginOutput();
      reportSpiderStatus('m');
      env.out() << "Memory limit exceeded!\n";
# if VDEBUG
	Allocator::reportUsageByClasses();
# endif
      if(env.statistics) {
	env.statistics->print(env.out());
      }
      env.endOutput();
      System::terminateImmediately(1);
#else
      throw Lib::MemoryLimitExceededException();
#endif
    }
    _usedMemory = newSize;

    char* mem = static_cast<char*>(malloc(realSize));
    if (!mem) {
      env.beginOutput();
      reportSpiderStatus('m');
      env.out() << "Memory limit exceeded!\n";
      if(env.statistics) {
        // statistics should be fine when out of memory, but not RuntimeStatistics, which allocate a Stack
        // (i.e. potential crazy exception recursion may happen in DEBUG mode)
        env.statistics->print(env.out());
      }
      env.endOutput();
      System::terminateImmediately(1);

      // CANNOT throw vampire exception when out of memory - it contains allocations because of the message string
      // throw Lib::MemoryLimitExceededException(true);
    }
    result = reinterpret_cast<Page*>(mem);
  }
  result->size = realSize;

#if VDEBUG
  Descriptor* desc = Descriptor::find(result);
  ASS(! desc->allocated);

  desc->address = result;
  desc->cls = "Allocator::Page";
  desc->timestamp = ++Descriptor::globalTimestamp;
  desc->size = realSize;
  desc->allocated = 1;
  desc->known = 0;
  desc->page = 1;

#if TRACE_ALLOCATIONS
  cout << *desc << ": AP\n" << flush;
#endif // TRACE_ALLOCATIONS
#endif // VDEBUG

  result->next = _myPages;
  result->previous = 0;
  if (_myPages) {
    _myPages->previous = result;
  }
  _myPages = result;

#if WATCH_ADDRESS
  unsigned addr = (unsigned)(void*)result;
  unsigned cp = Debug::Tracer::passedControlPoints();
  if (addr <= WATCH_ADDRESS &&
      WATCH_ADDRESS < addr+realSize) {
    watchPage = true;
    Debug::Tracer::canWatch = true;
    if (cp >= WATCH_FIRST &&
	cp <= WATCH_LAST) {
      watchAddressLastValue = *((unsigned*)WATCH_ADDRESS);
      cout << "Watch! Page allocated!\n"
	   << "  Timestamp: " << cp << '\n'
	   << "  Page addresses: " << (void*)addr << '-'
	   << (void*)(addr+realSize-1) << '\n'
	   << "  Value: " << (void*)watchAddressLastValue << '\n'
	   << "Watch! end\n";
    }
  }
#endif

  return result;
#endif // USE_SYSTEM_ALLOCATION
} // Allocator::allocatePages

/**
 * Deallocate a (multi)page, that is, add it to the free list of
 * pages.
 * @since 11/01/2008 Manchester
 */
void Allocator::deallocatePages(Page* page)
{
  ASS(page);

#if VDEBUG && USE_SYSTEM_ALLOCATION
  ASSERTION_VIOLATION;
#else
  CALLC("Allocator::deallocatePages",MAKE_CALLS);

#if VDEBUG
  Descriptor* desc = Descriptor::find(page);
  desc->timestamp = ++Descriptor::globalTimestamp;
#if TRACE_ALLOCATIONS
  cout << *desc << ": DP\n" << flush;
#endif
  ASS(desc->address == page);
  ASS_STR_EQ(desc->cls,"Allocator::Page");
  ASS(desc->size == page->size);
  ASS(desc->allocated);
  ASS(! desc->known);
  ASS(desc->page);
  desc->allocated = 0;
#endif

  size_t size = page->size;
  int index = (size-1)/VPAGE_SIZE;

  Page* next = page->next;
  if (next) {
    next->previous = page->previous;
  }
  if (page->previous) {
    page->previous->next = next;
  }

  if (page == _myPages) {
    _myPages = next;
  }

  page->next = _pages[index];
  _pages[index] = page;

#if WATCH_ADDRESS
  unsigned addr = (unsigned)(void*)page;
  unsigned cp = Debug::Tracer::passedControlPoints();
  if (addr <= WATCH_ADDRESS &&
      WATCH_ADDRESS < addr+size &&
      cp >= WATCH_FIRST &&
      cp <= WATCH_LAST) {
    unsigned currentValue = *((unsigned*)WATCH_ADDRESS);
    cout << "Watch! Page deallocated!\n"
	 << "  Timestamp: " << cp << '\n'
	 << "  Page addresses: " << (void*)addr << '-'
	 << (void*)(addr+size-1) << '\n';
    if (currentValue != watchAddressLastValue) {
      watchAddressLastValue = currentValue;
      cout << "  Value: " << (void*)watchAddressLastValue << '\n';
    }
    cout << "Watch! end\n";
  }
#endif

#endif // ! USE_SYSTEM_ALLOCATION
} // Allocator::deallocatePages(Page*)


/**
 * Allocate object of size @b size. 
 * @since 12/01/2008 Manchester
 */
#if VDEBUG
void* Allocator::allocateKnown(size_t size,const char* className)
#else
void* Allocator::allocateKnown(size_t size)
#endif
{
  CALLC("Allocator::allocateKnown",MAKE_CALLS);
  ASS(size > 0);

  TimeoutProtector tp;

  char* result = allocatePiece(size);

#if VDEBUG
  Descriptor* desc = Descriptor::find(result);
  ASS_REP(! desc->allocated, size);

  desc->address = result;
  desc->cls = className;
  desc->timestamp = ++Descriptor::globalTimestamp;
  desc->size = size;
  desc->allocated = 1;
  desc->known = 1;
  desc->page = 0;
#if TRACE_ALLOCATIONS
  cout << *desc << ": AK\n" << flush;
#endif
#endif

#if WATCH_ADDRESS
  unsigned addr = (unsigned)(void*)result;
  unsigned cp = Debug::Tracer::passedControlPoints();
  if (addr <= WATCH_ADDRESS &&
      WATCH_ADDRESS < addr+size &&
      cp >= WATCH_FIRST &&
      cp <= WATCH_LAST) {
    unsigned currentValue = *((unsigned*)WATCH_ADDRESS);
    cout << "Watch! Known-size piece allocated!\n"
	 << "  Timestamp: " << cp << '\n'
	 << "  Piece addresses: " << (void*)addr << '-'
	 << (void*)(addr+size-1) << '\n';
    if (currentValue != watchAddressLastValue) {
      watchAddressLastValue = currentValue;
      cout << "  Value: " << (void*)watchAddressLastValue << '\n';
    }
    cout << "  " << *desc << '\n'
	 << "Watch! end\n";
  }
#endif
  return result;
} // Allocator::allocateKnown


/**
 * Allocate a piece of memory of a given size.
 * If @b size is REQUIRES_PAGE or more it is 
 * allocated on a separate page.
 * @since 15/01/2008 Manchester
 */
char* Allocator::allocatePiece(size_t size)
{
  CALLC("Allocator::allocatePiece",MAKE_CALLS);

  char* result;
#if USE_SYSTEM_ALLOCATION
//  result = new char[size];
  result = static_cast<char*>(malloc(size));
#else // USE_SYSTEM_ALLOCATION
  if (size >= REQUIRES_PAGE) {
    Page* page = allocatePages(size);
    result = reinterpret_cast<char*>(page) + PAGE_PREFIX_SIZE;
  }
  else { // try to find it in the free list
    int index = (size-1)/sizeof(Known);
    // Align on the pointer basis
    size = (index+1) * sizeof(Known);
    Known* mem = _freeList[index];
    if (mem) {
      _freeList[index] = mem->next;
      result = reinterpret_cast<char*>(mem);
    } // There is no available piece in the free list
    else if (_reserveBytesAvailable >= size) { // reserve has enough memory
    use_reserve:
      result = _nextAvailableReserve;
      _nextAvailableReserve += size;
      _reserveBytesAvailable -= size;
    }
    else {
      // No bytes in the reserve, new reserve page must be allocated
      // First, save any remaining memory in the free list
      if (_reserveBytesAvailable) {
	index = (_reserveBytesAvailable-1)/sizeof(Known);
	Known* save = reinterpret_cast<Known*>(_nextAvailableReserve);
#if VDEBUG
	Descriptor* desc = Descriptor::find(save);
	ASS(! desc->allocated);
	desc->size = _reserveBytesAvailable;
	desc->timestamp = ++Descriptor::globalTimestamp;
#if TRACE_ALLOCATIONS
	cout << *desc << ": RR\n" << flush;
#endif
#endif
	save->next = _freeList[index];
	_freeList[index] = save;
      }
      Page* page = allocatePages(0);
      _reserveBytesAvailable = VPAGE_SIZE-PAGE_PREFIX_SIZE;
      _nextAvailableReserve = reinterpret_cast<char*>(&page->content);
      goto use_reserve;
    }
  }
#endif // USE_SYSTEM_ALLOCATION
  return result;
} // Allocator::allocatePiece


/**
 * Works similar to allocateKnown but saves the size of the
 * object in an extra word. More precisely, it saves the size
 * of the memory needed to store the object, that is, the size
 * of the object plus the size of a word.
 * @since 13/01/2008 Manchester
 */
#if VDEBUG
void* Allocator::allocateUnknown(size_t size,const char* className)
#else
void* Allocator::allocateUnknown(size_t size)
#endif
{
  CALLC("Allocator::allocateUnknown",MAKE_CALLS);
  ASS(size>0);

  TimeoutProtector tp;

  size += sizeof(Known);
  char* result = allocatePiece(size);
  Unknown* unknown = reinterpret_cast<Unknown*>(result);
  unknown->size = size;
  result += sizeof(Known);

#if VDEBUG
  Descriptor* desc = Descriptor::find(result);
  ASS(! desc->allocated);

  desc->address = result;
  desc->cls = className;
  desc->timestamp = ++Descriptor::globalTimestamp;
  desc->size = size;
  desc->allocated = 1;
  desc->known = 0;
  desc->page = 0;

#if TRACE_ALLOCATIONS
  cout << *desc << ": AU\n" << flush;
#endif
#endif

#if WATCH_ADDRESS
  unsigned addr = (unsigned)(void*)(result-sizeof(Known));
  unsigned cp = Debug::Tracer::passedControlPoints();
  if (addr <= WATCH_ADDRESS &&
      WATCH_ADDRESS < addr+size &&
      cp >= WATCH_FIRST &&
      cp <= WATCH_LAST) {
    unsigned currentValue = *((unsigned*)WATCH_ADDRESS);
    cout << "Watch! Unknown-size piece allocated!\n"
	 << "  Timestamp: " << cp << '\n'
	 << "  Piece addresses: " << (void*)addr << '-'
	 << (void*)(addr+size-1) << '\n';
    if (currentValue != watchAddressLastValue) {
      watchAddressLastValue = currentValue;
      cout << "  Value: " << (void*)watchAddressLastValue << '\n';
    }
    cout << "  " << *desc << '\n'
	 << "Watch! end\n";
  }
#endif
  return result;
} // Allocator::allocateUnknown


#if VDEBUG
/**
 * Find a descriptor in the map, and if it is not there, add it.
 * @since 14/12/2005 Bellevue
 */
Allocator::Descriptor* Allocator::Descriptor::find (const void* addr)
{    
  CALLC("Allocator::Descriptor::find",MAKE_CALLS);
  BYPASSING_ALLOCATOR;

  if (noOfEntries >= maxEntries) { // too many entries
    // expand the hash table first
//     capacity = capacity ? 2*capacity : 8188;
    capacity = capacity ? 2*capacity : 2000000;

#if TRACE_ALLOCATIONS
    cout << "Allocator map expansion to capacity " << capacity << "\n" << flush;
#endif

    Descriptor* oldMap = map;
    try {
      map = new Descriptor [capacity];
    } catch(bad_alloc&) {
      env.beginOutput();
      reportSpiderStatus('m');
      env.out() << "Memory limit exceeded!\n";
      env.endOutput();
      System::terminateImmediately(1);

      // CANNOT throw vampire exception when out of memory - it contains allocations because of the message string
      // throw Lib::MemoryLimitExceededException(true);
    }
    Descriptor* oldAfterLast = afterLast;
    afterLast = map + capacity;
    maxEntries = (int)(capacity * 0.7);
    noOfEntries = 0;

    for (Descriptor* current = oldMap;current != oldAfterLast;current++) {
      if (! current->address) {
	continue;
      }
      // now current is occupied
      Descriptor* d = find(current->address);
      *d = *current;
    }
    delete [] oldMap;
  }
  Descriptor* desc = map + (hash(addr) % capacity);
  while (desc->address) {
    if (desc->address == addr) {
      return desc;
    }

    desc++;
    // check if the entry is a valid one
    if (desc == afterLast) {
      desc = map;
    }
  }

  desc->address = addr;
  noOfEntries++;

  return desc;
} // Allocator::Descriptor::find

/**
 * Output the string description of the descriptor to an ostream.
 * @author Martin Suda
 * @since 12/08/2014 Manchester
 */
ostream& Lib::operator<<(ostream& out, const Allocator::Descriptor& d) {
  CALLC("operator<<(ostream,Allocator::Descriptor)",MAKE_CALLS);
  
  out << (size_t)(&d)
      << " [address:" << d.address
      << ",timestamp:" << d.timestamp
      << ",class:" << d.cls
      << ",size:" << d.size
      << ",allocated:" << (d.allocated ? "yes" : "no")
      << ",known:" << (d.known ? "yes" : "no")
      << ",page:" << (d.page ? "yes" : "no") << ']';  
  
  return out;
}

void* Allocator::Descriptor::operator new[](size_t s) {
  return malloc(s);
}

void Allocator::Descriptor::operator delete[](void* obj) {
  free(obj);
}

/**
 * Initialise a descriptor.
 * @since 17/12/2005 Vancouver
 */
Allocator::Descriptor::Descriptor ()
  : address(0),
    cls("???"),
    timestamp(0),
    size(0),
    allocated(0),
    known(0),
    page(0)
{
//   CALL("Allocator::Descriptor::Descriptor");
} // Allocator::Descriptor::Descriptor

/**
 * The FNV-hashing.
 * @since 31/03/2006 Bellevue
 */
unsigned Allocator::Descriptor::hash (const void* addr)
{
  CALLC("Allocator::Descriptor::hash",MAKE_CALLS);

  char* val = reinterpret_cast<char*>(&addr);
  unsigned hash = 2166136261u;
  for (int i = sizeof(void*)-1;i >= 0;i--) {
    hash = (hash ^ val[i]) * 16777619u;
  }
  return hash;
} // Allocator::Descriptor::hash(const char* str)

#endif

/**
 * In debug mode we replace the global new and delete (also the array versions)
 * and terminate in cases when they are used "unwillingly".
 * Where "unwillingly" means people didn't mark the code explicitly with BYPASSING_ALLOCATOR
 * and yet they attempt to call global new (and not the class specific versions 
 * built on top of Allocator).
 * 
 * Update: In release, we newly use global new/delete as well,
 * but just silently redirect the allocations to our Allocator.
 * Another update: Back to not using global new and delete in release
 * some compiles on some platforms produce weird bugs and segfaults
 * when connected to z3. (A static initialization order fiasco?
 * How does the linker know anyway what global new / delete to call if a linked library has its own?)
 *
 * This is a link about some requirements on new/delete: 
 * http://stackoverflow.com/questions/7194127/how-should-i-write-iso-c-standard-conformant-custom-new-and-delete-operators/
 * (Note that we ignore the globalHandler issue here.)
 **/ 

#if VDEBUG

void* operator new(size_t sz) {    
  ASS_REP(Allocator::_tolerantZone > 0,"Attempted to use global new operator, thus bypassing Allocator!");
  // Please read: https://github.com/easychair/vampire/wiki/Attempted-to-use-global-new-operator,-thus-bypassing-Allocator!
  
  static Allocator::Initialiser i; // to initialize Allocator even for other libraries
  
  if (sz == 0)
    sz = 1;
  
  void* res = ALLOC_UNKNOWN(sz,"global new");

  if (!res)
    throw bad_alloc();
  
  return res;
}

void* operator new[](size_t sz) {  
  ASS_REP(Allocator::_tolerantZone > 0,"Attempted to use global new[] operator, thus bypassing Allocator!");
  // Please read: https://github.com/easychair/vampire/wiki/Attempted-to-use-global-new-operator,-thus-bypassing-Allocator!

  static Allocator::Initialiser i; // to initialize Allocator even for other libraries

  if (sz == 0)
    sz = 1;
  
  void* res = ALLOC_UNKNOWN(sz,"global new[]");

  if (!res)
    throw bad_alloc();
  
  return res;
}

void operator delete(void* obj) throw() {  
  ASS_REP(Allocator::_tolerantZone > 0,"Custom operator new matched by global delete!");
  // Please read: https://github.com/easychair/vampire/wiki/Attempted-to-use-global-new-operator,-thus-bypassing-Allocator!

  static Allocator::Initialiser i; // to initialize Allocator even for other libraries

  if (obj != nullptr) {
    DEALLOC_UNKNOWN(obj,"global new");
  }
}

void operator delete[](void* obj) throw() {  
  ASS_REP(Allocator::_tolerantZone > 0,"Custom operator new[] matched by global delete[]!");
  // Please read: https://github.com/easychair/vampire/wiki/Attempted-to-use-global-new-operator,-thus-bypassing-Allocator!

  static Allocator::Initialiser i; // to initialize Allocator even for other libraries

  if (obj != nullptr) {
    DEALLOC_UNKNOWN(obj,"global new[]");
  }
}

#endif

#if VTEST

#include "Random.hpp"
using namespace Lib;

struct Mem
{
  void* address; // 0 if deallocated
  int size;      // 0 is deallocated
  bool known;
  const char* className;
  Mem() : address(0) {}
};

/**
 * Allocate many objects of known small sizes and
 * then deallocate them all.
 * @since 17/03/2008 Torrevieja
 */
void testAllocator()
{
  CALLC("testAllocator",MAKE_CALLS);
//   Random::setSeed(1);
  cout << "Testing the Allocator class...\n";

  Allocator* a = Allocator::current;

  int tries = 1000000000;  // number of tries
  int pieces = 1000;  // max number of allocated pieces
  int maxsize = 1000000;    // maximal memory size
  const char* classes[10] = {"a","b","c","d","e","f","g","h","i","j"};
  int frequency = 1000; // frequency of outputting a dot to cout
  int out = frequency;   // output when 0

   Mem* mems = new Mem[pieces]; // memory pieces
  int total = 0;
  for (int i = 0; i < tries;i++) {
    out--;
    if (! out) {
      out = frequency;
      cout << '.' << flush;
//       cout << total << '\n' << flush;
    }
    int rand = Random::getInteger(pieces);

    Mem& m = mems[rand];
    if (m.address) { // allocated
      if (m.known) {
	a->deallocateKnown(m.address,m.size,m.className);
      }
      else {
	a->deallocateUnknown(m.address,m.className);
      }
      m.address = 0;
    }
    else { // not allocated
      int size = Random::getInteger(maxsize)+1;
      m.size = size;
      total += size;
      const char* className = classes[Random::getInteger(10)];
      m.className = className;
      if (Random::getBit()) {
	m.known = false;
	m.address = a->allocateUnknown(size,className);
      }
      else {
	m.known = true;
	m.address = a->allocateKnown(size,className);
      }
    }
  }

  cout << "\nTest completed!\n";
} // testAllocator

#endif // VTEST


