
/*
 * File Portability.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
#ifndef __Portability__
#define __Portability__

#include "Debug/Assertion.hpp"

//////////////////////////////////////////////////////
// Detect compiler

/*
#ifndef __APPLE__
# define __APPLE__ 0
#endif

#ifndef __CYGWIN__
# define __CYGWIN__ 0
#endif
*/

//////////////////////////////////////////////////////
// Detect architecture

#ifdef _LP64
#define ARCH_X64 1
#define ARCH_X86 0
#elif _M_X64
//this should handle MS C++ compiler
#define ARCH_X64 1
#define ARCH_X86 0
#else
#define ARCH_X64 0
#define ARCH_X86 1
#endif


//////////////////////////////////////////////////////
// Check assumed data-type properties

ASS_STATIC(sizeof(char)==1);


//////////////////////////////////////////////////////
// Definitions for non-GCC compilers

/* If we're not using GNU C, elide __attribute__ */
#ifndef __GNUC__
# define  __attribute__(x)  /*NOTHING*/
#endif

//////////////////////////////////////////////////////
// Function directives

/** Marks function which does not return */
#define NO_RETURN __attribute__((noreturn))

//////////////////////////////////////////////////////
// Prefetching

#ifdef EFENCE
# define NO_PREFETCH
#endif

#ifdef VALGRIND
# define NO_PREFETCH
#endif

#ifdef NO_PREFETCH
# define PREFETCH(x)
# define PREFETCH_LOC(x)
#else
# ifdef __GNUC__
#  define PREFETCH(x) __builtin_prefetch((x),0,2)
#  define PREFETCH_LOC(x) __builtin_prefetch((x),0,0)
# else
#  define PREFETCH(x)
#  define PREFETCH_LOC(x)
# endif
#endif

//////////////////////////////////////////////////////
// Attempt to detect endianness

#include <sys/param.h>  
#ifdef linux
# include <endian.h>    
#endif

/*
 * Best guess at if we're using big-endian or little-endian.  This may
 * need adjustment.
 */
#if (defined(__BYTE_ORDER) && defined(__LITTLE_ENDIAN) && \
     __BYTE_ORDER == __LITTLE_ENDIAN) || \
    (defined(i386) || defined(__i386__) || defined(__i486__) || \
     defined(__i586__) || defined(__i686__) || defined(vax) || defined(MIPSEL))
# define HASH_LITTLE_ENDIAN 1
# define HASH_BIG_ENDIAN 0
#elif (defined(__BYTE_ORDER) && defined(__BIG_ENDIAN) && \
       __BYTE_ORDER == __BIG_ENDIAN) || \
      (defined(sparc) || defined(POWERPC) || defined(mc68000) || defined(sel))
# define HASH_LITTLE_ENDIAN 0
# define HASH_BIG_ENDIAN 1
#else
# define HASH_LITTLE_ENDIAN 1
# define HASH_BIG_ENDIAN 0
#endif

#endif /*__Portability__*/
