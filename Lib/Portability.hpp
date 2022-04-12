/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef __Portability__
#define __Portability__

//////////////////////////////////////////////////////
// Detect compiler

#ifndef __APPLE__
# define __APPLE__ 0
#endif

#ifndef __CYGWIN__
# define __CYGWIN__ 0
#endif

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

// enable warnings for unused results
// C++17: replace this with [[nodiscard]]
#ifdef __GNUC__
#define VWARN_UNUSED [[gnu::warn_unused_result]]
#else
#define VWARN_UNUSED
#endif

// clang can attach to class, struct etc, but GCC cannot
#ifdef __clang__
#define VWARN_UNUSED_TYPE [[clang::warn_unused_result]]
#else
#define VWARN_UNUSED_TYPE
#endif

#endif /*__Portability__*/
