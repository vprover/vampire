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
#include <climits>

//////////////////////////////////////////////////////
// architecture sanity check

static_assert(
    CHAR_BIT == 8,
    "Vampire assumes that there are 8 bits in a `char`"
);

#define VAMPIRE_PERF_EXISTS 0
#ifdef __linux__
#if __has_include(<linux/perf_event.h>)
#undef VAMPIRE_PERF_EXISTS
#define VAMPIRE_PERF_EXISTS 1
#endif
#endif

#endif /*__Portability__*/
