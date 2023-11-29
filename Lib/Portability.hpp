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

static_assert(
    sizeof(void *) == 8,
    "Vampire assumes that the size of a pointer is 8 bytes for efficiency reasons. "
    "This may be fixed/relaxed in future, but for the moment expect problems if running on other architectures."
);

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
