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

#endif /*__Portability__*/
