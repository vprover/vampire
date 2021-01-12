/*
 * File NonZeroness.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef __NON_ZERONESS__HPP__
#define __NON_ZERONESS__HPP__

// TODO rename this file to something more appropriate

#define NON_ZERO_FAIL(ident, ground)                                                                          \
  env.statistics->nonZeroFailures ## ident ++;                                                                \
  if (ground) {                                                                                               \
    env.statistics->nonZeroFailures ## ident ## Ground ++;                                                    \
  }                                                                                                           \


#endif // __NON_ZERONESS__HPP__
