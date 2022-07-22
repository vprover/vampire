/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Theory.hpp"
#if WITH_GMP
#include "Theory_gmp.cpp"
#else
#include "Theory_int.cpp"
#endif
