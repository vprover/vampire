/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __MacroUtils__
#define __MacroUtils__

#define __EXPAND(A) A
#define __CONCAT_IDENTS(A, B) A ## B
#define CONCAT_IDENTS(A, B) __EXPAND(__CONCAT_IDENTS)(A, B)

#define CAR(x, ...) x
#define CDR(x, ...) __VA_ARGS__

#endif // __MacroUtils__
