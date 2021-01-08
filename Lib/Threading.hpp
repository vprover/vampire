/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef __Threading__
#define __Threading__

#if VTHREADED
#define VTHREAD_LOCAL thread_local
#else
#define VTHREAD_LOCAL
#endif

#endif
