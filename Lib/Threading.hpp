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
#include <atomic>
#define VTHREAD_LOCAL thread_local
#define VATOMIC(T) std::atomic<T>
#else
#define VTHREAD_LOCAL
#define VATOMIC(T) T
#endif

#if (defined(__has_feature) && __has_feature(thread_sanitizer))
#define TSAN 1
#else
#define TSAN 0
#endif

#endif
