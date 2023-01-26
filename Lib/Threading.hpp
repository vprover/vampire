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

// some things only if Vampire is compiled thread-safe
#if VTHREADED
#include <atomic>
#define VTHREAD_LOCAL thread_local
#define VATOMIC(T) std::atomic<T>
#else
#define VTHREAD_LOCAL
#define VATOMIC(T) T
#endif

/* detect ThreadSanitizer
 * this causes some trouble for Vampire,
 * notably because it provides its own global new/delete operators
 * it's very useful, however...
 */
#ifdef __has_feature
#if __has_feature(thread_sanitizer)
#define TSAN 1
#endif
#endif
#ifndef TSAN
#define TSAN 0
#endif

#if VTHREADED
bool weAreTheMainThread();
#else
bool weAreTheMainThread() { return true; }
#endif

#endif
