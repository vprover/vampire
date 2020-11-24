/**
 * Usage:
 *
 *    CDEBUG("message: " << 123);
 *
 * If DEBUG_STREAM_ENABLED is true, prints the message to std:cerr,
 * and automatically adds a newline character at the end.
 *
 * Otherwise, do nothing.
 *
 * By default, DEBUG_STREAM_ENABLED is only enabled in debug mode.
 */

#include <iostream>


// By default, enable output in debug mode
#ifndef DEBUG_STREAM_ENABLED
#   define DEBUG_STREAM_ENABLED VDEBUG
// #   define DEBUG_STREAM_ENABLED 0
#endif

#ifdef CDEBUG
#   undef CDEBUG
#endif

#if DEBUG_STREAM_ENABLED
#define CDEBUG(x)                \
  do                             \
  {                              \
    std::cerr << x << std::endl; \
  } while (false)
#else
#define CDEBUG(x) \
  do              \
  { /* nothing */ \
  } while (false)
#endif

#undef DEBUG_STREAM_ENABLED
