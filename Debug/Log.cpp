/**
 * @file Log.cpp
 * Implements class Log.
 */

#include "Lib/Portability.hpp"

#if !COMPILER_MSVC
#include <unistd.h>
#endif

#include "Log.hpp"

namespace Debug
{

/**
 * Return current process id for the purpose of log outputs
 */
size_t LOG_getpid()
{
#if !COMPILER_MSVC
  return getpid();
#else
  //TODO: Implement pid retrieval for windows
  return 0;
#endif
}

}
