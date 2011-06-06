/**
 * @file Log.cpp
 * Implements class Log.
 */

#include "Lib/System.hpp"

#include "Log.hpp"

namespace Debug
{

using namespace Lib;

/**
 * Return current process id for the purpose of log outputs
 */
size_t LOG_getpid()
{
  return System::getPID();
}

}
