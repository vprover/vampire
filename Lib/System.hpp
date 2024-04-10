/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file System.hpp
 * Defines the class System that contains wrappers of some system functions
 * and methods that take care of the system stuff and don't fit anywhere
 * else (handling signals etc...)
 */

#ifndef __System__
#define __System__

#include <cstdlib>

enum {
  VAMP_RESULT_STATUS_SUCCESS,
  VAMP_RESULT_STATUS_UNKNOWN,
  VAMP_RESULT_STATUS_OTHER_SIGNAL,
  VAMP_RESULT_STATUS_INTERRUPTED,
  VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION
};

namespace Lib {

class System {
public:
  static void setSignalHandlers();

  [[noreturn]] static void terminateImmediately(int resultStatus) {
    std::quick_exit(resultStatus);
  }

  static void registerForSIGHUPOnParentDeath();

  /**
   * Register the value of the argv[0] argument of the main function, so that
   * it can be later used to determine the executable directory
   */
  static void registerArgv0(const char* argv0) { s_argv0 = argv0; }
  static const char *getArgv0() { return s_argv0; }

private:
  static const char* s_argv0;
};

}

#endif /* __System__ */
