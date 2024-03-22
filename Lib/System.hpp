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

#include "Forwards.hpp"
#include "Array.hpp"

#define VAMP_RESULT_STATUS_SUCCESS 0
#define VAMP_RESULT_STATUS_UNKNOWN 1
#define VAMP_RESULT_STATUS_OTHER_SIGNAL 2
#define VAMP_RESULT_STATUS_SIGINT 3
#define VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION 4

namespace Lib {

class System {
public:
  static void setSignalHandlers();
  static bool extractDirNameFromPath(vstring path, vstring& dir);

  static void addTerminationHandler(VoidFunc proc, unsigned priority=0);
  static void onTermination();
  [[noreturn]] static void terminateImmediately(int resultStatus);

  static void registerForSIGHUPOnParentDeath();

  /**
   * Register the value of the argv[0] argument of the main function, so that
   * it can be later used to determine the executable directory
   */
  static void registerArgv0(const char* argv0) { s_argv0 = argv0; }
  static const char *getArgv0() { return s_argv0; }

private:
  /**
   * Lists of functions that will be called before Vampire terminates
   *
   * Functions in lists with lower numbers will be called first.
   */
  static ZIArray<List<VoidFunc>*>& terminationHandlersArray();

  static const char* s_argv0;
};

}

#endif /* __System__ */
