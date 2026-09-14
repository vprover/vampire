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
 * @file Multiprocessing.hpp
 * Defines class Multiprocessing.
 */

#ifndef __Multiprocessing__
#define __Multiprocessing__

#include <sys/types.h>

namespace Lib::Sys {

// records how a child process died
struct Headstone {
  // child PID
  pid_t pid;
  // if the child was killed by a signal
  bool signalled;
  // exit code if child exited of its own accord,
  // or the signal number used otherwise
  int code;
};

// wrap the usual system calls
pid_t fork();
void kill(pid_t child, int signal);
// wait for a child process to exit: pass -1 for any child
// wraps waitpid
Headstone waitForChildTermination(pid_t pid);

}


#endif // __Multiprocessing__
