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
 * @file Tracer.cpp
 * Try and work out where we crashed and print out a call stack.
 *
 * You don't typically _want_ to use this for debugging,
 * but sometimes Vampire crashes on some server somewhere,
 * and this is the best you're going to get. Good luck!
 *
 * @since 01/05/2002 Manchester
 * @since 25/12/2023 Mísečky invoke system binary for backtrace
 * @since 25/07/2024 Oxford invoke debugger for general sanity
 */

#include <csignal>
#include <cstdlib>
#include <sstream>

// for getpid()
// TODO compile guards for this and similar headers
#include <unistd.h>

#include "Tracer.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Options.hpp"

// define in version.cpp.in
extern const char* VERSION_STRING;

// try and invoke the GNU debugger in batch mode on this process
static bool try_gdb(pid_t pid) {
  std::stringstream command;
  command
    // ask for a traceback in batch mode
    << "gdb --batch -ex bt --pid="
    << pid;
  std::cout << command.str() << '\n';
  return std::system(command.str().c_str()) == 0;
}

// try and invoke the LLVM debugger in batch mode on this process
static bool try_lldb(pid_t pid) {
  std::stringstream command;
  command
    // ask for a traceback in batch mode
    << "lldb --batch -o bt "
    //<< argv0
    << " --attach-pid "
    << pid;
  std::cout << command.str() << '\n';
  return std::system(command.str().c_str()) == 0;
}

/**
 * Print the stack if --traceback on
 * @since 24/10/2002 Manchester
 * @since 12/7/2023 using platform-specific calls to get the stack trace
 */
void Debug::Tracer::printStack() {
  std::cout << "Version : " << VERSION_STRING << "\n";
  if(env.options->traceback()) {
    pid_t pid = getpid();
    // is your favourite debugger not here? add it!
    if(!try_gdb(pid) && !try_lldb(pid))
      std::cout << "(neither GDB nor LLDB worked: perhaps you need to install one of them?)\n";
  }
  else
    std::cout << "(use '--traceback on' to invoke a debugger and get a human-readable stack trace)\n";

  // usually causes debuggers to break here
  // if not under a debugger, ignored
  std::raise(SIGTRAP);
}
