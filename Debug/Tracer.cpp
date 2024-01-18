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
 */

#ifdef __has_include

#if __has_include(<execinfo.h>)
#include <execinfo.h>
#define HAVE_EXECINFO
#endif

#include <cstdlib>
#include <sstream>

#include "Tracer.hpp"
#include "Lib/System.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Options.hpp"

// define in version.cpp.in
extern const char* VERSION_STRING;

// if we have a callstack, the maximum number to actually retrieve
const unsigned MAX_CALLS = 1024;

/**
 * Print the stack.
 * @since 24/10/2002 Manchester
 * @since 12/7/2023 using platform-specific calls to get the stack trace
 */
void Debug::Tracer::printStack(std::ostream& str) {
  str << "Version : " << VERSION_STRING << "\n";

#ifdef HAVE_EXECINFO
  void *call_stack[MAX_CALLS];
  int sz = ::backtrace(call_stack, MAX_CALLS);
  str << "call stack:";
  for(int i = 0; i < sz; i++)
    str << ' ' << call_stack[sz - (i + 1)];
  str << std::endl;

  if (env.options->traceback()) {
// UNIX-like systems, including BSD and Linux but not MacOS
#if defined(__unix__)
  str << "invoking addr2line(1) ..." << std::endl;
  std::stringstream out;
  out << "addr2line -Cfe " << Lib::System::getArgv0();
  for(int i = 0; i < sz; i++)
    out << ' ' << call_stack[sz - (i + 1)];
  std::system(out.str().c_str());
// Apple things
#elif defined(__APPLE__)
  str << "invoking atos(1) ..." << std::endl;
  std::stringstream out;
  out << "atos -o " << Lib::System::getArgv0();
  for(int i = 0; i < sz; i++)
    out << ' ' << call_stack[sz - (i + 1)];
  std::system(out.str().c_str());
#else
  // TODO symbol lookup support for other platforms
  str << "no symbol lookup support for this platform yet" << std::endl;
#endif
  }

#else
  // TODO backtrace support for other platforms
  str << "no call stack support for this platform yet" << std::endl;
#endif
} // Tracer::printStack (ostream& str)

#endif
