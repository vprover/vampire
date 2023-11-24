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
 *
 * @since 01/05/2002 Manchester
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
  std::cout << "call stack:";
  for(int i = 0; i < sz; i++)
    std::cout << ' ' << call_stack[sz - (i + 1)];
  std::cout << std::endl;

  std::cout << "invoking addr2line(1) ..." << std::endl;
  std::stringstream out;
  out << "addr2line -Cfe " << Lib::System::getArgv0();
  for(int i = 0; i < sz; i++)
    out << ' ' << call_stack[sz - (i + 1)];

  std::system(out.str().c_str());
#else
  // TODO backtrace support for other platforms
  str << "no backtrace support for this compiler/platform yet" << std::endl;
#endif
} // Tracer::printStack (ostream& str)

#endif
