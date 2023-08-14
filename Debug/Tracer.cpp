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

#if __has_include(<dlfcn.h>)
#include <dlfcn.h>
#define HAVE_DLFCN
#endif

#if __has_include(<cxxabi.h>)
#include <cxxabi.h>
#define HAVE_CXXABI
#endif

#endif

#include "Tracer.hpp"

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
  for(int i = 0; i < sz; i++) {
    for(int j = 0; j < i; j++)
      str << ' ';
    void *call = call_stack[sz - (i + 1)];
#ifdef HAVE_DLFCN
    Dl_info info;
    if(dladdr(call, &info) && info.dli_sname) {
      const char *name = info.dli_sname;
#ifdef HAVE_CXXABI
      int status;
      const char *demangled = abi::__cxa_demangle(info.dli_sname, nullptr, nullptr, &status);
      if(status == 0)
        name = demangled;
#else
      // TODO demangling support for other platforms
#endif
      str << name << std::endl;
    }
    else {
      str << "???" << std::endl;
    }
#else
    // TODO symbol name support for other platforms
    str << "???" << std::endl;
#endif
  }
#else
  // TODO backtrace support for other platforms
  str << "no backtrace support for this compiler/platform yet" << std::endl;
#endif
} // Tracer::printStack (std::ostream& str)
