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
 * @file CommandLine.hpp
 * Defines class for processing command line.
 *
 * @since 14/11/2004 Manchester
 */

#ifndef __CommandLine__
#define __CommandLine__

#include <ostream>

namespace Shell {

class Options;

/**
 * Class CommandLine for processing command line.
 *
 * @since 14/11/2004 Manchester
 */
class CommandLine
{
public:
  CommandLine(int argc, const char* const argv []);
  void interpret(Options&);
private:
  /** Next string to process */
  const char* const * _next;
  /** (After) last string to process */
  const char* const * _last;
}; // class CommandLine

std::ostream& printVersion(std::ostream& out);

}

#endif
