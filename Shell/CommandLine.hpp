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
  CommandLine(int argc, char* argv []);
  void interpret(Options&);
private:
  /** Next string to process */
  char** _next;
  /** (After) last string to process */
  char** _last;
}; // class CommandLine

}

#endif
