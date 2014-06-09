/**
 * @file CommandLine.hpp
 * Defines class for processing command line.
 *
 * @since 14/11/2004 Manchester
 */

#ifndef __CommandLine__
#define __CommandLine__

namespace Shell {

class OptionsContainer;

/**
 * Class CommandLine for processing command line.
 *
 * @since 14/11/2004 Manchester
 */
class CommandLine
{
public:
  CommandLine(int argc, char* argv []);
  // Will update global env
  void interpret();
private:
  /** Next string to process */
  char** _next;
  /** (After) last string to process */
  char** _last;
}; // class CommandLine

}

#endif
