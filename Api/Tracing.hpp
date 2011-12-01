/**
 * @file Tracing.hpp
 * Defines class Tracing.
 */

#ifndef __Tracing__
#define __Tracing__

#include <climits>
#include <string>


namespace Api {

class Tracing {
private:
  static unsigned s_traceStackDepth;
public:
  /**
   * Enable specified trace and either all its children, or children up to
   * specified depth limit.
   */
  static void enableTrace(std::string traceName, unsigned depth=UINT_MAX);
  /**
   * Process string specifying traces to be enabled (call the displayHelp() function
   * to see details)
   */
  static void processTraceString(std::string str);
  /**
   * Saves the current state of tracing tags to be restored later by
   * @c popTracingState().
   */
  static void pushTracingState();
  /**
   * Restores the last pushed state of tracing tags
   */
  static void popTracingState();
  /**
   * Displays help including the list of the tracing tags
   */
  static void displayHelp();
};

}

#endif // __Tracing__
