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
 * @file Tracing.hpp
 * Defines class Tracing.
 */

#ifndef __API_Tracing__
#define __API_Tracing__

#include <climits>

#include "Lib/VString.hpp"

namespace Api {

class Tracing {
private:
  static unsigned s_traceStackDepth;
public:
  /**
   * Enable specified trace and either all its children, or children up to
   * specified depth limit.
   */
  static void enableTrace(Lib::vstring traceName, unsigned depth=UINT_MAX);
  /**
   * Process vstring specifying traces to be enabled (call the displayHelp() function
   * to see details)
   */
  static void processTraceString(Lib::vstring str);
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

#endif // __API_Tracing__
