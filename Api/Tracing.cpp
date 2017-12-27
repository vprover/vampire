
/*
 * File Tracing.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Tracing.cpp
 * Implements class Tracing.
 */

#include "Debug/Tracer.hpp"

#include "Tracing.hpp"

namespace Api
{
/*
unsigned Tracing::s_traceStackDepth = 0;

void Tracing::enableTrace(vstring traceName, unsigned depth)
{
  CALL("Tracing::enableTrace");
  ENABLE_TAG_LIMITED(traceName.c_str(), depth);
}

void Tracing::processTraceString(vstring str)
{
  CALL("Tracing::processTraceString");
  PROCESS_TRACE_SPEC_STRING(str);
}

void Tracing::pushTracingState()
{
  CALL("Tracing::pushTracingState");

  PUSH_TAG_STATES();
  s_traceStackDepth++;
}

void Tracing::popTracingState()
{
  CALL("Tracing::popTracingState");

  if(s_traceStackDepth==0) {
    throw "No pushed tracing state left to be popped";
  }
  s_traceStackDepth--;
  POP_TAG_STATES();
}

void Tracing::displayHelp()
{
  CALL("Tracing::displayHelp");
  DISPLAY_HELP();
}
*/
}
