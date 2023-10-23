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
 * @file Tracing.cpp
 * Implements class Tracing.
 */


#include "Tracing.hpp"

namespace Api
{
/*
unsigned Tracing::s_traceStackDepth = 0;

void Tracing::enableTrace(vstring traceName, unsigned depth)
{
  ENABLE_TAG_LIMITED(traceName.c_str(), depth);
}

void Tracing::processTraceString(vstring str)
{
  PROCESS_TRACE_SPEC_STRING(str);
}

void Tracing::pushTracingState()
{
  PUSH_TAG_STATES();
  s_traceStackDepth++;
}

void Tracing::popTracingState()
{
  if(s_traceStackDepth==0) {
    throw "No pushed tracing state left to be popped";
  }
  s_traceStackDepth--;
  POP_TAG_STATES();
}

void Tracing::displayHelp()
{
  DISPLAY_HELP();
}
*/
}
