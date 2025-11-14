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
 * @file System.cpp
 * Wrappers of some system functions and methods that take care of the
 * system stuff and don't fit anywhere else (handling signals etc...)
 */

#include <csignal>

#ifdef __linux__
#include <sys/prctl.h>
#endif

#include "Debug/Tracer.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "Environment.hpp"

#include "System.hpp"

namespace Lib {

const char* signalToString (int sigNum)
{
  switch (sigNum)
    {
    case SIGTERM:
      return "SIGTERM";
# ifndef _MSC_VER
    case SIGQUIT:
      return "SIGQUIT";
    case SIGHUP:
      return "SIGHUP";
    case SIGXCPU:
      return "SIGXCPU";
    case SIGBUS:
      return "SIGBUS";
    case SIGTRAP:
      return "SIGTRAP";
# endif
    case SIGINT:
      return "SIGINT";
    case SIGILL:
      return "SIGILL";
    case SIGFPE:
      return "SIGFPE";
    case SIGSEGV:
      return "SIGSEGV";
    case SIGABRT:
      return "SIGABRT";
    default:
      return "UNKNOWN SIGNAL";
    }
} // signalToString


// true if a terminal signal has been handled already,
// avoids catching signals over and over again
static std::sig_atomic_t TERMINAL_SIGNAL_HANDLED = false;

/**
 * Signal handling function. Rewritten from the kernel standalone.
 *
 * @param sigNum signal number
 * @since 28/06/2003 Manchester, statistics result registration added
 * @since 10/04/2024 Oxford, simplify
 */
void handleSignal (int sigNum)
{
  if(TERMINAL_SIGNAL_HANDLED)
    return;

  switch(sigNum) {
  // polite non-crashing interrupts, shut up and exit immediately
  case SIGINT:
  case SIGTERM:
#ifndef _MSC_VER
  case SIGHUP:
  case SIGXCPU:
#endif
    TERMINAL_SIGNAL_HANDLED = true;
    System::terminateImmediately(VAMP_RESULT_STATUS_INTERRUPTED);

  // crashy or impolite interrupts, complain about it
  case SIGABRT:
  case SIGFPE:
  case SIGILL:
  case SIGSEGV:
#ifndef _MSC_VER
  case SIGQUIT:
  case SIGBUS:
#endif
    // following is not standards-compliant as it calls functions that are not permitted in signal handlers
    // but we're dying anyway, so try our best to report something
    TERMINAL_SIGNAL_HANDLED = true;
    Shell::reportSpiderFail();
    if(Shell::outputAllowed(true)) {
      Shell::addCommentSignForSZS(std::cout);
      std::cout << "Aborted by signal " << signalToString(sigNum);
      if(env.options)
        std::cout << " on " << env.options->inputFile();
      std::cout << std::endl;
      if (!Shell::UIHelper::portfolioParent) {
        if(env.statistics)
          env.statistics->print(std::cout);
        Debug::Tracer::printStack();
      }
      System::terminateImmediately(VAMP_RESULT_STATUS_OTHER_SIGNAL);
    }
  default:
    break;
  }
} // handleSignal

void System::setSignalHandlers()
{
  signal(SIGTERM,handleSignal);
  signal(SIGINT,handleSignal);
  signal(SIGILL,handleSignal);
  signal(SIGFPE,handleSignal);
  signal(SIGSEGV,handleSignal);
  signal(SIGABRT,handleSignal);

#ifndef _MSC_VER
  signal(SIGQUIT,handleSignal);
  signal(SIGHUP,handleSignal);
  signal(SIGXCPU,handleSignal);
  signal(SIGBUS,handleSignal);
  signal(SIGTRAP,handleSignal);
#endif
}

/**
 * Make sure that the process will receive the SIGHUP signal
 * when its parent process dies
 *
 * This setting is not passed to the child processes created by fork().
 */
void System::registerForSIGHUPOnParentDeath()
{
#ifdef __linux__
  prctl(PR_SET_PDEATHSIG, SIGHUP);
#endif
}

};
