/**
 * @file System.cpp
 * Wrappers of some system functions and methods that take care of the
 * system stuff and don't fit anywhere else (handling signals etc...)
 */

#include "Portability.hpp"

#include <stdlib.h>
#ifdef _MSC_VER
#  include <Winsock2.h>
#  include <process.h>
#else
#  include <unistd.h>
#endif

#include <string>
#include <csignal>
#include <iostream>

#include "Debug/Tracer.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Timer.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "System.hpp"

bool outputAllowed()
{
#if VDEBUG
  return true;
#else
  return !Lib::env.options || Lib::env.options->mode()!=Shell::Options::MODE_SPIDER;
#endif
}

bool inSpiderMode()
{
  return Lib::env.options && Lib::env.options->mode()==Shell::Options::MODE_SPIDER;
}

void reportSpiderFail()
{
  reportSpiderStatus('!');
}

void reportSpiderStatus(char status)
{
  static bool headerPrinted=false;

  if(inSpiderMode() && !headerPrinted) {
    headerPrinted=true;

    Lib::env.out << status << " ";
    Lib::env.out << (Lib::env.options ? Lib::env.options->problemName() : "unknown") << " ";
    Lib::env.out << (Lib::env.timer ? Lib::env.timer->elapsedDeciseconds() : 0) << " ";
    Lib::env.out << (Lib::env.options ? Lib::env.options->testId() : "unknown") << "\n";
  }
}

namespace Lib {

using namespace std;
using namespace Shell;

///**
// * Reimplements the system gethostname function.
// * @since 31/03/2005 Torrevieja
// */
//void System::gethostname(char* hostname,int maxlength)
//{
//  ::gethostname(hostname,maxlength);
//}

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


/**
 * Signal handling function. Rewritten from the kernel standalone.
 *
 * @param sigNum signal number
 * @since 28/06/2003 Manchester, statistics result registration added
 */
void handleSignal (int sigNum)
{
  // true if a terminal signal has been handled already.
  // to avoid catching signals over and over again
  static bool handled = false;
  const char* signalDescription = signalToString(sigNum);

  switch (sigNum)
    {
    case SIGTERM:
# ifndef _MSC_VER
    case SIGQUIT:
    case SIGHUP:
    case SIGXCPU:
      if (handled) {
	exit(0);
      }
      handled = true;
      if(outputAllowed()) {
	if(env.options) {
	  env.out << "Aborted by signal " << signalDescription << " on " << env.options->inputFile() << "\n";
	} else {
	  cout << "Aborted by signal " << signalDescription << "\n";
	}
      }
      return;
# endif

    case SIGINT:
//      exit(0);
//      return;

    case SIGILL:
    case SIGFPE:
    case SIGSEGV:

# ifndef _MSC_VER
    case SIGBUS:
    case SIGTRAP:
# endif
    case SIGABRT:
      {
	if (handled) {
	  exit(0);
	}
	reportSpiderFail();
	handled = true;
	if(outputAllowed()) {
	  if(env.options && env.statistics) {
	    env.out << "Aborted by signal " << signalDescription << " on " << env.options->inputFile() << "\n";
	    env.statistics->print();
	  } else {
	    cout << "Aborted by signal " << signalDescription << "\n";
	  }
#if VDEBUG
	  Debug::Tracer::printStack(cout);
#endif
	}
	exit(0);
	return;
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
  //TODO: disabled to make abort() terminate the execution immediately (needed for CASC)
//  signal(SIGABRT,handleSignal);

#ifndef _MSC_VER
  signal(SIGQUIT,handleSignal);
  signal(SIGHUP,handleSignal);
  signal(SIGXCPU,handleSignal);
  signal(SIGBUS,handleSignal);
  signal(SIGTRAP,handleSignal);
#endif
}

string System::extractFileNameFromPath(string str)
{
  size_t index=str.find_last_of("\\/")+1;
  if(index==string::npos) {
    return str;
  }
  return string(str, index);
}

};
