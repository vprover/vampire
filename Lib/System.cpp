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

#include <cerrno>
#include <string>
#include <csignal>
#include <iostream>

#include "Debug/Tracer.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
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
  using namespace Lib;

  static bool headerPrinted=false;

  if(inSpiderMode() && !headerPrinted) {
    headerPrinted=true;

    env.beginOutput();
    env.out() << status << " "
      << (Lib::env.options ? Lib::env.options->problemName() : "unknown") << " "
      << (Lib::env.timer ? Lib::env.timer->elapsedDeciseconds() : 0) << " "
      << (Lib::env.options ? Lib::env.options->testId() : "unknown") << "\n";
    env.endOutput();
  }
}

#if COMPILER_MSVC

#include <windows.h>

long long getTotalSystemMemory()
{
  MEMORYSTATUSEX status;
  GetMemoryStatusEx(&status);
  return status.ullTotalPhys;
}

unsigned Lib::System::getNumberOfCores()
{
  SYSTEM_INFO sysinfo;
  GetSystemInfo( &sysinfo );
  return sysinfo.dwNumberOfProcessors;
}

#else

#include <unistd.h>

long long Lib::System::getSystemMemory()
{
  long pages = sysconf(_SC_PHYS_PAGES);
  long page_size = sysconf(_SC_PAGE_SIZE);
  return static_cast<long long>(pages) * page_size;
}

unsigned Lib::System::getNumberOfCores()
{
  return sysconf( _SC_NPROCESSORS_ONLN );
}


#endif

namespace Lib {

using namespace std;
using namespace Shell;

/**
 * List of functions that will be called before Vampire terminates
 */
ZIArray<List<VoidFunc>*> System::s_onTerminationHandlers(2);

bool System::s_shouldIgnoreSIGINT = false;

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
  static bool haveSigInt = false;
  const char* signalDescription = signalToString(sigNum);

  if(sigNum==SIGHUP) {
    cout<<"SIGHUP received by "<<getpid()<<endl;
  }

  switch (sigNum)
    {
    case SIGTERM:
# ifndef _MSC_VER
    case SIGQUIT:
    case SIGXCPU:
      if (handled) {
	System::terminateImmediately(haveSigInt ? 3 : 2);
      }
      handled = true;
      if(outputAllowed()) {
	if(env.options) {
	  env.beginOutput();
	  env.out() << "Aborted by signal " << signalDescription << " on " << env.options->inputFile() << "\n";
	  env.endOutput();
	} else {
	  cout << "Aborted by signal " << signalDescription << "\n";
	}
      }
      return;
# endif

    case SIGINT:
      if(System::shouldIgnoreSIGINT()) {
	return;
      }
      haveSigInt=true;
//      exit(0);
//      return;

    case SIGILL:
    case SIGFPE:
    case SIGSEGV:

# ifndef _MSC_VER
    case SIGBUS:
    case SIGTRAP:
    case SIGHUP:
# endif
    case SIGABRT:
      {
	if (handled) {
	  System::terminateImmediately(haveSigInt ? 3 : 2);
	}
	reportSpiderFail();
	handled = true;
	if(outputAllowed()) {
	  if(env.options && env.statistics) {
	    env.beginOutput();
	    env.out() << "Aborted by signal " << signalDescription << " on " << env.options->inputFile() << "\n";
	    env.statistics->print(env.out());
#if VDEBUG
	    Debug::Tracer::printStack(env.out());
#endif
	    env.endOutput();
	  } else {
	    cout << "Aborted by signal " << signalDescription << "\n";
#if VDEBUG
	    Debug::Tracer::printStack(cout);
#endif
	  }
	}
	System::terminateImmediately(haveSigInt ? 3 : 2);
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

  errno=0;
  int res=atexit(onTermination);
  if(res==-1) {
    SYSTEM_FAIL("Call of atexit() function in System::setSignalHandlers failed.", errno);
  }
  ASS_EQ(res,0);
}

/**
 * Ensure that @b proc will be called before termination of the process.
 * Functions added with lower @b priority will be called first.
 *
 * We try to cover all possibilities how the process may terminate, but
 * some are probably impossible (such as receiving the signal 9). In these
 * cases the @b proc function is not called.
 */
void System::addTerminationHandler(VoidFunc proc, unsigned priority)
{
  CALL("System::addTerminationHandler");

  VoidFuncList::push(proc, s_onTerminationHandlers[priority]);
}

/**
 * This function should be called as the last thing on every path that leads
 * to a process termination.
 */
void System::onTermination()
{
  static bool called=false;
  if(called) {
    return;
  }
  called=true;

  size_t sz=s_onTerminationHandlers.size();
  for(size_t i=0;i<sz;i++) {
    while(s_onTerminationHandlers[i]) {
      VoidFunc func=VoidFuncList::pop(s_onTerminationHandlers[i]);
      func();
    }
  }
}

void System::terminateImmediately(int resultStatus)
{
  onTermination();
  _exit(resultStatus);
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
