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

#include "Portability.hpp"

#include <cstdlib>
#  include <unistd.h>
#  if !__APPLE__ && !__CYGWIN__
#    include <sys/prctl.h>
#  endif

#include <dirent.h>

#include <cerrno>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <fstream>
#include <thread>

#include "Debug/Tracer.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "Environment.hpp"
#include "Exception.hpp"
#include "Int.hpp"
#include "Stack.hpp"
#include "Timer.hpp"
#include "VString.hpp"

#include "System.hpp"

#include <unistd.h>

long long Lib::System::getSystemMemory()
{
#if __APPLE__ || __CYGWIN__
  NOT_IMPLEMENTED;
#else
  long pages = sysconf(_SC_PHYS_PAGES);
  long page_size = sysconf(_SC_PAGE_SIZE);
  return static_cast<long long>(pages) * page_size;
#endif
}

unsigned Lib::System::getNumberOfCores()
{
  return std::thread::hardware_concurrency();
}

namespace Lib {

using namespace std;
using namespace Shell;

bool System::s_shouldIgnoreSIGINT = false;
bool System::s_shouldIgnoreSIGHUP = false;
const char* System::s_argv0 = 0;

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
  CALL("System::handleSignal");

  // true if a terminal signal has been handled already.
  // to avoid catching signals over and over again
  static bool handled = false;
  static bool haveSigInt = false;
  const char* signalDescription = signalToString(sigNum);

  switch (sigNum)
    {
    case SIGTERM:
# ifndef _MSC_VER
    case SIGQUIT:
      if (handled) {
	System::terminateImmediately(haveSigInt ? VAMP_RESULT_STATUS_SIGINT : VAMP_RESULT_STATUS_OTHER_SIGNAL);
      }
      handled = true;
      if(outputAllowed(true)) {
	if(env.options) {
	  env.beginOutput();
	  env.out() << "Aborted by signal " << signalDescription << " on " << env.options->inputFile() << "\n";
	  env.endOutput();
	} else {
	  cout << "Aborted by signal " << signalDescription << "\n";
	}
      }
      return;
    case SIGXCPU:
      if(outputAllowed(true)) {
	if(env.options) {
	  env.beginOutput();
	  env.out() << "External time out (SIGXCPU) on " << env.options->inputFile() << "\n";
	  env.endOutput();
	} else {
	  cout << "External time out (SIGXCPU)\n";
	}
      }
      System::terminateImmediately(VAMP_RESULT_STATUS_OTHER_SIGNAL);
      break;
# endif

    case SIGINT:
      if(System::shouldIgnoreSIGINT()) {
	return;
      }
      haveSigInt=true;
//      exit(0);
//      return;

    case SIGHUP:
      if(System::shouldIgnoreSIGHUP()) {
  return;
      }
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
	  System::terminateImmediately(haveSigInt ? VAMP_RESULT_STATUS_SIGINT : VAMP_RESULT_STATUS_OTHER_SIGNAL);
	}
	reportSpiderFail();
	handled = true;
	if(outputAllowed()) {
	  if(env.options && env.statistics) {
	    env.beginOutput();
	    env.out() << getpid() << " Aborted by signal " << signalDescription << " on " << env.options->inputFile() << "\n";
	    env.statistics->print(env.out());
#if VDEBUG
	    Debug::Tracer::printStack(env.out());
#endif
	    env.endOutput();
	  } else {
	    cout << getpid() << "Aborted by signal " << signalDescription << "\n";
#if VDEBUG
	    Debug::Tracer::printStack(cout);
#endif
	  }
	}
	System::terminateImmediately(haveSigInt ? VAMP_RESULT_STATUS_SIGINT : VAMP_RESULT_STATUS_OTHER_SIGNAL);
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
  // ensure that termination handlers are created _before_ the atexit() call
  // C++ then guarantees that the array is destructed _after_ onTermination
  terminationHandlersArray();
  int res=atexit(onTermination);
  if(res==-1) {
    SYSTEM_FAIL("Call of atexit() function in System::setSignalHandlers failed.", errno);
  }
  ASS_EQ(res,0);
}

/**
 * Function that returns a reference to an array that contains
 * lists of termination handlers
 *
 * Using a function with a static variable inside is a way to ensure
 * that no matter how early we want to register a termination
 * handler, the array will be constructed.
 */
ZIArray<List<VoidFunc>*>& System::terminationHandlersArray()
{
  CALL("System::initializationHandlersArray");

  static ZIArray<List<VoidFunc>*> arr(2);
  return arr;
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

  VoidFuncList::push(proc, terminationHandlersArray()[priority]);
}

/**
 * This function should be called as the last thing on every path that leads
 * to a process termination.
 */
void System::onTermination()
{
  CALL("System::onTermination");

  static bool called=false;
  if(called) {
    return;
  }
  called=true;

  auto handlers = terminationHandlersArray();
  size_t sz=handlers.size();
  for(size_t i=0;i<sz;i++) {
    VoidFuncList::Iterator thIter(handlers[i]);
    while(thIter.hasNext()) {
      VoidFunc func=thIter.next();
      func();
    }
  }
}

void System::terminateImmediately(int resultStatus)
{
  CALL("System::terminateImmediately");

  onTermination();
  _exit(resultStatus);
}

/**
 * Make sure that the process will receive the SIGHUP signal
 * when its parent process dies
 *
 * This setting is not passed to the child processes created by fork().
 */
void System::registerForSIGHUPOnParentDeath()
{
#if __APPLE__ || __CYGWIN__
  // cerr<<"Death of parent process not being handled on Mac and Windows"<<endl;
  // NOT_IMPLEMENTED;
#else
  prctl(PR_SET_PDEATHSIG, SIGHUP);
#endif
}

/**
 * Read command line arguments into @c res and register the executable name
 * (0-th element of @c argv) using the @c registerArgv0() function.
 */
void System::readCmdArgs(int argc, char* argv[], StringStack& res)
{
  CALL("System::readCmdArgs");
  ASS_GE(argc,1);
  ASS(res.isEmpty()); //just to avoid any confusion, if it causes problems, the assumption can be removed

  registerArgv0(argv[0]);
  for(int i=1; i<argc; i++) {
    res.push(argv[i]);
  }
}

vstring System::extractFileNameFromPath(vstring str)
{
  CALL("System::extractFileNameFromPath");

  size_t index=str.find_last_of("\\/")+1;
  if(index==vstring::npos) {
    return str;
  }
  return vstring(str, index);
}

/**
 * If directory name can be extracted from @c path, assign it into
 * @c dir and return true; otherwise return false.
 *
 * The directory name is extracted without the final '/'.
 */
bool System::extractDirNameFromPath(vstring path, vstring& dir)
{
  CALL("System::extractDirNameFromPath");

  size_t index=path.find_last_of("\\/");
  if(index==vstring::npos) {
    return false;
  }
  dir = path.substr(0, index);
  return true;
}

bool System::fileExists(vstring fname)
{
  CALL("System::fileExists");
  BYPASSING_ALLOCATOR;

  ifstream ifile(fname.c_str());
  return ifile.good();
}

/**
 * Guess path to the current executable.
 *
 * Guessing means that the returned path might not be correct.
 */
vstring System::guessExecutableDirectory()
{
  CALL("System::guessExecutableDirectory");

  vstring res;

  if(s_argv0 && extractDirNameFromPath(s_argv0, res)) {
    return res;
  }

  return ".";
}

/**
 * Guess the current executable file.
 *
 * Guessing means that the returned file path might not be correct.
 */
vstring System::guessExecutableName()
{
  CALL("System::guessExecutableName");

  vstring res;

  if(s_argv0) {
    return s_argv0;
  }

  return "./vampire";
}

pid_t System::getPID()
{
  CALL("System::getPID");

  return getpid();
}

void System::readDir(vstring dirName, Stack<vstring>& filenames)
{
  CALL("System::readDir");

  DIR *dirp;
  struct dirent *dp;

  static Stack<vstring> todo;
  ASS(todo.isEmpty());
  todo.push(dirName);

  while (todo.isNonEmpty()) {
    vstring dir = todo.pop();

    dirp = opendir(dir.c_str());
    
    if (!dirp) {
      // cout << "Cannot open dir " << dir << endl;
      continue;
    }
    
    while ((dp = readdir(dirp)) != NULL) {
      if (strncmp(dp->d_name, ".", 1) == 0) {
        continue;
      }
      if (strncmp(dp->d_name, "..", 2) == 0) {
        continue;
      }

      switch (dp->d_type) {
        case DT_REG:
          filenames.push(dir+"/"+dp->d_name);
          break;
        case DT_DIR:
          // cout << "seen dir " << dp->d_name << endl;
          todo.push(dir+"/"+dp->d_name);
          break;
        default:
          ;
          // cout << "weird file type" << endl;
      }
    }
    (void)closedir(dirp);
  }

  todo.reset();
}

/**
 * Execute command @c command, pass content of @c input as standard input
 * and return the output of the command in @c output.
 */
int System::executeCommand(vstring command, vstring input, Stack<vstring>& outputLines)
{
  CALL("System::executeCommand");

  vstring pidStr = Int::toString(getPID());
  vstring inFile  = "/tmp/vampire_executeCommand_"+pidStr+"_in";
  vstring outFile = "/tmp/vampire_executeCommand_"+pidStr+"_out";

  vstring cmdLine = command + " <" + inFile + " >" + outFile;

  {
    BYPASSING_ALLOCATOR;

    ofstream inpFile(inFile.c_str());
    inpFile << input;
    inpFile.close();
  }

  int resStatus=system(cmdLine.c_str());

  {
    BYPASSING_ALLOCATOR;

    outputLines.reset();
    vstring line;
    ifstream outpFile(outFile.c_str());
    while (getline(outpFile, line)) {
      outputLines.push(line);
    }
    outpFile.close();
  }

//  if(WIFSIGNALED(resStatus) && WTERMSIG(resStatus)==SIGINT) {
//    //if child Vampire was terminated by SIGINT (Ctrl+C), we also terminate
//    //(3 is the return value for this case; see documentation for the
//    //@b vampireReturnValue global variable)
//    handleSIGINT();
//  }

  remove(inFile.c_str());
  remove(outFile.c_str());

  if(WIFEXITED(resStatus)) {
    return WEXITSTATUS(resStatus);
  }
  else if(WIFSIGNALED(resStatus)) {
    return -WTERMSIG(resStatus);
  }
  else {
    return -0xffff;
  }
}

};
