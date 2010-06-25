/**
 * @file Multiprocessing.cpp
 * Implements class Multiprocessing.
 */

#include <cerrno>

#include "Lib/Portability.hpp"

#if !COMPILER_MSVC

#include <sys/types.h>
#include <sys/wait.h>

#endif

#include "Lib/Environment.hpp"
#include "Lib/List.hpp"

#include "Multiprocessing.hpp"

namespace Lib
{
namespace Sys
{

Multiprocessing* Multiprocessing::instance()
{
  static Multiprocessing inst;
  return &inst;
}

Multiprocessing::Multiprocessing()
: _preFork(0), _postForkParent(0), _postForkChild(0)
{

}

Multiprocessing::~Multiprocessing()
{
  _preFork->destroy();
  _postForkParent->destroy();
  _postForkChild->destroy();
}

void Multiprocessing::registerForkHandlers(VoidFunc before, VoidFunc afterParent, VoidFunc afterChild)
{
  CALL("Multiprocessing::registerForkHandlers");
  if(before) {
    VoidFuncList::push(before, _preFork);
  }
  if(afterParent) {
    VoidFuncList::push(afterParent, _postForkParent);
  }
  if(afterChild) {
    VoidFuncList::push(afterChild, _postForkChild);
  }
}

void Multiprocessing::executeFuncList(VoidFuncList* lst)
{
  CALL("Multiprocessing::executeFuncList");

  VoidFuncList::Iterator fit(lst);
  while(fit.hasNext()) {
    VoidFunc func=fit.next();
    func();
  }
}


pid_t Multiprocessing::fork()
{
  CALL("Multiprocessing::fork");
  ASS(!env.haveOutput());

#if COMPILER_MSVC
  INVALID_OPERATION("fork() is not supported on Windows")
#else
  executeFuncList(_preFork);
  errno=0;
  pid_t res=::fork();
  if(res==-1) {
    SYSTEM_FAIL("Call to fork() function failed.", errno);
  }
  if(res==0) {
    executeFuncList(_postForkChild);
  }
  else {
    executeFuncList(_postForkParent);
  }
  return res;
#endif
}

/**
 * Wait for a first child process to terminate, return its pid and assign
 * its exit status into @b resValue. If the child was terminated by a signal,
 * assign into @b resValue the signal number increased by 256.
 */
pid_t Multiprocessing::waitForChildTermination(int& resValue)
{
  CALL("Multiprocessing::waitForChildTermination");

#if COMPILER_MSVC
  INVALID_OPERATION("waitid() is not supported on Windows")
#else

  siginfo_t si;

  errno=0;
  int res=waitid(P_ALL, 0, &si, WEXITED);
  if(res==-1) {
    SYSTEM_FAIL("Call to waitid() function failed.", errno);
  }

  if(si.si_code) {
    resValue=si.si_status;
  }
  else {
    resValue=si.si_status+256;
  }
  return si.si_pid;
#endif
}

}
}










