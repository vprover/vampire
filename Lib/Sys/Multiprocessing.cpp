/**
 * @file Multiprocessing.cpp
 * Implements class Multiprocessing.
 */

#include <cerrno>

#include "Lib/Portability.hpp"

#if !COMPILER_MSVC

#include <signal.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>

#endif

#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/Timer.hpp"

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
  ASS(!env -> haveOutput());

#if COMPILER_MSVC
  INVALID_OPERATION("fork() is not supported on Windows");
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
  INVALID_OPERATION("waitpid() is not supported on Windows");
#else

  int status;
  pid_t childPid;

  do {
    errno=0;
    childPid = wait(&status);
    if(childPid==-1) {
      SYSTEM_FAIL("Call to wait() function failed.", errno);
    }
  } while(WIFSTOPPED(status));

  if(WIFEXITED(status)) {
    resValue = WEXITSTATUS(status);
  }
  else {
    ASS(WIFSIGNALED(status));
    resValue = WTERMSIG(status)+256;
  }
  return childPid;
#endif
}

/**
 * Wait for termination of a child or until timeMs elapses. If the later happens,
 * return 0 instead of process pid.
 */
pid_t Multiprocessing::waitForChildTerminationOrTime(unsigned timeMs,int& resValue)
{
  CALL("Multiprocessing::waitForChildTerminationOrTime");

#if COMPILER_MSVC
  INVALID_OPERATION("waitpid() is not supported on Windows");
#else

  int status;
  pid_t childPid;

  int dueTime = env -> timer->elapsedMilliseconds()+timeMs;

  for(;;) {
    errno=0;
    childPid = waitpid(WAIT_ANY,&status,WNOHANG);
    if(childPid==-1) {
      SYSTEM_FAIL("Call to waitpid() function failed.", errno);
    }
    if(childPid==0) {
      if(dueTime<=env -> timer->elapsedMilliseconds()) {
	return 0;
      }
      sleep(50);
      continue;
    }
    else {
      if(!WIFSTOPPED(status)) {
	break;
      }
    }
  }

  if(WIFEXITED(status)) {
    resValue = WEXITSTATUS(status);
  }
  else {
    ASS(WIFSIGNALED(status));
    resValue = WTERMSIG(status)+256;
  }
  return childPid;
#endif
}

/**
 * Wait for a first child process to terminate, return its pid and assign
 * its exit status into @b resValue. If the child was terminated by a signal,
 * assign into @b resValue the signal number increased by 256.
 */
void Multiprocessing::waitForParticularChildTermination(pid_t child, int& resValue)
{
  CALL("Multiprocessing::waitForChildTermination");

#if COMPILER_MSVC
  INVALID_OPERATION("waitpid() is not supported on Windows");
#else

  int status;

  do {
    errno=0;
    int res=waitpid(child, &status, 0);
    if(res==-1) {
      SYSTEM_FAIL("Call to waitpid() function failed.", errno);
    }
    ASS_EQ(res,child);
  } while(WIFSTOPPED(status));

  if(WIFEXITED(status)) {
    resValue = WEXITSTATUS(status);
  }
  else {
    ASS(WIFSIGNALED(status));
    resValue = WTERMSIG(status)+256;
  }
#endif
}

void Multiprocessing::sleep(unsigned ms)
{
  CALL("Multiprocessing::sleep");

#if COMPILER_MSVC
  INVALID_OPERATION("sleep() is not supported on Windows");
#else

  timespec init;
  timespec ts;
  timespec remaining;
  init.tv_nsec = (ms%1000)*1000000;
  init.tv_sec = ms/1000;
  ts = init;
  for(;;) {
    int res = nanosleep(&ts, &remaining);
    if(!res || remaining.tv_sec>init.tv_sec) { //the latter statement covers remaining time underflow
      return;
    }
    ASS_EQ(res,-1);
    if(errno!=EINTR) {
      SYSTEM_FAIL("Call to nanosleep() function failed.", errno);
    }
    ts = remaining;
  }
#endif
}

void Multiprocessing::kill(pid_t child, int signal)
{
  CALL("Multiprocessing::kill");

#if COMPILER_MSVC
  INVALID_OPERATION("kill() is not supported on Windows");
#else
  int res = ::kill(child, signal);
  if(res!=0) {
    ASS_EQ(res,-1);
    SYSTEM_FAIL("Call to kill() function failed.", errno);
  }
#endif
}

}
}










