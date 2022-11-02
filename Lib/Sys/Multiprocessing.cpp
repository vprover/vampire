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
 * @file Multiprocessing.cpp
 * Implements class Multiprocessing.
 */

#include <cerrno>

#include "Lib/Portability.hpp"

#include <csignal>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>

#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/Timer.hpp"

#include "Multiprocessing.hpp"
#include "Debug/TimeProfiling.hpp"

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
  VoidFuncList::destroy(_preFork);
  VoidFuncList::destroy(_postForkParent);
  VoidFuncList::destroy(_postForkChild);
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
}

/**
 * Wait for a first child process to terminate, return its pid and assign
 * its exit status into @b resValue. If the child was terminated by a signal,
 * assign into @b resValue the signal number increased by 256.
 */
pid_t Multiprocessing::waitForChildTermination(int& resValue)
{
  CALL("Multiprocessing::waitForChildTermination");
  TIME_TRACE("waiting for child")

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
}

void Multiprocessing::kill(pid_t child, int signal)
{
  CALL("Multiprocessing::kill");

  int res = ::kill(child, signal);
  if(res!=0) {
    ASS_EQ(res,-1);
    SYSTEM_FAIL("Call to kill() function failed.", errno);
  }
}

void Multiprocessing::killNoCheck(pid_t child, int signal)
{
  CALL("Multiprocessing::killNoCheck");
  ::kill(child, signal);
}

pid_t Multiprocessing::poll_children(bool &exited, bool &signalled, int &code)
{
  CALL("Multiprocessing::poll_child");

  int status;
  pid_t pid = waitpid(-1 /*wait for any child*/, &status, WUNTRACED);

  if (pid == -1) {
    SYSTEM_FAIL("Call to waitpid() function failed.", errno);
  }

  exited = WIFEXITED(status);
  signalled = WIFSIGNALED(status);
  if(exited)
  {
    code = WEXITSTATUS(status);
  }
  if(signalled)
  {
    code = WTERMSIG(status);
  }
  return pid;
}

}
}
