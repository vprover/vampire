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

#include <cerrno> // errno
#include <csignal> // kill
#include <unistd.h> // fork
#include <sys/wait.h> // waitpid

#include "Debug/Assertion.hpp"
#include "Lib/Exception.hpp"

#include "Multiprocessing.hpp"

namespace Lib
{
namespace Sys
{

pid_t fork()
{
  errno=0;
  pid_t res=::fork();
  if(res==-1) {
    SYSTEM_FAIL("Call to fork() function failed.", errno);
  }
  return res;
}

void kill(pid_t child, int signal)
{
  int res = ::kill(child, signal);
  if(res!=0) {
    ASS_EQ(res,-1);
    SYSTEM_FAIL("Call to kill() function failed.", errno);
  }
}

Headstone waitForChildTermination(pid_t query)
{
  int status;
  pid_t pid = waitpid(query, &status, 0);

  if (pid == -1) {
    SYSTEM_FAIL("Call to waitpid() function failed.", errno);
  }

  // PID 0 and 1 are unlikely!
  ASS_G(pid, 1)
  bool exited = WIFEXITED(status), signalled = WIFSIGNALED(status);
  // child should actually have changed state,
  // and these are mutually-exclusive conditions
  ASS_NEQ(WIFEXITED(status), WIFSIGNALED(status))

  int code = exited ? WEXITSTATUS(status) : WTERMSIG(status);
  return { pid, signalled, code };
}

}
}
