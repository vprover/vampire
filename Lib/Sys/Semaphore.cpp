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
 * @file Semaphore.cpp
 * Implements class Semaphore.
 */

#include "Lib/Portability.hpp"

#include <cerrno>
#include <cstdlib>
#include <unistd.h>
#include <sys/types.h>
#include <sys/ipc.h>
#include <sys/sem.h>

#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"
#include "Lib/List.hpp"
#include "Lib/System.hpp"

#include "Multiprocessing.hpp"

#include "Semaphore.hpp"

namespace Lib
{
namespace Sys
{

/**
 * List of all Semaphore objects, so that the reference counters of the
 * OS semaphores can be updated after a fork
 */
Semaphore::SemaphoreList* Semaphore::s_instances = 0;

/**
 * Creates Semaphore object with @b num semaphores
 *
 * Actually @b num+2 semaphore OS object is created. The @b num-th semaphore
 * is used to determine when there is noone else using the OS semaphore,
 * so that the semaphore can be deleted in the destructor. The @b (num+1)-th
 * semaphore is used to protect the destructor, so we don't have resource
 * leaks on unfavourable scheduling.
 */
Semaphore::Semaphore(int num)
:semCnt(num)
{
  CALL("Semaphore::Semaphore(int)");
  ASS_G(num,0);

  ensureEventHandlersInstalled();

  bool retrying=false;
get_retry:
  errno=0;
  semid=semget(IPC_PRIVATE, semCnt+2, 0600);
  if(semid==-1 && errno==ENOSPC && !retrying) {
    retrying=true;
    system("ipcs -s | grep 0x00000000 | cut -d' ' -f2|xargs -n 1 ipcrm -s");
    goto get_retry;
  }
  if(semid==-1) {
    SYSTEM_FAIL("Cannot create semaphore.",errno);
  }

  //initialize the semaphores
  unsigned short semVals[semCnt+2];
  for(int i=0;i<=semCnt;i++) {
    semVals[i]=0;
  }
  semVals[semCnt+1]=1;

  semun arg;
  arg.array=semVals;

  errno=0;
  int res=semctl(semid, num, SETALL, arg);
  if(res==-1) {
    SYSTEM_FAIL("Cannot set initial semaphore values.",errno);
  }
  ASS_EQ(res,0);

  registerInstance();
}

Semaphore::~Semaphore()
{
  CALL("Semaphore::~Semaphore");

  deregisterInstance();
}

Semaphore::Semaphore(const Semaphore& s)
{
  CALL("Semaphore::Semaphore(const Semaphore&)");

  semid=s.semid;
  semCnt=s.semCnt;
  registerInstance();
}

const Semaphore& Semaphore::operator=(const Semaphore& s)
{
  CALL("Semaphore::operator=");

  deregisterInstance();
  semid=s.semid;
  semCnt=s.semCnt;
  registerInstance();
  return *this;
}

/**
 * Internal version of a semaphore manipulation function that
 * allows accessing the internal semaphores as well.
 */
void Semaphore::doInc(int num)
{
  CALL("Semaphore::doInc");
  ASS(hasSemaphore());
  ASS_L(num, semCnt+2);

  sembuf buf;
  buf.sem_num=num;
  buf.sem_op=1;
  buf.sem_flg=SEM_UNDO;

  errno=0;
  int res=semop(semid, &buf, 1);
  if(res==-1) {
    SYSTEM_FAIL("Cannot increase semaphore.",errno);
  }
}

/**
 *  * Internal version of a semaphore manipulation function that
 *   * allows accessing the internal semaphores as well.
 *    */
void Semaphore::doIncPersistent(int num)
{
  CALL("Semaphore::doIncPersistent");
  ASS(hasSemaphore());
  ASS_L(num, semCnt+2);

  sembuf buf;
  buf.sem_num=num;
  buf.sem_op=1;
  buf.sem_flg=0;

  errno=0;
  int res=semop(semid, &buf, 1);
  if(res==-1) {
    SYSTEM_FAIL("Cannot increase semaphore.",errno);
  }
}

/**
 * Internal version of a semaphore manipulation function that
 * allows accessing the internal semaphores as well.
 */
void Semaphore::doDec(int num)
{
  CALL("Semaphore::doDec");
  ASS(hasSemaphore());
  ASS_L(num, semCnt+2);

  sembuf buf;
  buf.sem_num=num;
  buf.sem_op=-1;
  buf.sem_flg=SEM_UNDO;

retry_decreasing:
  errno=0;
  int res=semop(semid, &buf, 1);
  if(res==-1 && errno==EINTR) {
    //we just received a signal -- now we can continue waiting
    goto retry_decreasing;
  }
  if(res==-1) {
    SYSTEM_FAIL("Cannot decrease semaphore.",errno);
  }
}

/**
 * Internal version of a semaphore manipulation function that
 * allows accessing the internal semaphores as well.
 */
void Semaphore::doSet(int num, int val)
{
  CALL("Semaphore::doSet");
  ASS(hasSemaphore());
  ASS_L(num, semCnt+2);
  ASS_GE(val,0); //semaphores cannot be negative

  semun arg;
  arg.val=val;

  errno=0;
  int res=semctl(semid, num, SETVAL, arg);
  if(res==-1) {
    SYSTEM_FAIL("Cannot set the semaphore value.",errno);
  }
}

/**
 * Internal version of a semaphore manipulation function that
 * allows accessing the internal semaphores as well.
 */
int Semaphore::doGet(int num)
{
  CALL("Semaphore::doGet");
  ASS(hasSemaphore());
  ASS_L(num, semCnt+2);

  semun unused_arg;

  errno=0;
  int res=semctl(semid, num, GETVAL, unused_arg);
  if(res==-1) {
    SYSTEM_FAIL("Cannot get the semaphore value.",errno);
  }
  ASS_GE(res,0);
  return res;
}

/**
 * Increase the value of the semaphore number @b num
 */
void Semaphore::inc(int num)
{
  CALL("Semaphore::inc");
  ASS(hasSemaphore());
  ASS_L(num, semCnt);

  doInc(num);
}

/**
 *  * Increase the value of the semaphore number @b num
 *   */
void Semaphore::incp(int num)
{
  CALL("Semaphore::incp");
  ASS(hasSemaphore());
  ASS_L(num, semCnt);

  doIncPersistent(num);
}

/**
 * If the value of the semaphore number @b num is greater than
 * zero, decrease it and return immediately. Otherwise wait until
 * it becomes greater than zero and decrease it then.
 */
void Semaphore::dec(int num)
{
  CALL("Semaphore::dec");
  ASS(hasSemaphore());
  ASS_L(num, semCnt);

  doDec(num);
}

/**
 * Return the value of the semaphore number @b num
 */
int Semaphore::get(int num)
{
  CALL("Semaphore::get");
  ASS(hasSemaphore());
  ASS_L(num, semCnt);

  return doGet(num);
}

/**
 * Return the value of the semaphore number @b num
 */
void Semaphore::set(int num, int val)
{
  CALL("Semaphore::set");
  ASS(hasSemaphore());
  ASS_L(num, semCnt);
  ASS_GE(val, 0);

  doSet(num, val);
}

/**
 * Return true iff this Semaphore object is the only object that
 * has access to its semaphores
 */
bool Semaphore::isLastInstance()
{
  CALL("Semaphore::isLastInstance");
  ASS(hasSemaphore());

  return doGet(semCnt)==1;
}
/**
 * If linked to an OS semaphore, increase its reference counter, and
 * if @b addToInstanceList is true, add itself into the @b s_instances list
 *
 * @b addToInstanceList is false in case case we call the function for a fork
 * handler, because in that case the semaphore is already in the @b s_instances
 * list.
 */
void Semaphore::registerInstance(bool addToInstanceList)
{
  CALL("Semaphore::registerInstance");

  if(!hasSemaphore()) {
    return;
  }

  acquireInstance();

  if(addToInstanceList) {
    SemaphoreList::push(this, s_instances);
  }
}

/**
 * If linked to an OS semaphore, decrease its reference counter, and
 * if @b addToInstanceList is true, add itself into the @b s_instances list
 */
void Semaphore::deregisterInstance()
{
  CALL("Semaphore::deregisterInstance");

  if(!hasSemaphore()) {
    return;
  }
  ASS(SemaphoreList::member(this, s_instances));
  s_instances = SemaphoreList::remove(this, s_instances);

  releaseInstance();
}

/**
 * Increase reference counter of linked OS semaphore
 */
void Semaphore::acquireInstance()
{
  CALL("Semaphore::acquireInstance");
  ASS(hasSemaphore());

  doInc(semCnt);
}

/**
 * Decrease reference counter of linked OS semaphore, and
 * if @b addToInstanceList is true, add itself into the @b s_instances list
 */
void Semaphore::releaseInstance()
{
  CALL("Semaphore::releaseInstance");
  ASS(hasSemaphore());

  //Here we may wait until other deregisterInstance() calls finish.
  //There is no need to wait for calls to registerInstance() function,
  //as we only need to avoid race conditions with decreasing of the
  //semaphore.
  doDec(semCnt+1);

  ASS_G(doGet(semCnt), 0);
  doDec(semCnt);

  if(doGet(semCnt)==0) {
    semun unused_arg;
    errno=0;
    int res=semctl(semid, 1, IPC_RMID, unused_arg);
    if(res==-1) {
      SYSTEM_FAIL("Cannot destroy semaphore.",errno);
    }
    ASS_EQ(res,0);
  }
  else {
    //if we didn't delete the semaphore, we now allow other destructors to proceed
    doInc(semCnt+1);
  }
}

/**
 * Release all semaphores held by this process
 *
 * This function should be called when we are exitting the process
 * in some manner that does not lead to calling destructors (e.g. the
 * @b abort() function).
 */
void Semaphore::releaseAllSemaphores()
{
  CALL("Semaphore::releaseAllSemaphores");

  SemaphoreList* instIter=s_instances;
  while(instIter) {
    Semaphore* s=instIter->head();
    if(s->semid!=-1) {
      s->releaseInstance();
    }
    s->semid=-1;
    instIter=instIter->tail();
  }
}


/**
 * A handler that updates semaphore reference counter after
 * each fork operation
 */
void Semaphore::postForkInChild()
{
  CALL("Semaphore::postForkInChild");

  SemaphoreList::Iterator sit(s_instances);
  while(sit.hasNext()) {
    Semaphore* s=sit.next();
    s->acquireInstance();
  }
}

/**
 * Ensure a handler that will update semaphore reference counter after
 * a fork operation is installed
 */
void Semaphore::ensureEventHandlersInstalled()
{
  CALL("Semaphore::ensureForkHandlerInstalled");

  static bool installed=false;
  if(installed) {
    return;
  }
  Multiprocessing::instance()->registerForkHandlers(0,0,postForkInChild);
  //this termination handler must be called after the termination handler
  //of the SyncPipe class
  System::addTerminationHandler(releaseAllSemaphores,1);
  installed=true;
}

}
}


