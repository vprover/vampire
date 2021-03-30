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
 * @file SyncPipe.cpp
 * Implements class SyncPipe.
 */

#include "Lib/Portability.hpp"

#include <cerrno>
#include <unistd.h>

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/fdstream.hpp"
#include "Lib/List.hpp"
#include "Lib/System.hpp"

#include "Multiprocessing.hpp"

#include "SyncPipe.hpp"

namespace Lib
{
namespace Sys
{

SyncPipe::PipeList* SyncPipe::s_instances = 0;

SyncPipe::SyncPipe()
: _isReading(false), _isWriting(false), _syncSemaphore(3)
{
  ensureEventHandlersInstalled();

  int fd[2];
  errno=0;
  int res=pipe(fd);
  if(res==-1) {
    SYSTEM_FAIL("Pipe creation.", errno);
  }

  _readDescriptor=fd[0];
  _writeDescriptor=fd[1];

  {
    BYPASSING_ALLOCATOR;
  
    _istream=new fdstream(_readDescriptor);
    _ostream=new fdstream(_writeDescriptor);
  }
  
  _istream->rdbuf()->pubsetbuf(0,0);

  //add the privileges into the semaphore
  _syncSemaphore.set(0,1);
  _syncSemaphore.set(1,1);
  //set the read-ahead byte to empty values
  _syncSemaphore.set(2,256);

  PipeList::push(this, s_instances);
}

SyncPipe::~SyncPipe()
{
  CALL("SyncPipe::~SyncPipe");

  releasePrivileges();
  ASS(PipeList::member(this, s_instances));
  s_instances = PipeList::remove(this, s_instances);

  if(canRead()) {
    neverRead();
  }
  if(canWrite()) {
    neverWrite();
  }
}

/**
 * Acquire a privilege for this process to read from the pipe
 */
void SyncPipe::acquireRead()
{
  CALL("SyncPipe::acquireRead");
  ASS(canRead());
  ASS(!isReading());
  ASS(!isWriting()); //it does not make sense if one process would both reads and writes into a pipe

  _syncSemaphore.dec(0);

  //restore the preread character
  int preRead=_syncSemaphore.get(2);
  if(preRead==256) {
    preRead=-1;
  }
  ASS_LE(preRead,255);
  _istream->setPreReadChar(preRead);

  _isReading=true;
}

/**
 * Give up the privilege of this process to read from the pipe
 */
void SyncPipe::releaseRead()
{
  CALL("SyncPipe::releaseRead");
  ASS(isReading());

  _isReading=false;

  int preRead=_istream->getPreReadChar();
  if(preRead==-1) {
    preRead=256;
  }
  ASS_GE(preRead,0);
  ASS_LE(preRead,256);
  _syncSemaphore.set(2,preRead);

  _syncSemaphore.inc(0);
}

/**
 * Release the reading end of the pipe from this object. This
 * means that it will not be possible to call @b acquireRead on it.
 */
void SyncPipe::neverRead()
{
  CALL("SyncPipe::neverRead");
  ASS(canRead());  //@b neverRead() can only be called once
  ASS(!isReading());

  int res=close(_readDescriptor);
  if(res==-1) {
    SYSTEM_FAIL("Closing read descriptor of a pipe.", errno);
  }
  ASS_EQ(res,0);
  {
    BYPASSING_ALLOCATOR;
  
    delete _istream;
    _istream=0;
  }
}


/**
 * Acquire a privilege for this process to write into the pipe
 */
void SyncPipe::acquireWrite()
{
  CALL("SyncPipe::acquireWrite");
  ASS(canWrite());
  ASS(!isWriting());
  ASS(!isReading()); //it does not make sense if one process would both reads and writes into a pipe

  _syncSemaphore.dec(1);
  _isWriting=true;
}

/**
 * Give up the privilege of this process to write into the pipe
 */
void SyncPipe::releaseWrite()
{
  CALL("SyncPipe::releaseWrite");
  ASS(isWriting());

  _ostream->flush();
  _isWriting=false;
  _syncSemaphore.inc(1);
}

/**
 * Release the writing end of the pipe from this object. This
 * means that it will not be possible to call @b acquireWrite on it.
 */
void SyncPipe::neverWrite()
{
  CALL("SyncPipe::neverWrite");
  ASS(canWrite());  //@b neverWrite() can only be called once
  ASS(!isWriting());
  ASS(env.getOutputPipe()!=this); //we cannot forbid writing to pipe that we use as output

  int res=close(_writeDescriptor);
  if(res==-1) {
    SYSTEM_FAIL("Closing write descriptor of a pipe.", errno);
  }
  ASS_EQ(res,0);

  {
    BYPASSING_ALLOCATOR;
    
    delete _ostream;
    _ostream=0;
  }
}
/**
 * Give up all the privileges of this object
 */
void SyncPipe::releasePrivileges()
{
  CALL("SyncPipe::releasePrivileges");
  ASS(_syncSemaphore.hasSemaphore());

  if(isReading()) {
    releaseRead();
  }
  if(isWriting()) {
    releaseWrite();
  }
}

/**
 * Give up privileges of all the object in this process
 *
 * This function is called in the beginning of a forked child process.
 */
void SyncPipe::postForkChildHadler()
{
  CALL("SyncPipe::postForkChildHadler");

  PipeList::Iterator pit(s_instances);
  while(pit.hasNext()) {
    SyncPipe* p=pit.next();
    p->releasePrivileges();
  }
}

/**
 * Give up privileges of all the object in this process and destroy
 * the list of all pipe objects
 *
 * This function is called before the process termination.
 */
void SyncPipe::terminationHadler()
{
  CALL("SyncPipe::terminationHadler");

  PipeList* listIter=s_instances;
  while(listIter) {
    if(listIter->head()) {
      SyncPipe* p=listIter->head();
      p->releasePrivileges();
      listIter->setHead(0);
    }
    listIter=listIter->tail();
  }
}

void SyncPipe::ensureEventHandlersInstalled()
{
  CALL("SyncPipe::ensureEventHandlersInstalled");

  static bool installed=false;
  if(installed) {
    return;
  }
  Multiprocessing::instance()->registerForkHandlers(0,0,postForkChildHadler);
  //this termination handler must be called before the termination handler
  //of the Semaphore class
  System::addTerminationHandler(terminationHadler,0);
  installed=true;
}


}
}

