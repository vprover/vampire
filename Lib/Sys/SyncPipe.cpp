/**
 * @file SyncPipe.cpp
 * Implements class SyncPipe.
 */

#include <cerrno>

#include "Lib/fdstream.hpp"

#include "Lib/Portability.hpp"

#if !COMPILER_MSVC
#include <unistd.h>
#endif

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
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

  _istream=new fdstream(_readDescriptor);
  _ostream=new fdstream(_writeDescriptor);

  _istream->rdbuf()->pubsetbuf(0,0);

  //add the priviledges into the semaphore
  _syncSemaphore.inc(0);
  _syncSemaphore.inc(1);
  _syncSemaphore.set(2,256);

  PipeList::push(this, s_instances);
}

SyncPipe::~SyncPipe()
{
  CALL("SyncPipe::~SyncPipe");

  releasePriviledges();
  ASS(s_instances->member(this));
  s_instances=s_instances->remove(this);

  if(canRead()) {
    neverRead();
  }
  if(canWrite()) {
    neverWrite();
  }
}

/**
 * Acquire a priviledge for this process to read from the pipe
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
 * Give up the priviledge of this process to read from the pipe
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
  delete _istream;
  _istream=0;
}


/**
 * Acquire a priviledge for this process to write into the pipe
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
 * Give up the priviledge of this process to write into the pipe
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

  delete _ostream;
  _ostream=0;
}
/**
 * Give up all the priviledges of this object
 */
void SyncPipe::releasePriviledges()
{
  CALL("SyncPipe::releasePriviledges");
  ASS(_syncSemaphore.hasSemaphore());

  if(isReading()) {
    releaseRead();
  }
  if(isWriting()) {
    releaseWrite();
  }
}

/**
 * Give up priviledges of all the object in this process
 *
 * This function is called in the beginning of a forked child process.
 */
void SyncPipe::postForkChildHadler()
{
  CALL("SyncPipe::postForkChildHadler");

  PipeList::Iterator pit(s_instances);
  while(pit.hasNext()) {
    SyncPipe* p=pit.next();
    p->releasePriviledges();
  }
}

/**
 * Give up priviledges of all the object in this process and destroy
 * the list of all pipe objects
 *
 * This function is called before the process termination.
 */
void SyncPipe::terminationHadler()
{
  CALL("SyncPipe::terminationHadler");

  while(s_instances) {
    SyncPipe* p=PipeList::pop(s_instances);
    p->releasePriviledges();
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
