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
: _canRead(false), _canWrite(false), _syncSemaphore(2)
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

  //add the priviledges into the semaphore
  _syncSemaphore.inc(0);
  _syncSemaphore.inc(1);

  PipeList::push(this, s_instances);
}

SyncPipe::~SyncPipe()
{
  CALL("SyncPipe::~SyncPipe");

  releasePriviledges();
  ASS(s_instances->member(this));
  s_instances=s_instances->remove(this);

  int res=close(_readDescriptor);
  if(res==-1) {
    SYSTEM_FAIL("Closing read descriptor of a pipe.", errno);
  }
  ASS_EQ(res,0);

  res=close(_writeDescriptor);
  if(res==-1) {
    SYSTEM_FAIL("Closing write descriptor of a pipe.", errno);
  }
  ASS_EQ(res,0);

  delete _istream;
  delete _ostream;
}

/**
 * Acquire a priviledge for this process to read from the pipe
 */
void SyncPipe::acquireRead()
{
  CALL("SyncPipe::acquireRead");
  ASS(!canRead());
  ASS(!canWrite()); //it does not make sense if one process would both reads and writes into a pipe

  _syncSemaphore.dec(0);
  _canRead=true;
}

/**
 * Give up the priviledge of this process to read from the pipe
 */
void SyncPipe::releaseRead()
{
  CALL("SyncPipe::releaseRead");
  ASS(canRead());

  _canRead=false;
  _syncSemaphore.inc(0);
}

/**
 * Acquire a priviledge for this process to write into the pipe
 */
void SyncPipe::acquireWrite()
{
  CALL("SyncPipe::acquireWrite");
  ASS(!canWrite());
  ASS(!canRead()); //it does not make sense if one process would both reads and writes into a pipe

  _syncSemaphore.dec(1);
  _canWrite=true;
}

/**
 * Give up the priviledge of this process to write into the pipe
 */
void SyncPipe::releaseWrite()
{
  CALL("SyncPipe::releaseWrite");
  ASS(canWrite());

  _canWrite=false;
  _syncSemaphore.inc(1);
}

/**
 * Give up all the priviledges of this object
 */
void SyncPipe::releasePriviledges()
{
  CALL("SyncPipe::releasePriviledges");
  ASS(_syncSemaphore.hasSemaphore());

  if(canRead()) {
    releaseRead();
  }
  if(canWrite()) {
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
