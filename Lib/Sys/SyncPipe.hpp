/**
 * @file SyncPipe.hpp
 * Defines class SyncPipe.
 */

#ifndef __SyncPipe__
#define __SyncPipe__

#include <fstream>

#include "Forwards.hpp"

#include "Lib/Exception.hpp"

#include "Semaphore.hpp"

namespace Lib {
namespace Sys {

class SyncPipe {
public:
  SyncPipe();
  ~SyncPipe();

  /** Return true iff the current object has acquired the read priviledge */
  bool canRead() const { return _canRead; }
  void acquireRead();
  void releaseRead();

  /** Return true iff the current object has acquired the write priviledge */
  bool canWrite() const { return _canWrite; }
  void acquireWrite();
  void releaseWrite();

  void releasePriviledges();

  /**
   * If we have read privilidges, return reference to an istream object
   */
  istream& in()
  {
    ASS(canRead());
    if(!canRead()) {
      INVALID_OPERATION("Unallowed read from pipe.");
    }
    return *_istream;
  }

  /**
   * If we have write privilidges, return reference to an ostream object
   */
  ostream& out()
  {
    ASS(canWrite());
    if(!canWrite()) {
      INVALID_OPERATION("Unallowed write to pipe.");
    }
    return *_ostream;
  }

private:
  SyncPipe(const SyncPipe&); //private and undefined
  const SyncPipe& operator=(const SyncPipe&); //private and undefined

  istream *_istream;
  ostream *_ostream;

  int _readDescriptor;
  int _writeDescriptor;
  bool _canRead;
  bool _canWrite;

  /**
   * Semaphore object with two semaphores. The first (number 0)
   * controls reading and the second one controls writing
   *
   * When the semaphore value is one, anyone can acquire a priviledge,
   * when it is zero, the acquire function will wait until it
   * increases.
   */
  Semaphore _syncSemaphore;

  static void postForkChildHadler();
  static void terminationHadler();
  static void ensureEventHandlersInstalled();

  typedef List<SyncPipe*> PipeList;

  static PipeList* s_instances;
};

}
}

#endif // __SyncPipe__
