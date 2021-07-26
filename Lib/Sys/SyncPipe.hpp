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
 * @file SyncPipe.hpp
 * Defines class SyncPipe.
 */

#ifndef __SyncPipe__
#define __SyncPipe__

#include <fstream>

#include "Forwards.hpp"

#include "Lib/fdstream.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Portability.hpp"

#include "Semaphore.hpp"

namespace Lib {
namespace Sys {

class SyncPipe {
public:
  SyncPipe();
  ~SyncPipe();

  /** Return true iff the current object has acquired the read privilege */
  bool isReading() const { return _isReading; }
  /** Return true iff the current object can acquire read privileges */
  bool canRead() const { return _istream; }

  void acquireRead();
  void releaseRead();
  void neverRead();

  /** Return true iff the current object has acquired the write privilege */
  bool isWriting() const { return _isWriting; }
  /** Return true iff the current object can acquire write privileges */
  bool canWrite() const { return _ostream; }

  void acquireWrite();
  void releaseWrite();
  void neverWrite();

  void releasePrivileges();

  /**
   * If we have read privileges, return reference to an istream object
   */
  istream& in()
  {
    ASS(_istream);
    ASS(isReading());
    if(!isReading()) {
      INVALID_OPERATION("Unallowed read from pipe.");
    }
    return *_istream;
  }

  /**
   * If we have write privileges, return reference to an ostream object
   */
  ostream& out()
  {
    ASS(_ostream);
    ASS(isWriting());
    if(!isWriting()) {
      INVALID_OPERATION("Unallowed write to pipe.");
    }
    return *_ostream;
  }

private:
  SyncPipe(const SyncPipe&); //private and undefined
  const SyncPipe& operator=(const SyncPipe&); //private and undefined

  /** Contains pointer to input stream reading from the pipe, or 0 if
   * @b neverRead has been called */
  fdstream *_istream;
  /** Contains pointer to output stream writing to the pipe, or 0 if
   * @b neverWrite has been called */
  fdstream *_ostream;

  int _readDescriptor;
  int _writeDescriptor;
  bool _isReading;
  bool _isWriting;

  /**
   * Semaphore object with three semaphores. The first (number 0)
   * controls reading, the second one controls writing, and the third
   * one contains the value of the read-ahead byte from the pipe, or
   * 256 if there is not any.
   *
   * When the semaphore value is one, anyone can acquire a privilege,
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
