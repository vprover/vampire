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
 * @file CLTBModeLearning.hpp
 * Defines class CLTBModeLearning.
 */

#ifndef __CLTBModeLearning__
#define __CLTBModeLearning__

#include <utility>

#include "Forwards.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/Portability.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Set.hpp"

#include "Lib/VString.hpp"

#include "Lib/Sys/SyncPipe.hpp"

#include "Kernel/Problem.hpp"

#include "Shell/Property.hpp"
#include "Shell/SineUtils.hpp"

namespace CASC {

using namespace std;
using namespace Lib;
using namespace Kernel;

class CLTBProblemLearning;

  struct ProbRecord{
    Set<vstring> suc;
    Set<vstring> fail;
    float avg;
  };

class CLTBModeLearning
{
public:
  CLTBModeLearning() : stratSem(1) {
    strategies = new SyncPipe();;
    stratSem.set(0,0); 
  }

  static void perform();
private:
  void solveBatch(istream& batchFile, bool first, vstring inputDirectory);
  int readInput(istream& batchFile, bool first);
  static ostream& lineOutput();
  static ostream& coutLineOutput();
  void loadIncludes();
  void doTraining(int time,bool startup);

  typedef List<vstring> StringList;
  typedef Stack<vstring> StringStack;
  typedef pair<vstring,vstring> StringPair;
  typedef Stack<StringPair> StringPairStack;
  typedef Stack<vstring> Schedule;
  static void fillSchedule(Schedule& strats);

  vstring _trainingDirectory;
  /** per-problem time limit, in milliseconds */
  int _problemTimeLimit;
  /** true if question answers should be given */
  bool _questionAnswering;
  /** total time used by batches before this one, in milliseconds */
  int _timeUsedByPreviousBatches;

  /** files to be included */
  StringList* _theoryIncludes;

  /** The first vstring in the pair is problem file, the second
   * one is output file. The problemFiles[0] is the first
   * problem that should be attempted. */
  StringPairStack _problemFiles;

  ScopedPtr<Problem> _baseProblem;

  Semaphore stratSem;
  SyncPipe* strategies;

  static DHMap<vstring,ProbRecord*> probRecords;
  static DHMap<vstring,Stack<vstring>*> stratWins;

  Stack<vstring> problems;
  Stack<vstring> new_problems;
  Schedule strats;

  friend class CLTBProblemLearning;
};


class CLTBProblemLearning
{
public:
  CLTBProblemLearning(CLTBModeLearning* parent, vstring problemFile, vstring outFile);

  typedef Set<vstring> StrategySet;
  typedef Stack<vstring> Schedule;

  [[noreturn]] void searchForProof(int terminationTime,int timeLimit,Schedule& strats,bool stopOnProof);
private:
  bool runSchedule(Schedule&,StrategySet& remember,bool fallback,int terminationTime, bool stopOnProof);
  unsigned getSliceTime(vstring sliceCode,vstring& chopped);

  void performStrategy(int terminationTime,int timeLimit,  Shell::Property* property, Schedule& quick, bool stopOnProof);
  void waitForChildAndExitWhenProofFound(bool stopOnProof);
  [[noreturn]] void exitOnNoSuccess();

  static ofstream* writerFileStream;
  [[noreturn]] static void terminatingSignalHandler(int sigNum);
  [[noreturn]] void runSlice(vstring slice, unsigned milliseconds,bool printProof);
  [[noreturn]] void runSlice(Options& strategyOpt, bool printProof);

  static vstring problemFinishedString;

#if VDEBUG
  DHSet<pid_t> childIds;
#endif

  CLTBModeLearning* parent;
  vstring problemFile;
  vstring outFile;

  /**
   * Problem that is being solved.
   *
   * This is just a reference to parent's @c baseProblem object into which we
   * add problem-specific axioms in the @c searchForProof() function. We can do this,
   * because in the current process this child object is the only one that
   * will be using the problem object.
   */
  Problem& prb;

  Semaphore _syncSemaphore; // semaphore for synchronizing writing if the solution

  /**
   * Assumes semaphore object with 1 semaphores (at index 0).
   * Locks on demand (once) and releases the lock on destruction.
   */
  struct ScopedSemaphoreLocker { //
    Semaphore& _sem;
    bool locked;
    ScopedSemaphoreLocker(Semaphore& sem) : _sem(sem), locked(false) {}

    void lock() {
      if (!locked) {
        _sem.dec(0);
        locked = true;
      }
    }

    ~ScopedSemaphoreLocker() {
      if (locked) {
        _sem.inc(0);
      }
    }
  };

  struct ScopedSyncPipe {
    SyncPipe* pipe;
    // Probably dangerous to acquire in constructor
    ScopedSyncPipe(SyncPipe* p) : pipe(p)
    {
      cout << "getting pipe" << endl;
      pipe->acquireWrite();
      cout << "got pipe" << endl;
    }
    ~ScopedSyncPipe(){
      cout << "release pipe" << endl;
      pipe->releaseWrite();
    } 
  };

};

}

#endif // __CLTBModeLearning__
