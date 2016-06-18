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

#include "Lib/VString.hpp"

#include "Lib/Sys/SyncPipe.hpp"

#include "Kernel/Problem.hpp"

#include "Shell/Property.hpp"
#include "Shell/SineUtils.hpp"

namespace CASC {

using namespace std;
using namespace Lib;
using namespace Kernel;



#if COMPILER_MSVC

class CLTBModeLearning
{
public:
  static void perform() { USER_ERROR("casc_ltb mode is not supported on Windows"); }
};

#else

class CLTBProblemLearning;

class CLTBModeLearning
{
public:
  CLTBModeLearning() {
    attemptedStrategies = new SyncPipe();
    successfulStrategies = new SyncPipe();;
  }

  static void perform();
private:
  void solveBatch(istream& batchFile, bool first, vstring inputDirectory);
  int readInput(istream& batchFile, bool first);
  static ostream& lineOutput();
  static ostream& coutLineOutput();
  void loadIncludes();
  void doTraining(int time);

  typedef List<vstring> StringList;
  typedef Stack<vstring> StringStack;
  typedef pair<vstring,vstring> StringPair;
  typedef Stack<StringPair> StringPairStack;

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

  SyncPipe* attemptedStrategies;
  SyncPipe* successfulStrategies;

  friend class CLTBProblemLearning;
};


class CLTBProblemLearning
{
public:
  CLTBProblemLearning(CLTBModeLearning* parent, vstring problemFile, vstring outFile);

  void searchForProof(int terminationTime,int timeLimit) __attribute__((noreturn));
  typedef Set<vstring> StrategySet;
  typedef Stack<vstring> Schedule;
private:
  bool runSchedule(Schedule&,StrategySet& remember,bool fallback,int terminationTime);
  unsigned getSliceTime(vstring sliceCode,vstring& chopped);

  void performStrategy(int terminationTime,int timeLimit,  Shell::Property* property);
  void waitForChildAndExitWhenProofFound();
  void exitOnNoSuccess() __attribute__((noreturn));

  static ofstream* writerFileStream;
  static void terminatingSignalHandler(int sigNum) __attribute__((noreturn));
  void runSlice(vstring slice, unsigned milliseconds) __attribute__((noreturn));
  void runSlice(Options& strategyOpt) __attribute__((noreturn));

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

};

#endif //!COMPILER_MSVC

}

#endif // __CLTBModeLearning__
