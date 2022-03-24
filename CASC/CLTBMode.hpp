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
 * @file CLTBMode.hpp
 * Defines class CLTBMode.
 */

#ifndef __CLTBMode__
#define __CLTBMode__

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

#include "Schedules.hpp"

namespace CASC {

using namespace std;
using namespace Lib;
using namespace Kernel;

enum Category {
  HH4,
  ISA,
  HLL,
  MZR,
  UNKNOWN
};

class CLTBProblem;

class CLTBMode
{
public:
  static void perform();
private:
  void solveBatch(istream& batchFile, bool first,vstring inputDirectory);
  int readInput(istream& batchFile, bool first);
  static ostream& lineOutput();
  static ostream& coutLineOutput();
  void loadIncludes();
  void doTraining();
  void learnFromSolutionFile(vstring& solnFileName);

  typedef List<vstring> StringList;
  typedef Stack<vstring> StringStack;
  typedef pair<vstring,vstring> StringPair;
  typedef Stack<StringPair> StringPairStack;

  Category getCategory(vstring& categoryStr) {
    if (categoryStr == "LTB.HH4" || categoryStr == "LTB.HL4") {
      return HH4;
    } else if (categoryStr == "LTB.ISA") {
      return ISA;
    } else if (categoryStr == "LTB.HLL" || categoryStr == "LTB.HOL") {
      return HLL;
    } else if (categoryStr == "LTB.MZR") {
      return MZR;
    } else {
      return UNKNOWN;
    }
  }

  Category _category;
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

  // This contains formulas 'learned' in the sense that they were input
  // formulas used in proofs of previous problems
  // Note: this relies on the assurance that formulas are consistently named
  DHSet<vstring> _learnedFormulas;
  DHMap<vstring,unsigned> _learnedFormulasCount;
  unsigned _learnedFormulasMaxCount;
  bool _biasedLearning;

  friend class CLTBProblem;
};


class CLTBProblem
{
public:
  CLTBProblem(CLTBMode* parent, vstring problemFile, vstring outFile);

  [[noreturn]] void searchForProof(int terminationTime,int timeLimit,const Category category);
  typedef Set<vstring> StrategySet;
private:
  bool runSchedule(Schedule&,StrategySet& remember,int terminationTime);
  unsigned getSliceTime(vstring sliceCode,vstring& chopped);

  void performStrategy(int terminationTime,int timeLimit,Category category,const Shell::Property* property);
  static void fillSchedule(Schedule& sched,const Shell::Property* property,int timeLimit,Category category);

  void waitForChildAndExitWhenProofFound();
  [[noreturn]] void exitOnNoSuccess();

  static ofstream* writerFileStream;
  [[noreturn]] static void terminatingSignalHandler(int sigNum);
  [[noreturn]] void runSlice(vstring slice, unsigned milliseconds);
  [[noreturn]] void runSlice(Options& strategyOpt);

  static vstring problemFinishedString;

#if VDEBUG
  DHSet<pid_t> childIds;
#endif

  CLTBMode* parent;
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

}

#endif // __CLTBMode__
