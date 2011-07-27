/**
 * @file CLTBMode.hpp
 * Defines class CLTBMode.
 */

#ifndef __CLTBMode__
#define __CLTBMode__

#include <string>
#include <utility>

#include "Forwards.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/Portability.hpp"
#include "Lib/Stack.hpp"

#include "Lib/Sys/SyncPipe.hpp"

#include "Shell/Property.hpp"
#include "Shell/SineUtils.hpp"

namespace Shell {
namespace CASC {

using namespace std;
using namespace Lib;

#if COMPILER_MSVC

class CLTBMode
{
public:
  void perform() { USER_ERROR("casc_ltb mode is not supported on Windows"); }
};

#else

class CLTBProblem;

class CLTBMode
{
public:
  static void perform();
private:
  void perform(istream& batchFile);
  void readInput(istream& batchFile);

  void loadIncludes();

  typedef List<string> StringList;
  typedef Stack<string> StringStack;
  typedef pair<string,string> StringPair;
  typedef Stack<StringPair> StringPairStack;

  string category;
  int problemTimeLimit;
//  int overallTimeLimit;
  bool questionAnswering;

  StringList* theoryIncludes;
  /** The first string in the pair is problem file, the second
   * one is output file. The problemFiles[0] is the first
   * problem that should be attempted. */
  StringPairStack problemFiles;

//  SineTheorySelector theorySelector;
  UnitList* theoryAxioms;

  Property* property;

  friend class CLTBProblem;
};


class CLTBProblem
{
public:
  CLTBProblem(CLTBMode* parent, string problemFile, string outFile);

  void perform() __attribute__((noreturn));
private:
  typedef Set<string> StrategySet;
  typedef Stack<string> Schedule;
  bool runSchedule(Schedule&,StrategySet& remember,bool fallback);
  unsigned getSliceTime(string sliceCode,string& chopped);

  void performStrategy();
  void waitForChildAndExitWhenProofFound();
  void exitOnNoSuccess() __attribute__((noreturn));

  static ofstream* writerFileStream;
  static void terminatingSignalHandler(int sigNum) __attribute__((noreturn));
  void runWriterChild() __attribute__((noreturn));
  void runChild(string slice, unsigned ds) __attribute__((noreturn));
  void runChild(Options& opt) __attribute__((noreturn));

  static string problemFinishedString;

#if VDEBUG
  DHSet<pid_t> childIds;
#endif

  CLTBMode* parent;
  string problemFile;
  string outFile;

  UnitList* probUnits;
  Property* property;

  pid_t writerChildPid;
  /** pipe for collecting the output from children */
  SyncPipe childOutputPipe;
};

#endif //!COMPILER_MSVC

}
}

#endif // __CLTBMode__
