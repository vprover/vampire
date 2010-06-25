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

class CLTBProblem;

class CLTBMode
{
public:
  void perform();
private:
  void readInput();

  void loadIncludes();

  typedef List<string> StringList;
  typedef Stack<string> StringStack;
  typedef pair<string,string> StringPair;
  typedef Stack<StringPair> StringPairStack;

  string division;
  int problemTimeLimit;
  int overallTimeLimit;

  StringList* theoryIncludes;
  /** The first string in the pair is problem file, the second
   * one is output file. The problemFiles[0] is the first
   * problem that should be attempted. */
  StringPairStack problemFiles;

  SineTheorySelector theorySelector;
  UnitList* theoryAxioms;

  Property property;

  friend class CLTBProblem;
};


class CLTBProblem
{
public:
  CLTBProblem(CLTBMode* parent, string problemFile, string outFile);
  ~CLTBProblem();

  void perform() __attribute__((noreturn));
private:

  void waitForChildAndExitWhenProofFound();

  bool runSchedule(const char** sliceCodes);

  void runWriterChild() __attribute__((noreturn));

  void runChild(string slice, unsigned ds) __attribute__((noreturn));
  void runChild(Options& opt) __attribute__((noreturn));

  unsigned getSliceTime(string sliceCode);

#if VDEBUG
  DHSet<pid_t> childIds;
#endif

  CLTBMode* parent;
  string problemFile;
  string outFile;

  UnitList* probUnits;
  Property property;

  pid_t writerChildPid;
  //pipe for collecting the output from children
  SyncPipe childOutputPipe;
};

}
}

#endif // __CLTBMode__
