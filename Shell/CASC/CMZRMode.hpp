/**
 * @file CMZRMode.hpp
 * Defines class CMZRMode.
 */

#ifndef __CMZRMode__
#define __CMZRMode__

#include <string>
#include <utility>

#include "Forwards.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/Portability.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "Lib/Sys/SyncPipe.hpp"

#include "Kernel/Problem.hpp"

#include "Shell/Property.hpp"
#include "Shell/SineUtils.hpp"

namespace Shell {
namespace CASC {

using namespace std;
using namespace Lib;
using namespace Kernel;

#if COMPILER_MSVC

class CMZRMode
{
public:
  static void perform() { USER_ERROR("casc_mzr mode is not supported on Windows"); }
};

#else

class CMZRProblem;

class CMZRMode
{
public:
  CMZRMode();

  static void perform();
private:
  void perform(istream& batchFile);
  void readInput(istream& batchFile);

  void loadIncludes();
  void loadProblems();

  typedef Stack<string> StringStack;

  unsigned getSliceTime(string sliceCode);
  void getStrategy(Property& property, StringStack& res);

  struct ProblemInfo {
    ProblemInfo(string inputFName="",string outputFName="")
    : inputFName(inputFName), outputFName(outputFName), specificFormulas(0), property(0),
      solved(false), runningProcessPID(-1) {}

    string inputFName;
    string outputFName;

    //the fields below are populated in loadProblems()
    UnitList* specificFormulas;
    bool hasConjecture;
    Property* property;
    /** schedule of strategies to try, the first (next) one to try is at the top of the stack,
     * scheduler removes attempted strategies from this stack */
    StringStack schedule;

    //these fields are used for scheduling
    bool solved;
    /** pid of process that is currently solving the problem or -1 if there is none */
    int runningProcessPID;
    /** the time when the child process should terminate */
    unsigned processDueTime;
  };


  typedef List<string> StringList;



  string category;
  /** in seconds */
  int problemTimeLimit;
//  int overallTimeLimit;
  bool questionAnswering;

  StringList* theoryIncludes;


  ScopedPtr<Problem> baseProblem;

  /** Initialized in loadIncludes */
  Property* _axiomProperty;

  /** Contains information on problems, the _problemFiles[0] is the first
   * that appeared in the batch file. */
  Stack<ProblemInfo> _problems;


  //scheduling related members
  bool canAttemptProblem(unsigned idx) const;
  void attemptProblem(unsigned idx);
  void waitForOneFinished();

  void startStrategyRun(unsigned prbIdx, string strategy, unsigned timeMs);
  void strategyRunChild(unsigned prbIdx, string strategy, unsigned timeMs) NO_RETURN;

  unsigned _availCoreCnt;
  unsigned _unsolvedCnt;

  typedef DHMap<pid_t,unsigned> ProcessMap;
  /** map from process IDs to problems they are solving */
  ProcessMap _processProblems;

  friend class CMZRProblem;
};


#endif //!COMPILER_MSVC

}
}

#endif // __CMZRMode__
