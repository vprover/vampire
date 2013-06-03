/**
 * @file SpawningCM.cpp
 * Implements class SpawningCM.
 */

#include <stdlib.h>
#include <csignal>

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/List.hpp"
#include "Lib/System.hpp"

#include "Kernel/Problem.hpp"
#include "Kernel/Unit.hpp"

#include "Shell/Options.hpp"
#include "Shell/UIHelper.hpp"

#include "SpawningCM.hpp"

using namespace CASC;

SpawningCM::SpawningCM(string executable)
  : _executable(executable)
{
  CALL("SpawningCM::SpawningCM");

  if (!system(0)) {
    USER_ERROR("The spawning CASC mode is not supported on this system (the \"int system(const char *)\" function is not available)");
  }

  if (env.options->inputFile() == "") {
    USER_ERROR("Value of the --input_file option must be specified for the CASC mode in Windows.");
  }
  _inputFile = env.options->inputFile();

  //we just need to extract property from the problem
  ScopedPtr<Problem> prb(UIHelper::getInputProblem(*env.options));
  _property = Property::scan(prb->units());
}

bool SpawningCM::runSlice(Options& opt)
{
  CALL("SpawningCM::runSlice");

  string strategy = opt.generateTestId();
  string cmdLine = _executable + " --decode " + strategy + " --input_file " + _inputFile;

  if (env.options->include() != "") {
    cmdLine += " --include " + env.options->include();
  }

#if COMPILER_MSVC
  //required by MSDN
  _flushall();

  //we want to deal with Ctrl+C sent to the child in a special way
  System::ignoreSIGINT();
#endif

  int res = system(cmdLine.c_str());

#if COMPILER_MSVC
  //restore signal handler for Ctrl+C
  System::heedSIGINT();

  if (res == 3)  {
    //if child Vampire was terminated by SIGINT (Ctrl+C), we also terminate
    //(3 is the return value for this case; see documentation for the
    //@b vampireReturnValue global variable)
    handleSIGINT();
  }

  if (res == 0) {
    return true;
  }
#else
  if ( (WIFSIGNALED(res) && WTERMSIG(res) == SIGINT) ||
      (WIFEXITED(res) && WEXITSTATUS(res) == 3) )  {
    //if child Vampire was terminated by SIGINT (Ctrl+C), we also terminate
    //(3 is the return value for this case; see documentation for the
    //@b vampireReturnValue global variable)
    handleSIGINT();
  }

  if (WIFEXITED(res) && WEXITSTATUS(res) == 0) {
    //if Vampire succeeds, its return value is zero
    return true;
  }
#endif

  return false;
}

