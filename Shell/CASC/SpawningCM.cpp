/**
 * @file SpawningCM.cpp
 * Implements class SpawningCM.
 */

#include <stdlib.h>
#include <csignal>

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/List.hpp"

#include "Kernel/Unit.hpp"

#include "Shell/Options.hpp"
#include "Shell/UIHelper.hpp"

#include "SpawningCM.hpp"

namespace Shell
{
namespace CASC
{

SpawningCM::SpawningCM(string executable)
: _executable(executable)
{
  CALL("SpawningCM::SpawningCM");

  if(!system(0)) {
    USER_ERROR("The spawning CASC mode is not supported on this system (the \"int system(const char *)\" function is not available)");
  }

  if(env.options->inputFile()=="") {
    USER_ERROR("Value for the option --input_file has to be specified for the spawning CASC mode.");
  }
  _inputFile=env.options->inputFile();

  UnitList* units=UIHelper::getInputUnits();
  _property.scan(units);
  while(units) {
    Unit* u=UnitList::pop(units);
    //this won't cause destruction of Formula objects but better than nothing...
    u->destroy();
  }
}

#if COMPILER_MSVC

void emptySignalHandler(int)
{
}

#endif


bool SpawningCM::runStrategy(string strategy, unsigned ds)
{
  CALL("SpawningCM::runStrategy");

  string cmdLine=_executable+" -decode "+strategy+" -t "+Int::toString(static_cast<float>(ds)/10.0f)+" -input_file "+_inputFile;

  if(env.options->include()!="") {
    cmdLine+=" -include "+env.options->include();
  }

#if COMPILER_MSVC
  //required by MSDN
  _flushall();

  //also we want to deal with Ctrl+C in a nice way
  void (*oldSIGINTHandler)(int);
  oldSIGINTHandler=signal(SIGINT, emptySignalHandler);
#endif

  int res=system(cmdLine.c_str());

#if COMPILER_MSVC
  //restore signal handler for Ctrl+C
  signal(SIGINT, oldSIGINTHandler);

  if(res==3)  {
    //if child Vampire was terminated by SIGINT (Ctrl+C), we also terminate
    //(3 is the return value for this case; see documentation for the
    //@b vampireReturnValue global variable)
    env.out<<"% Terminated by SIGINT!"<<endl;
    exit(3);
  }

  if(res==0) {
    return true;
  }
#else
  if( (WIFSIGNALED(res) && WTERMSIG(res)==SIGINT) ||
      (WIFEXITED(res) && WEXITSTATUS(res)==3) )  {
    //if child Vampire was terminated by SIGINT (Ctrl+C), we also terminate
    //(3 is the return value for this case; see documentation for the
    //@b vampireReturnValue global variable)
    env.out<<"% Terminated by SIGINT!"<<endl;
    exit(3);
  }

  if(WIFEXITED(res) && WEXITSTATUS(res)==0) {
    //if Vampire succeeds, its return value is zero
    return true;
  }
#endif

  return false;
}

}
}
