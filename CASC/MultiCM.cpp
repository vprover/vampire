/**
 * @file MultiCM.cpp
 * Implements class MultiCM.
 */

#include "Forwards.hpp"

#include "Lib/Environment.hpp"
#include "Shell/UIHelper.hpp"

#include "Kernel/MainLoopScheduler.hpp"
#include "Kernel/MainLoop.hpp"

#include "MultiCM.hpp"

// Defined separately from CASCMode as we might want different values in each place
#define SLOWNESS 1.1

namespace CASC
{


bool MultiCM::runSchedule(Schedule& schedule, unsigned ds, StrategySet& remember, bool fallback)
{
  CALL("MultiCM::runSchedule");

  if(fallback){
    //Currently we cannot handle a second schedule
    return 1;
  }
  //TODO should we use ds?

  transformToOptionsList(schedule);
   
  Kernel::MainLoopScheduler scheduler(*_prb, *env -> optionsList);
  scheduler.run();

  int resultValue=1;
  //return value to zero if we were successful
#if SATISFIABLE_IS_SUCCESS
  if(env -> statistics->terminationReason==Statistics::REFUTATION ||
     env -> statistics->terminationReason==Statistics::SATISFIABLE) {
#else
  if(env -> statistics->terminationReason==Statistics::REFUTATION) {
#endif
    resultValue=0;
    }

  env -> beginOutput();
  UIHelper::outputResult(env -> out());
  env -> endOutput();

  return resultValue;
}

void MultiCM::transformToOptionsList(Schedule& schedule)
{
  CALL("MultiCM::transformToOptionsList");

  //For each strategy we create an option object in the optionsList
  //Need to ensure additional global options are dealt with appropriately
  //Currently all global options are copied but overriden with those in the strategy 
  
  // save the original options that are about to be deleted
  Options orig_opt = *env->options;

  //Replace options list
  unsigned strategies = schedule.size(); 
  cout << "creating with " << strategies << " strategies" << endl;
  env->optionsList = SmartPtr<OptionsList>(new OptionsList(strategies));

  unsigned index=0;
  Schedule::BottomFirstIterator sit(schedule);
  while(sit.hasNext()){
    string sliceCode = sit.next();

    // get the option
    Options& opt = (*env->optionsList)[index++];

    // copy orig
    opt = orig_opt;    

    //decode slice
    cout << "decoding " << sliceCode << endl;
    opt.set("ignore_missing","on");
    opt.set("decode",sliceCode);

    //Slowdown simulated time limit for use in LRS
    int stl = opt.simulatedTimeLimit();
    if(stl){
      opt.setSimulatedTimeLimit(int(stl * SLOWNESS));
    }
  }

}


}

