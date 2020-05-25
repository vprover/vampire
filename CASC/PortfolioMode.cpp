/*
 * File PortfolioMode.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */

/**
 * @file PortfolioMode.cpp
 * Implements class PortfolioMode.
 */

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Portability.hpp"
#include "Lib/Stack.hpp"
#include "Lib/System.hpp"
#include "Lib/ScopedLet.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Sys/Multiprocessing.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"
#include "Shell/Normalisation.hpp"
#include "Shell/TheoryFinder.hpp"

#include <unistd.h>

#include "Saturation/ProvingHelper.hpp"

#include "Kernel/Problem.hpp"

#include "Schedules.hpp"

#include "PortfolioMode.hpp"

using namespace Lib;
using namespace CASC;

PortfolioMode::PortfolioMode() : _slowness(1.0), _syncSemaphore(2) {
  // We need the following two values because the way the semaphore class is currently implemented:
  // 1) dec is the only operation which is blocking
  // 2) dec is done in the mode SEM_UNDO, so is undone when a process terminates

  _syncSemaphore.set(SEM_LOCK,1);    // to synchronize access to the second field
  _syncSemaphore.set(SEM_PRINTED,0); // to indicate that a child has already printed result (it should only happen once)
}

/**
 * The function that does all the job: reads the input files and runs
 * Vampires to solve problems.
 */
bool PortfolioMode::perform(float slowness)
{
  CALL("PortfolioMode::perform");

  PortfolioMode pm;
  pm._slowness = slowness;

  bool resValue;
  try {
      resValue = pm.searchForProof();
  } catch (Exception& exc) {
      cerr << "% Exception at proof search level" << endl;
      exc.cry(cerr);
      System::terminateImmediately(1); //we didn't find the proof, so we return nonzero status code
  }

  if (outputAllowed()) {
    env.beginOutput();
    if (resValue) {
      addCommentSignForSZS(env.out());
      env.out()<<"Success in time "<<Timer::msToSecondsString(env.timer->elapsedMilliseconds())<<endl;
    }
    else {
      addCommentSignForSZS(env.out());
      env.out()<<"Proof not found in time "<<Timer::msToSecondsString(env.timer->elapsedMilliseconds())<<endl;
      if (env.remainingTime()/100>0) {
        addCommentSignForSZS(env.out());
        env.out()<<"SZS status GaveUp for "<<env.options->problemName()<<endl;
      }
      else {
        //From time to time we may also be terminating in the timeLimitReached()
        //function in Lib/Timer.cpp in case the time runs out. We, however, output
        //the same string there as well.
        addCommentSignForSZS(env.out());
        env.out()<<"SZS status Timeout for "<<env.options->problemName()<<endl;
      }
    }
    if (env.options && env.options->timeStatistics()) {
      TimeCounter::printReport(env.out());
    }
    env.endOutput();
  }

  return resValue;
}

bool PortfolioMode::searchForProof()
{
  CALL("PortfolioMode::searchForProof");

  env.timer->makeChildrenIncluded();
  TimeCounter::reinitialize();

  _prb = UIHelper::getInputProblem(*env.options);

  /* CAREFUL: Make sure that the order
   * 1) getProperty, 2) normalise, 3) TheoryFinder::search
   * is the same as in profileMode (vampire.cpp)
   * also, cf. the beginning of Preprocessing::preprocess*/
  Shell::Property* property = _prb->getProperty();
  {
    TimeCounter tc(TC_PREPROCESSING);

    //we normalize now so that we don't have to do it in every child Vampire
    ScopedLet<Statistics::ExecutionPhase> phaseLet(env.statistics->phase,Statistics::NORMALIZATION);
    Normalisation().normalise(*_prb);

    TheoryFinder(_prb->units(),property).search();
  }

  // now all the cpu usage will be in children, we'll just be waiting for them
  Timer::setTimeLimitEnforcement(false);

  return performStrategy(property);
}

bool PortfolioMode::performStrategy(Shell::Property* property)
{
  CALL("PortfolioMode::performStrategy");

  Schedule main;
  Schedule fallback;
  Schedule main_extra;
  Schedule fallback_extra;

  getSchedules(*property,main,fallback);
  getExtraSchedules(*property,main,main_extra,true,3);
  getExtraSchedules(*property,fallback,fallback_extra,true,3);

  // Normally we do main fallback main_extra fallback_extra
  // However, in SMTCOMP mode the fallback is universal for all
  // logics e.g. it's not very strong. Therefore, in SMTCOMP
  // mode we do main main_extra fallback fallback_extra
 
  Stack<Schedule> schedules;
  if(env.options->schedule() == Options::Schedule::SMTCOMP){
    schedules.push(fallback_extra);
    schedules.push(fallback);
    schedules.push(main_extra);
    schedules.push(main);
  }
  else{
    schedules.push(fallback_extra);
    schedules.push(main_extra);
    schedules.push(fallback);
    schedules.push(main);
  }

  int terminationTime = env.remainingTime()/100;

  while(terminationTime > 0) {
    // After running for the first time we replace schedules
    // by copies with x2 time limits and do this forever
    // We build these next_schedules as we go
    Stack<Schedule> next_schedules;

    Stack<Schedule>::Iterator sit(schedules);
    while(sit.hasNext() && terminationTime > 0){
      Schedule s = sit.next();
      if(runSchedule(s,terminationTime)){ return true; }
      Schedule ns;
      getExtraSchedules(*property,s,ns,false,2);
      next_schedules.push(ns);
      terminationTime = env.remainingTime()/100;
    }

    schedules = next_schedules;
  }
  return false;
}

/**
 * The idea here is to create extra schedules based on the existing schedules
 * There are two motivations
 *  1. Sometimes the provided schedules don't fill the given time limit
 *  2. Sometimes we have new options that are not yet included in the schedules
 *
 * This function will
 *  1. Increase the time limit of existing strategies (by time_multiplier)
 *  2. Add extra options to existing strategies (if add_extra is true)
 *
 * The expectation is that the extra_opts is updated before each competition submission
 *
 * IMPORTANT - every time we add something to extra_opts we are multiplying the length of the old schedule. For example,
 * if the old schedule takes 60 seconds to run and the length of extra_opts is 10 then extra could take 10 minutes to run
 * of course, many of the new strategies might fail immediately due to inconsistent constraints etc but in general we want
 * to keep extra_opts for important new additions only.
 *
 * @author Giles
 **/
void PortfolioMode::getExtraSchedules(Property& prop, Schedule& old, Schedule& extra, bool add_extra, int time_multiplier)
{
  CALL("PortfolioMode::getExtraSchedules");

  // Add new extra_opts here
  Stack<vstring> extra_opts;

  if(add_extra){

   // Always try these
   extra_opts.push("sp=frequency");
   extra_opts.push("avsq=on");
   extra_opts.push("slsq=on");
   extra_opts.push("plsq=on");

   // If contains integers, rationals and reals
   if(prop.props() & (Property::PR_HAS_INTEGERS | Property::PR_HAS_RATS | Property::PR_HAS_REALS)){
    extra_opts.push("tha=some");
    extra_opts.push("sos=theory:sstl=5");
    extra_opts.push("uwa=fixed:uwaf=on");
    extra_opts.push("thsq=on");
    extra_opts.push("thsq=on:thsqd=16");
   }

   // If in SMT-COMP mode try guessing the goal
   if(env.options->schedule() == Options::Schedule::SMTCOMP){
    extra_opts.push("gtg=exists_all");
   }

   // If using Datatypes try induction
   if(prop.props() & (Property::PR_HAS_DT_CONSTRUCTORS | Property::PR_HAS_CDT_CONSTRUCTORS)){
    extra_opts.push("ind=struct");
    extra_opts.push("gtg=exists_all:ind=struct");
    extra_opts.push("ind=struct:sik=all");
    extra_opts.push("ind=struct:sik=all:indmd=1");
    extra_opts.push("ind=struct:indgen=on");
    extra_opts.push("ind=struct:indgen=on:indoct=on");
   }

  }

  Schedule::BottomFirstIterator it(old);
  while(it.hasNext()){
      vstring s = it.next();
      // try and grab time string
      vstring ts = s.substr(s.find_last_of("_")+1,vstring::npos);
      int t;
      if(Lib::Int::stringToInt(ts,t)){
        vstring prefix = s.substr(0,s.find_last_of("_")); 

        // Add a copy with increased time limit
        vstring new_s = prefix + "_" + Lib::Int::toString(t*time_multiplier);
        extra.push(new_s);

        // Add copies with new extra options (keeping the old time limit) 
        Stack<vstring>::Iterator addit(extra_opts);
        while(addit.hasNext()){
          vstring new_s = prefix + ":" + addit.next() + "_" + Lib::Int::toString(t);
          extra.push(new_s);
        }
      }
      else{ASSERTION_VIOLATION;}
  }

}

void PortfolioMode::getSchedules(Property& prop, Schedule& quick, Schedule& fallback)
{
  CALL("PortfolioMode::getSchedules");

  switch(env.options->schedule()) {
  case Options::Schedule::CASC_2014_EPR:
    Schedules::getCasc2014EprSchedule(prop,quick,fallback);
    break;
  case Options::Schedule::CASC_2014:
    Schedules::getCasc2014Schedule(prop,quick,fallback);
    break;
  case Options::Schedule::CASC_2016:
    Schedules::getCasc2016Schedule(prop,quick,fallback);
    break;
  case Options::Schedule::CASC_2017:
    Schedules::getCasc2017Schedule(prop,quick,fallback);
    break;
  case Options::Schedule::CASC_2018:
    Schedules::getCasc2018Schedule(prop,quick,fallback);
    break;
  case Options::Schedule::CASC_2019:
  case Options::Schedule::CASC:
    Schedules::getCasc2019Schedule(prop,quick,fallback);
    break;
  case Options::Schedule::CASC_SAT_2014:
    Schedules::getCascSat2014Schedule(prop,quick,fallback);
    break;
  case Options::Schedule::CASC_SAT_2016:
    Schedules::getCascSat2016Schedule(prop,quick,fallback);
    break;
  case Options::Schedule::CASC_SAT_2017:
    Schedules::getCascSat2017Schedule(prop,quick,fallback);
    break;
  case Options::Schedule::CASC_SAT_2018:
    Schedules::getCascSat2018Schedule(prop,quick,fallback);
    break;
  case Options::Schedule::CASC_SAT_2019:
  case Options::Schedule::CASC_SAT:
    Schedules::getCascSat2019Schedule(prop,quick,fallback);
    break;
  case Options::Schedule::SMTCOMP_2016:
    Schedules::getSmtcomp2016Schedule(prop,quick,fallback);
    break;
  case Options::Schedule::SMTCOMP_2017:
    Schedules::getSmtcomp2017Schedule(prop,quick,fallback);
    break;
  case Options::Schedule::SMTCOMP:
  case Options::Schedule::SMTCOMP_2018:
    Schedules::getSmtcomp2018Schedule(prop,quick,fallback);
    break;

  case Options::Schedule::LTB_HH4_2015_FAST:
    Schedules::getLtb2015Hh4FastSchedule(prop,quick);
    break;
  case Options::Schedule::LTB_HH4_2015_MIDD:
    Schedules::getLtb2015Hh4MiddSchedule(prop,quick);
    break;
  case Options::Schedule::LTB_HH4_2015_SLOW:
    Schedules::getLtb2015Hh4SlowSchedule(prop,quick);
    break;
  case Options::Schedule::LTB_HH4_2017:
    Schedules::getLtb2017Hh4Schedule(prop,quick);
    break;

  case Options::Schedule::LTB_HLL_2015_FAST:
    Schedules::getLtb2015HllFastSchedule(prop,quick);
    break;
  case Options::Schedule::LTB_HLL_2015_MIDD:
    Schedules::getLtb2015HllMiddSchedule(prop,quick);
    break;
  case Options::Schedule::LTB_HLL_2015_SLOW:
    Schedules::getLtb2015HllSlowSchedule(prop,quick);
    break;
  case Options::Schedule::LTB_HLL_2017:
    Schedules::getLtb2017HllSchedule(prop,quick);
    break;

  case Options::Schedule::LTB_ISA_2015_FAST:
    Schedules::getLtb2015IsaFastSchedule(prop,quick);
    break;
  case Options::Schedule::LTB_ISA_2015_MIDD:
    Schedules::getLtb2015IsaMiddSchedule(prop,quick);
    break;
  case Options::Schedule::LTB_ISA_2015_SLOW:
    Schedules::getLtb2015IsaSlowSchedule(prop,quick);
    break;
  case Options::Schedule::LTB_ISA_2017:
    Schedules::getLtb2017IsaSchedule(prop,quick);
    break;

  case Options::Schedule::LTB_MZR_2015_FAST:
    Schedules::getLtb2015MzrFastSchedule(prop,quick);
    break;
  case Options::Schedule::LTB_MZR_2015_MIDD:
    Schedules::getLtb2015MzrMiddSchedule(prop,quick);
    break;
  case Options::Schedule::LTB_MZR_2015_SLOW:
    Schedules::getLtb2015MzrSlowSchedule(prop,quick);
    break;
  case Options::Schedule::LTB_MZR_2017:
    Schedules::getLtb2017MzrSchedule(prop,quick);
    break;
  case Options::Schedule::LTB_2014:
    Schedules::getLtb2014Schedule(prop,quick);
    break;
  case Options::Schedule::LTB_2014_MZR:
    Schedules::getLtb2014MzrSchedule(prop,quick,fallback);
    break;

  case Options::Schedule::LTB_DEFAULT_2017:
    Schedules::getLtb2017DefaultSchedule(prop,quick);
    break;
  default:
    INVALID_OPERATION("Unknown schedule");
  }
}

static unsigned milliToDeci(unsigned timeInMiliseconds) {
  return timeInMiliseconds/100;
}

// Simple one-after-the-other priority.
float PortfolioProcessPriorityPolicy::staticPriority(vstring sliceCode)
{
  static float priority = 0.;
  priority += 1.;
  return priority;
}

//should never be called
float PortfolioProcessPriorityPolicy::dynamicPriority(pid_t pid)
{
  ASSERTION_VIOLATION;
  return 0.;
}

PortfolioSliceExecutor::PortfolioSliceExecutor(PortfolioMode *mode)
  : _mode(mode)
{}

void PortfolioSliceExecutor::runSlice
  (vstring sliceCode, int terminationTime)
{
  vstring chopped;
  int sliceTime = _mode->getSliceTime(sliceCode, chopped);

  int elapsedTime = milliToDeci(env.timer->elapsedMilliseconds());
  int remainingTime = terminationTime - elapsedTime;
  if (sliceTime > remainingTime)
  {
    sliceTime = remainingTime;
  }

  ASS_GE(sliceTime,0);
  try
  {
    _mode->runSlice(sliceCode, sliceTime);
  }
  catch(Exception &e)
  {
    if(outputAllowed())
    {
      std::cerr << "% Exception at run slice level" << std::endl;
      e.cry(std::cerr);
    }
    System::terminateImmediately(1); // didn't find proof
  }
}

/**
 * Run a schedule.
 * Return true if a proof was found, otherwise return false.
 */
bool PortfolioMode::runSchedule(Schedule& schedule, int terminationTime)
{
  CALL("PortfolioMode::runSchedule");

  UIHelper::portfolioParent = true; // to report on overall-solving-ended in Timer.cpp

  PortfolioProcessPriorityPolicy policy;
  PortfolioSliceExecutor executor(this);
  ScheduleExecutor sched(&policy, &executor);

  return sched.run(schedule, terminationTime);
}

/**
 * Return the intended slice time in deciseconds and assign the slice
 * vstring with chopped time limit to @b chopped.
 */
unsigned PortfolioMode::getSliceTime(vstring sliceCode,vstring& chopped)
{
  CALL("PortfolioMode::getSliceTime");

  unsigned pos = sliceCode.find_last_of('_');
  vstring sliceTimeStr = sliceCode.substr(pos+1);
  chopped.assign(sliceCode.substr(0,pos));
  unsigned sliceTime;
  ALWAYS(Int::stringToUnsignedInt(sliceTimeStr,sliceTime));
  ASS_G(sliceTime,0); //strategies with zero time don't make sense

  unsigned time = _slowness * sliceTime + 1;
  if (time < 10) {
    time++;
  }
  return time;
} // getSliceTime

/**
 * Wait for termination of a child
 * return true if a proof was found
 */
bool PortfolioMode::waitForChildAndCheckIfProofFound()
{
  CALL("PortfolioMode::waitForChildAndCheckIfProofFound");
  ASS(!childIds.isEmpty());

  int resValue;
  pid_t finishedChild = Multiprocessing::instance()->waitForChildTermination(resValue);
#if VDEBUG
  ALWAYS(childIds.remove(finishedChild));
#endif
  if (!resValue) {
    // we have found the proof. It has been already written down by the writer child,

    /*
    env.beginOutput();
    lineOutput() << "terminated slice pid " << finishedChild << " (success)" << endl << flush;
    env.endOutput();
    */
    return true;
  }
  // proof not found

  /*
  env.beginOutput();
  lineOutput() << "terminated slice pid " << finishedChild << " (fail)" << endl;
  env.endOutput();
  */
  return false;
} // waitForChildAndExitWhenProofFound


/**
 * Run a slice given by its code using the specified time limit.
 */
void PortfolioMode::runSlice(vstring sliceCode, unsigned timeLimitInDeciseconds)
{
  CALL("PortfolioMode::runSlice");

  Options opt = *env.options;
  opt.readFromEncodedOptions(sliceCode);
  opt.setTimeLimitInDeciseconds(timeLimitInDeciseconds);
  int stl = opt.simulatedTimeLimit();
  if (stl) {
    opt.setSimulatedTimeLimit(int(stl * _slowness));
  }
  runSlice(opt);
} // runSlice

/**
 * Run a slice given by its options
 */
void PortfolioMode::runSlice(Options& strategyOpt)
{
  CALL("PortfolioMode::runSlice(Option&)");

  System::registerForSIGHUPOnParentDeath();
  UIHelper::portfolioParent=false;

  int resultValue=1;
  env.timer->reset();
  env.timer->start();
  TimeCounter::reinitialize();
  Timer::setTimeLimitEnforcement(true);

  Options opt = strategyOpt;
  //we have already performed the normalization
  opt.setNormalize(false);
  opt.setForcedOptionValues();
  opt.checkGlobalOptionConstraints();
  *env.options = opt; //just temporarily until we get rid of dependencies on env.options in solving

  if (outputAllowed()) {
    env.beginOutput();
    addCommentSignForSZS(env.out()) << opt.testId() << " on " << opt.problemName() << endl;
    env.endOutput();
  }

  Saturation::ProvingHelper::runVampire(*_prb, opt);

  //set return value to zero if we were successful
  if (env.statistics->terminationReason == Statistics::REFUTATION ||
      env.statistics->terminationReason == Statistics::SATISFIABLE) {
    resultValue=0;

    /*
     env.beginOutput();
     lineOutput() << " found solution " << endl;
     env.endOutput();
    */
  }

  System::ignoreSIGHUP(); // don't interrupt now, we need to finish printing the proof !

  bool outputResult = false;
  if (!resultValue) {
    // only successfull vampires get here

    _syncSemaphore.dec(SEM_LOCK); // will block for all accept the first to enter (make sure it's until it has finished printing!)

    if (!_syncSemaphore.get(SEM_PRINTED)) {
      _syncSemaphore.set(SEM_PRINTED,1);
      outputResult = true;
    }
  }

  if((outputAllowed() && resultValue) || outputResult) { // we can report on every failure, but only once on success
    env.beginOutput();
    UIHelper::outputResult(env.out());
    env.endOutput();
  }
  else{
    /*
    if (!resultValue) {
      env.beginOutput();
      addCommentSignForSZS(env.out()) << " found a proof after proof output" << endl;
      env.endOutput();
    }
    */
  }

  if (outputResult) {
    _syncSemaphore.inc(SEM_LOCK); // would be also released after the processes' death, but we are polite and do it already here
  }

  STOP_CHECKING_FOR_ALLOCATOR_BYPASSES;

  exit(resultValue);
} // runSlice

// BELOW ARE TWO LEFT-OVER FUNCTIONS FROM THE ORIGINAL (SINGLE-CHILD) CASC-MODE
// THE CODE WAS KEPT FOR NOW AS IT DOESN'T DIRECTLY CORRESPOND TO ANYTHING ABOVE

/*

void handleSIGINT()
{
  CALL("CASCMode::handleSIGINT");

  env.beginOutput();
  env.out()<<"% Terminated by SIGINT!"<<endl;
  env.out()<<"% SZS status User for "<<env.options->problemName() <<endl;
  env.statistics->print(env.out());
  env.endOutput();
  exit(VAMP_RESULT_STATUS_SIGINT);
}

bool CASCMode::runSlice(Options& opt)
{
  CALL("CASCMode::runSlice");

  pid_t fres=Multiprocessing::instance()->fork();

  if(!fres) {
    childRun(opt);

    INVALID_OPERATION("ForkingCM::childRun should never return.");
  }

  System::ignoreSIGINT();

  int status;
  errno=0;
  pid_t res=waitpid(fres, &status, 0);
  if(res==-1) {
    SYSTEM_FAIL("Error in waiting for forked process.",errno);
  }

  System::heedSIGINT();

  Timer::syncClock();

  if(res!=fres) {
    INVALID_OPERATION("Invalid waitpid return value: "+Int::toString(res)+"  pid of forked Vampire: "+Int::toString(fres));
  }

  ASS(!WIFSTOPPED(status));

  if( (WIFSIGNALED(status) && WTERMSIG(status)==SIGINT) ||
      (WIFEXITED(status) && WEXITSTATUS(status)==3) )  {
    //if the forked Vampire was terminated by SIGINT (Ctrl+C), we also terminate
    //(3 is the return value for this case; see documentation for the
    //@b vampireReturnValue global variable)

    handleSIGINT();
  }

  if(WIFEXITED(status) && WEXITSTATUS(status)==0) {
    //if Vampire succeeds, its return value is zero
    return true;
  }

  return false;
}

*/

