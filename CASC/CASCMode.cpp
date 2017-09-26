/**
 * @file CASCMode.cpp
 * Implements class CASCMode.
 */

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Portability.hpp"
#include "Lib/Stack.hpp"
#include "Lib/System.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Sys/Multiprocessing.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "CASCMode.hpp"

#define SLOWNESS 1.05

using namespace Lib;
using namespace CASC;

bool CASCMode::perform(int argc, char* argv [])
{
  CALL("CASCMode::perform/2");

  env.timer->makeChildrenIncluded();

  CASCMode cm; // remember what this guy did!
  bool res=cm.perform();

  env.beginOutput();
  if (res) {
    env.out()<<"% Success in time "<<Timer::msToSecondsString(env.timer->elapsedMilliseconds())<<endl;
  }
  else {
    env.out()<<"% Proof not found in time "<<Timer::msToSecondsString(env.timer->elapsedMilliseconds())<<endl;
    if (env.remainingTime()/100>0) {
      env.out()<<"% SZS status GaveUp for "<<env.options->problemName()<<endl;
    }
    else {
      //From time to time we may also be terminating in the timeLimitReached()
      //function in Lib/Timer.cpp in case the time runs out. We, however, output
      //the same string there as well.
      env.out()<<"% SZS status Timeout for "<<env.options->problemName()<<endl;
    }
  }
  if (env.options && env.options->timeStatistics()) {
    TimeCounter::printReport(env.out());
  }
  env.endOutput();

  return res;
}

CASCMode::CASCMode()
{
  CALL("CASCMode::CASCMode");

  _prb = UIHelper::getInputProblem(*env.options);

  {
    TimeCounter tc(TC_PREPROCESSING);

    //we normalize now so that we don't have to do it in every child Vampire
    ScopedLet<Statistics::ExecutionPhase> phaseLet(env.statistics->phase,Statistics::NORMALIZATION);
    Normalisation norm;
    norm.normalise(*_prb);
  }

  _property = _prb->getProperty();
  TheoryFinder tf(_prb->units(),_property);
  tf.search();
}

bool CASCMode::perform()
{
  CALL("CASCMode::perform/0");

  cout << "Hi Geoff, go and have some cold beer while I am trying to solve this very hard problem!\n";
  Schedule quick;
  Schedule fallback;

  getCasc2017Schedule(property,quick,fallback);

  int remainingTime=env.remainingTime()/100;
  if (remainingTime<=0) {
    return false;
  }
  StrategySet used;
  if (runSchedule(quick,remainingTime,used,false)) {
    return true;
  }
  remainingTime=env.remainingTime()/100;
  if (remainingTime<=0) {
    return false;
  }
  return runSchedule(fallback,remainingTime,used,true);
}

unsigned CASCMode::getSliceTime(vstring sliceCode,vstring& chopped)
{
  CALL("CASCMode::getSliceTime");

  unsigned pos=sliceCode.find_last_of('_');
  vstring sliceTimeStr=sliceCode.substr(pos+1);
  chopped.assign(sliceCode.substr(0,pos));
  unsigned sliceTime;
  ALWAYS(Int::stringToUnsignedInt(sliceTimeStr,sliceTime));
  ASS_G(sliceTime,0); //strategies with zero time don't make sense

  unsigned time = (unsigned)(sliceTime * SLOWNESS) + 1;
  if (time < 10) {
    time++;
  }
  return time;
}

/**
 * Run strategies from the null-terminated array @b strategies,
 * so that the sequence would not take longer tham @b ds deciseconds
 *
 * The remaining time is always split between the remaining strategies
 * in the ratio of their hard-coded time (the last number in the
 * slice string).
 *
 * Return true iff the proof or satisfiability was found.
 *
 * For each strategy code, this code stripped off the time information will
 * be saved in ss.
 * If fallback is true and the code was previously in ss, the strategy will
 * not be run
 */
bool CASCMode::runSchedule(Schedule& schedule,unsigned ds,StrategySet& ss,bool fallback)
{
  CALL("CASCMode::runSchedule");

  Schedule::BottomFirstIterator sit(schedule);
  while (sit.hasNext()) {
    vstring sliceCode = sit.next();
    vstring chopped;
    unsigned sliceTime = getSliceTime(sliceCode,chopped);
    if (fallback && ss.contains(chopped)) {
      continue;
    }
    ss.insert(chopped);
    int remainingTime = env.remainingTime()/100;
    if (remainingTime<=0) {
      return false;
    }
    // cast to unsigned is OK since realTimeRemaining is positive
    if (sliceTime > (unsigned)remainingTime) {
      sliceTime = remainingTime;
    }

    env.beginOutput();
    env.out()<<"% remaining time: "<<remainingTime<<" next slice time: "<<sliceTime<<endl;
    env.endOutput();

    if (runSlice(sliceCode,sliceTime)) {
      return true;
    }
  }
  return false;
} // runSchedule

bool CASCMode::runSlice(vstring slice, unsigned ds)
{
  CALL("CASCMode::runSlice");


  // Copy options - it is import options can be copied nicely
  Options opt=*env.options;
  opt.readFromEncodedOptions(slice);
  opt.setTimeLimitInDeciseconds(ds);
  int stl = opt.simulatedTimeLimit();
  if (stl) {
    opt.setSimulatedTimeLimit(int(stl * SLOWNESS));
  }
  return runSlice(opt);
}









void CASCMode::handleSIGINT()
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

/**
 * Do the theorem proving in a forked-off process
 */
void CASCMode::childRun(Options& strategyOpt)
{
  CALL("CASCMode::childRun");

  UIHelper::portfolioChild=true;
  int resultValue=1;
  env.timer->reset();
  env.timer->start();
  TimeCounter::reinitialize();

  Options opt(strategyOpt);

  //we have already performed the normalization
  opt.setNormalize(false);
  opt.setForcedOptionValues();
  opt.checkGlobalOptionConstraints();
  *env.options = opt; //just temporarily until we get rid of dependencies on env.options in solving
  env.options->setTimeLimitInDeciseconds(opt.timeLimitInDeciseconds());

  env.beginOutput();
  env.out()<<opt.testId()<<" on "<<env.options->problemName()<<endl;
  env.endOutput();

  ProvingHelper::runVampire(*_prb,opt);

  //set return value to zero if we were successful
  if(env.statistics->terminationReason==Statistics::REFUTATION ||
      env.statistics->terminationReason==Statistics::SATISFIABLE) {
    resultValue=0;
  }

  env.beginOutput();
  UIHelper::outputResult(env.out());
  env.endOutput();

  exit(resultValue);
}
