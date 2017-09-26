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
  Shell::Property* property = _prb->getProperty();

  {
    TimeCounter tc(TC_PREPROCESSING);

    //we normalize now so that we don't have to do it in every child Vampire
    ScopedLet<Statistics::ExecutionPhase> phaseLet(env.statistics->phase,Statistics::NORMALIZATION);
    Normalisation norm;
    norm.normalise(*_prb);

    TheoryFinder tf(_prb->units(),property);
    tf.search();
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

  getSchedules(*property,main,fallback);

  // simply insert fallback after main
  Schedule::BottomFirstIterator it(fallback);
  main.loadFromIterator(it);

  int terminationTime = env.remainingTime()/100;

  if (terminationTime <= 0) {
    return false;
  }

  return runSchedule(main,terminationTime);
}

void PortfolioMode::getSchedules(Property& prop, Schedule& quick, Schedule& fallback)
{
  CALL("PortfolioMode::getSchedules");

  switch(env.options->schedule()) {
  case Options::Schedule::CASC:
  case Options::Schedule::CASC_2017:
    Schedules::getCasc2017Schedule(prop,quick,fallback);
    break;
  case Options::Schedule::CASC_SAT:
  case Options::Schedule::CASC_SAT_2017:
    Schedules::getCascSat2017Schedule(prop,quick,fallback);
    break;
  case Options::Schedule::SMTCOMP:
  case Options::Schedule::SMTCOMP_2017:
    Schedules::getSmtcomp2017Schedule(prop,quick,fallback);
    break;
  case Options::Schedule::LTB_HH4_2017:
    Schedules::getLtb2017Hh4Schedule(prop,quick);
    break;
  case Options::Schedule::LTB_HLL_2017:
    Schedules::getLtb2017HllSchedule(prop,quick);
    break;
  case Options::Schedule::LTB_ISA_2017:
    Schedules::getLtb2017IsaSchedule(prop,quick);
    break;
  case Options::Schedule::LTB_MZR_2017:
    Schedules::getLtb2017MzrSchedule(prop,quick);
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

static ostream& lineOutput()
{
  CALL("PortfolioMode static lineOutput");
  addCommentSignForSZS(env.out());
  return env.out() << "(" << getpid() << ',' << (env.timer->elapsedMilliseconds()/100)/10.0 << ") ";
}

/**
 * Run a schedule.
 * Return true if a proof was found, otherwise return false.
 * It spawns processes by calling runSlice()
 */
bool PortfolioMode::runSchedule(Schedule& schedule, int terminationTime)
{
  CALL("PortfolioMode::runSchedule");

  // keep track of strategies and times they were used with not to repeat useless work
  DHMap<vstring,int> used;

  // compute the number of parallel processes depending on the number of available cores
  unsigned coreNumber = System::getNumberOfCores();
  if (coreNumber < 1) { coreNumber = 1; }

  int parallelProcesses = min(coreNumber,env.options->multicore());

  // if requested is 0 then use (a sensible) max
  if (parallelProcesses == 0) {
    if (coreNumber >= 8) {
      coreNumber = coreNumber-2;
    }
    parallelProcesses = coreNumber;
  }

  if (outputAllowed()) {
    env.beginOutput();
    addCommentSignForSZS(env.out());
    env.out() << "Starting " << (parallelProcesses == 1 ? "sequential " : "") <<
        "portfolio solving with schedule \"" << env.options->scheduleName() << "\"";
    if (parallelProcesses > 1) {
      env.out() << " and " << parallelProcesses << " parallel processes.";
    }
    env.out() << endl;
    env.endOutput();
  }

  int processesLeft = parallelProcesses;
  Schedule::BottomFirstIterator it(schedule);

  int slices = schedule.length();
  while (it.hasNext()) {
    while (processesLeft) {
      slices--;
      ASS_G(processesLeft,0);

      /*
      env.beginOutput();
      lineOutput() << "Slices left: " << slices << endl;
      lineOutput() << "Processes available: " << processesLeft << endl;
      env.endOutput();
      */

      int elapsedTime = milliToDeci(env.timer->elapsedMilliseconds());
      if (elapsedTime >= terminationTime) {
        // time limit reached
        goto finish_up;
      }

      vstring sliceCode = it.next();
      vstring chopped;

      // slice time in deciseconds
      int sliceTime = getSliceTime(sliceCode,chopped);
      int usedTime;
      if (used.find(chopped,usedTime) && usedTime >= sliceTime) {
        // this slice was already used with at least as long time as currently requested
        continue;
      }
      used.insert(chopped,sliceTime);

      int remainingTime = terminationTime - elapsedTime;
      if (sliceTime > remainingTime) {
        sliceTime = remainingTime;
      }
      ASS_GE(sliceTime,0);

      pid_t childId=Multiprocessing::instance()->fork();
      ASS_NEQ(childId,-1);
      if (!childId) {
        //we're in a proving child
        try {
          runSlice(sliceCode,sliceTime); //start proving
        } catch (Exception& exc) {
          if (outputAllowed()) {
            cerr << "% Exception at run slice level" << endl;
            exc.cry(cerr);
          }
          System::terminateImmediately(1); //we didn't find the proof, so we return nonzero status code
        }
        ASSERTION_VIOLATION; //the runSlice function should never return
      }
      Timer::syncClock();
      ASS(childIds.insert(childId));

      if (outputAllowed()) {
        env.beginOutput();
        lineOutput() << "spawned child "<< childId << " with time: " << sliceTime << " (total remaining time " << remainingTime << ")" << endl;
        env.endOutput();
      }

      processesLeft--;
      if (!it.hasNext()) {
        break;
      }
    }

    /*
    env.beginOutput();
    lineOutput() << "No processes available: " << endl;
    env.endOutput();
    */

    if (processesLeft==0) {
      if(waitForChildAndCheckIfProofFound()) { return true; }
      // proof search failed
      processesLeft++;
    }
  }

  finish_up:

  while (parallelProcesses!=processesLeft) {
    ASS_L(processesLeft, parallelProcesses);
    if(waitForChildAndCheckIfProofFound()) { return true; }
    // proof search failed
    processesLeft++;
    Timer::syncClock();
  }
  return false;
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
    time = 10;
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
  UIHelper::portfolioChild=true;

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
    lineOutput() << opt.testId() << " on " << opt.problemName() << endl;
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
    _syncSemaphore.dec(SEM_LOCK); // will block for all accept the first to enter

    if (!_syncSemaphore.get(SEM_PRINTED)) {
      _syncSemaphore.set(SEM_PRINTED,1);
      outputResult = true;
    }

    _syncSemaphore.inc(SEM_LOCK); // would be also released after the processes' death, but we are polite and do it already here
  }

  if(outputResult){
    env.beginOutput();
    UIHelper::outputResult(env.out());
    env.endOutput();
  }
  else{
    /*
    if (!resultValue) {
      env.beginOutput();
      lineOutput() << " found a proof after proof output" << endl;
      env.endOutput();
    }
    */
  }

  exit(resultValue);
} // runSlice
