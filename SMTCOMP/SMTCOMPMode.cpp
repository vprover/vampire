/**
 * @file SMTCOMPMode.cpp
 * Implements class SMTCOMPMode.
 */
#include <fstream>
#include <cstdlib>
#include <csignal>
#include <sstream>

#include "Lib/Portability.hpp"

#if !COMPILER_MSVC

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"
#include "Lib/StringUtils.hpp"
#include "Lib/System.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Lib/Sys/Multiprocessing.hpp"
#include "Lib/Sys/SyncPipe.hpp"

#include "Shell/Options.hpp"
#include "Shell/Normalisation.hpp"
#include "Saturation/ProvingHelper.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "Parse/TPTP.hpp"

#include "SMTCOMPMode.hpp"

#include "SMTCOMPMode.hpp"

#define SLOWNESS 1.3
#define OUTPUT 0

using namespace SMTCOMP;
using namespace std;
using namespace Lib;
using namespace Lib::Sys;
using namespace Saturation;

/**
 * The function that does all the job: reads the input files and runs
 * Vampires to solve problems.
 */
bool SMTCOMPMode::perform()
{
  CALL("SMTCOMPMode::perform");

  //TODO needed?
  // to prevent from terminating by time limit
  env.options->setTimeLimitInSeconds(100000);

  env.options->setStatistics(Options::Statistics::NONE);

  SMTCOMPMode casc;

  bool resValue;
  try {
      resValue = casc.searchForProof();
  } catch (Exception& exc) {
      cerr << "% Exception at proof search level" << endl;
      exc.cry(cerr);
      System::terminateImmediately(1); //we didn't find the proof, so we return nonzero status code
  }

#if OUTPUT
  env.beginOutput();
  if (resValue) {
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
#endif

  return resValue;
} 

/**
  *
 */
bool SMTCOMPMode::performStrategy(Shell::Property* property)
{
  CALL("SMTCOMPMode::performStrategy");

  Schedule quick;
  Schedule fallback;

  getSchedules(*property,quick,fallback);

  int terminationTime = env.remainingTime()/100; 
  if(terminationTime <= 0){ return false; }

  StrategySet usedSlices;
  if (runSchedule(quick,usedSlices,false,terminationTime)) {
    return true;
  }
  terminationTime = env.remainingTime()/100;
  if (terminationTime <= 0){
    return false;
  }
  return runSchedule(fallback,usedSlices,true,terminationTime);
} // SMTCOMPMode::performStrategy

/**
 *
 */
bool SMTCOMPMode::searchForProof()
{
  CALL("SMTCOMPMode::searchForProof");

  env.timer->makeChildrenIncluded();
  TimeCounter::reinitialize();

  prb = UIHelper::getInputProblem(*env.options); 

  Shell::Property* property = prb->getProperty();

  {
    TimeCounter tc(TC_PREPROCESSING);
    env.statistics->phase=Statistics::NORMALIZATION;
    Normalisation norm;
    norm.normalise(*prb);
  }

  env.statistics->phase=Statistics::UNKNOWN_PHASE;

  // now all the cpu usage will be in children, we'll just be waiting for them
  Timer::setTimeLimitEnforcement(false);

  return performStrategy(property);
} // SMTCOMPMode::perform

static unsigned milliToDeci(unsigned timeInMiliseconds) {
  return timeInMiliseconds/100;
}

/**
 * Run a schedule. 
 * Return true if a proof was found, otherwise return false. 
 * It spawns processes by calling runSlice()
 */
bool SMTCOMPMode::runSchedule(Schedule& schedule,StrategySet& used,bool fallback,int terminationTime)
{
  CALL("SMTCOMPMode::runSchedule");

  // compute the number of parallel processes depending on the
  // number of available cores

#if __APPLE__ || __CYGWIN__
  unsigned coreNumber = 16; // probaby an overestimate! 
#else
  unsigned coreNumber = System::getNumberOfCores();
#endif
  if (coreNumber < 1){
    coreNumber = 1;
  }
  unsigned requested = env.options->multicore();
  int parallelProcesses = min(coreNumber,requested);

  // if requested is 0 then use (sensible) max
  if (parallelProcesses == 0){
    if (coreNumber >=8){
      coreNumber = coreNumber-2;
    }
    parallelProcesses = coreNumber;
  }

  int processesLeft = parallelProcesses;
  Schedule::BottomFirstIterator it(schedule);
 
  int slices = schedule.length();
  while (it.hasNext()) {
    while (processesLeft) {
      slices--;
#if OUTPUT
      SMTCOMPMode::coutLineOutput() << "Slices left: " << slices << endl;
      SMTCOMPMode::coutLineOutput() << "Processes available: " << processesLeft << endl << flush;
#endif
      ASS_G(processesLeft,0);

      int elapsedTime = env.timer->elapsedMilliseconds();
      if (elapsedTime >= terminationTime) {
	// time limit reached
        goto finish_up;
      }

      vstring sliceCode = it.next();
      vstring chopped;

      // slice time in milliseconds
      int sliceTime = SLOWNESS * getSliceTime(sliceCode,chopped);
      if (used.contains(chopped)) {
	// this slice was already used
	continue;
      }
      used.insert(chopped);
      int remainingTime = terminationTime - elapsedTime;
      if (sliceTime > remainingTime) {
	sliceTime = remainingTime;
      }

      ASS_GE(sliceTime,0);
      if (milliToDeci((unsigned)sliceTime) == 0) {
        // can be still zero, due to rounding
        // and zero time limit means no time limit -> the child might never return!

        // time limit reached
        goto finish_up;
      }

      pid_t childId=Multiprocessing::instance()->fork();
      ASS_NEQ(childId,-1);
      if (!childId) {
        //we're in a proving child
        try {
          runSlice(sliceCode,sliceTime); //start proving
        } catch (Exception& exc) {
#if OUTPUT
          cerr << "% Exception at run slice level" << endl;
          exc.cry(cerr);
#endif
          System::terminateImmediately(1); //we didn't find the proof, so we return nonzero status code
        }
        ASSERTION_VIOLATION; //the runSlice function should never return
      }
      Timer::syncClock();
      ASS(childIds.insert(childId));
#if OUTPUT
      SMTCOMPMode::coutLineOutput() << "slice pid "<< childId << " slice: " << sliceCode
				 << " time: " << (sliceTime/100)/10.0 << endl << flush;
#endif
      processesLeft--;
      if (!it.hasNext()) {
	break;
      }
    }

#if OUTPUT
    SMTCOMPMode::coutLineOutput() << "No processes available: " << endl << flush;
#endif
    if (processesLeft==0) {
      if(waitForChildAndCheckIfProofFound()){ return true; }
      // proof search failed
      processesLeft++;
    }
  }

  finish_up:

  while (parallelProcesses!=processesLeft) {
    ASS_L(processesLeft, parallelProcesses);
    if(waitForChildAndCheckIfProofFound()){ return true; }
    // proof search failed
    processesLeft++;
    Timer::syncClock();
  }
  return false;
} // SMTCOMPMode::runSchedule

/**
 * Wait for termination of a child 
 * return true if a proof was found
 */
bool SMTCOMPMode::waitForChildAndCheckIfProofFound()
{
  CALL("SMTCOMPMode::waitForChildAndCheckIfProofFound");
  ASS(!childIds.isEmpty());

  int resValue;
  pid_t finishedChild = Multiprocessing::instance()->waitForChildTermination(resValue);
#if VDEBUG
  ALWAYS(childIds.remove(finishedChild));
#endif
  if (!resValue) {
    // we have found the proof. It has been already written down by the writter child,
#if OUTPUT
    SMTCOMPMode::coutLineOutput() << "terminated slice pid " << finishedChild << " (success)" << endl << flush;
#endif
    return true;
  }
  // proof not found
#if OUTPUT
  SMTCOMPMode::coutLineOutput() << "terminated slice pid " << finishedChild << " (fail)" << endl << flush;
#endif
  return false;
} // waitForChildAndExitWhenProofFound


/**
 * Run a slice given by its code using the specified time limit.
 */
void SMTCOMPMode::runSlice(vstring sliceCode, unsigned timeLimitInMilliseconds)
{
  CALL("SMTCOMPMode::runSlice");

  Options opt = *env.options;
  opt.readFromEncodedOptions(sliceCode);
  opt.setTimeLimitInDeciseconds(milliToDeci(timeLimitInMilliseconds));
  int stl = opt.simulatedTimeLimit();
  if (stl) {
    opt.setSimulatedTimeLimit(int(stl * SLOWNESS));
  }
  runSlice(opt);
} // runSlice

/**
 * Run a slice given by its options
 */
void SMTCOMPMode::runSlice(Options& strategyOpt)
{
  CALL("SMTCOMPMode::runSlice(Option&)");

  System::registerForSIGHUPOnParentDeath();
  UIHelper::cascModeChild=true;

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

#if OUTPUT
  env.beginOutput();
  SMTCOMPMode::lineOutput() << opt.testId() << " on " << opt.problemName() << endl;
  env.endOutput();
#endif

  ProvingHelper::runVampire(*prb, opt);

  //set return value to zero if we were successful
  if (env.statistics->terminationReason == Statistics::REFUTATION ||
      env.statistics->terminationReason == Statistics::SATISFIABLE) {
    resultValue=0;
#if OUTPUT
     env.beginOutput();
     SMTCOMPMode::lineOutput() << " found solution " << endl;
     env.endOutput();
#endif
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
#if OUTPUT
    if (!resultValue) {
      env.beginOutput();
      SMTCOMPMode::lineOutput() << " found a proof after proof output" << endl;
      env.endOutput();
    }
#endif
  }

  exit(resultValue);
} // SMTCOMPMode::runSlice

/**
 * Return the intended slice time in milliseconds and assign the slice
 * vstring with chopped time limit to @b chopped.
 */
unsigned SMTCOMPMode::getSliceTime(vstring sliceCode,vstring& chopped)
{
  CALL("SMTCOMPMode::getSliceTime");

  unsigned pos = sliceCode.find_last_of('_');
  vstring sliceTimeStr = sliceCode.substr(pos+1);
  chopped.assign(sliceCode.substr(0,pos));
  unsigned sliceTime;
  ALWAYS(Int::stringToUnsignedInt(sliceTimeStr,sliceTime));
  ASS_G(sliceTime,0); //strategies with zero time don't make sense

  unsigned time = sliceTime + 1;
  if (time < 10) {
    time = 10;
  }
  // convert deciseconds to milliseconds
  return time * 100;
} // getSliceTime

/**
 * Start line output by writing the TPTP comment sign and the current
 * elapsed time in milliseconds to env.out(). Returns env.out()
 */
ostream& SMTCOMPMode::lineOutput()
{
  CALL("SMTCOMPMode::lineOutput");
  return env.out() << "% (" << getpid() << ',' << (env.timer->elapsedMilliseconds()/100)/10.0 << ") ";
} // SMTCOMPMode::lineOutput

/**
 * Start line output by writing the TPTP comment sign and the current
 * elapsed time in milliseconds to cout. Returns cout
 */
ostream& SMTCOMPMode::coutLineOutput()
{
  CALL("SMTCOMPMode::lineOutput");
  return cout << "% (" << getpid() << ',' << (env.timer->elapsedMilliseconds()/100)/10.0 << ") ";
} // SMTCOMPMode::coutLineOutput

/**
 * Get schedules for a problem of given property.
 * The schedules are to be executed from the toop of the stack,
 */
void SMTCOMPMode::getSchedules(Property& property, Schedule& quick, Schedule& fallback)
{

    switch (property.getSMTLIBLogic()) {
    case SMT_AUFDTLIA:
      quick.push("dis+1010_2_add=off:afr=on:afp=40000:afq=1.1:amm=sco:anc=none:ile=on:irw=on:lma=on:nm=64:nwc=1:sas=z3:sac=on:sp=reverse_arity:tac=light:tar=off:updr=off_0");
      quick.push("ott+1_5:1_afr=on:afp=4000:afq=1.2:amm=off:anc=none:bs=unit_only:br=off:cond=on:fsr=off:gs=on:gsem=on:ile=on:nm=64:newcnf=on:nwc=1:sac=on:sp=reverse_arity:urr=on:updr=off_0");
      quick.push("lrs-1_1_aac=none:add=off:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:gsp=input_only:gs=on:gsem=off:ile=on:lma=on:nm=64:nwc=1.5:sas=z3:stl=30:urr=on_0");
      quick.push("dis+11_4_add=large:afp=100000:afq=1.2:anc=none:fsr=off:gs=on:gsem=on:ile=on:lcm=predicate:nm=64:nwc=1.2:sas=z3:tac=light:tar=off:updr=off_0");
      quick.push("ins+11_3_av=off:gs=on:gsem=on:ile=on:igbrr=0.9:igrr=1/64:igrp=1400:igs=1004:igwr=on:nm=6:nwc=2.5:sp=occurrence:urr=on_0");
      quick.push("lrs+1011_3_add=large:afr=on:afp=100000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sac=on:tar=off_0");
      quick.push("dis+1010_1_av=off:ile=on:irw=on:nm=2:nwc=1:sas=z3:sp=occurrence:tar=off:urr=on_0");
      quick.push("dis+1011_2_add=large:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:cond=on:gs=on:ile=on:irw=on:nm=64:newcnf=on:nwc=1:urr=on_0");
      quick.push("dis+11_3_add=large:afr=on:afp=4000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=on:ile=on:irw=on:lma=on:nm=64:nwc=1:tac=light:tar=off_0");
      quick.push("lrs-1_12_av=off:bd=off:er=filter:fsr=off:ile=on:irw=on:lma=on:lwlo=on:nm=32:nwc=2:stl=30:sp=occurrence:updr=off_0");
      quick.push("dis+1011_10_av=off:er=filter:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=64:nwc=5:sp=occurrence:tac=light:tar=off:updr=off_0");
      quick.push("dis-11_4:1_aac=none:add=large:afp=4000:afq=1.2:anc=none:fsr=off:ile=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1:sas=z3:sp=occurrence_0");
      quick.push("dis+1002_3_add=off:afr=on:amm=off:anc=none:cond=on:ile=on:lma=on:nm=64:nwc=1:nicw=on:sac=on:sp=reverse_arity:tac=axiom:tar=off:updr=off_0");
      quick.push("dis+1011_1_add=off:afp=1000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:ile=on:lma=on:nm=64:newcnf=on:nwc=1:sos=all:sac=on:sp=occurrence:urr=on_0");
      quick.push("lrs+1010_5:4_afp=100000:afq=1.2:anc=none:cond=on:fsr=off:ile=on:irw=on:nm=64:nwc=1:stl=30:sac=on:sp=occurrence:urr=on_9");
      quick.push("dis+2_12_av=off:bsr=on:fsr=off:ile=on:lma=on:nwc=1:sos=all:sp=occurrence:tar=off:urr=on:updr=off_0");
      quick.push("dis+11_5_add=large:afr=on:afp=10000:afq=1.2:anc=none:gs=on:gsem=on:ile=on:irw=on:lma=on:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:sp=reverse_arity:urr=on:updr=off_273");
      quick.push("dis+1011_2:3_add=large:afr=on:afp=40000:afq=1.0:anc=none:br=off:cond=on:gs=on:gsem=on:ile=on:irw=on:lma=on:lwlo=on:nwc=1:sos=on:sac=on:sp=occurrence:tac=axiom:tar=off:urr=on:updr=off_264");
      quick.push("lrs+11_1_add=off:afp=100000:afq=1.4:amm=off:anc=none:bsr=on:fsr=off:gs=on:ile=on:nm=64:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:updr=off_0");
      return;

    case SMT_UFDTLIA:
      quick.push("dis+1011_2:3_add=large:afr=on:afp=40000:afq=1.0:anc=none:br=off:cond=on:gs=on:gsem=on:ile=on:irw=on:lma=on:lwlo=on:nwc=1:sos=on:sac=on:sp=occurrence:tac=axiom:tar=off:urr=on:updr=off_5");
      quick.push("ott+1_5:1_afr=on:afp=4000:afq=1.2:amm=off:anc=none:bs=unit_only:br=off:cond=on:fsr=off:gs=on:gsem=on:ile=on:nm=64:newcnf=on:nwc=1:sac=on:sp=reverse_arity:urr=on:updr=off_2");
      quick.push("dis+1004_1_add=off:afr=on:afp=1000:afq=1.1:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=from_current:gsem=on:ile=on:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1:sas=z3:sp=occurrence:tac=light:tar=off:tha=off:thi=all:urr=on:uhcvi=on_6");
      quick.push("lrs-1_1_aac=none:add=off:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:gsp=input_only:gs=on:gsem=off:ile=on:lma=on:nm=64:nwc=1.5:sas=z3:stl=30:urr=on_5");
      quick.push("dis+1011_1_add=off:afp=1000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:ile=on:lma=on:nm=64:newcnf=on:nwc=1:sos=all:sac=on:sp=occurrence:urr=on_0");
      quick.push("dis+11_3_add=large:afr=on:afp=4000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=on:ile=on:irw=on:lma=on:nm=64:nwc=1:tac=light:tar=off_0");
      quick.push("dis+1011_2_add=large:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:cond=on:gs=on:ile=on:irw=on:nm=64:newcnf=on:nwc=1:urr=on_0");
      quick.push("lrs+1010_5:4_afp=100000:afq=1.2:anc=none:cond=on:fsr=off:ile=on:irw=on:nm=64:nwc=1:stl=30:sac=on:sp=occurrence:urr=on_229");
      quick.push("dis+1011_10_av=off:er=filter:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=64:nwc=5:sp=occurrence:tac=light:tar=off:updr=off_0");
      quick.push("dis+1010_1_av=off:ile=on:irw=on:nm=2:nwc=1:sas=z3:sp=occurrence:tar=off:urr=on_0");
      quick.push("ins+11_3_av=off:gs=on:gsem=on:ile=on:igbrr=0.9:igrr=1/64:igrp=1400:igs=1004:igwr=on:nm=6:nwc=2.5:sp=occurrence:urr=on_0");
      quick.push("dis+11_5_add=large:afr=on:afp=10000:afq=1.2:anc=none:gs=on:gsem=on:ile=on:irw=on:lma=on:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:sp=reverse_arity:urr=on:updr=off_0");
      quick.push("lrs+1011_3_add=large:afr=on:afp=100000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sac=on:tar=off_0");
      quick.push("dis+1010_2_add=off:afr=on:afp=40000:afq=1.1:amm=sco:anc=none:ile=on:irw=on:lma=on:nm=64:nwc=1:sas=z3:sac=on:sp=reverse_arity:tac=light:tar=off:updr=off_0");
      quick.push("dis+2_12_av=off:bsr=on:fsr=off:ile=on:lma=on:nwc=1:sos=all:sp=occurrence:tar=off:urr=on:updr=off_0");
      quick.push("dis+11_4_add=large:afp=100000:afq=1.2:anc=none:fsr=off:gs=on:gsem=on:ile=on:lcm=predicate:nm=64:nwc=1.2:sas=z3:tac=light:tar=off:updr=off_0");
      quick.push("dis-11_4:1_aac=none:add=large:afp=4000:afq=1.2:anc=none:fsr=off:ile=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1:sas=z3:sp=occurrence_0");
      quick.push("lrs-1_12_av=off:bd=off:er=filter:fsr=off:ile=on:irw=on:lma=on:lwlo=on:nm=32:nwc=2:stl=30:sp=occurrence:updr=off_0");
      quick.push("dis+1002_3_add=off:afr=on:amm=off:anc=none:cond=on:ile=on:lma=on:nm=64:nwc=1:nicw=on:sac=on:sp=reverse_arity:tac=axiom:tar=off:updr=off_0");
      quick.push("lrs+11_1_add=off:afp=100000:afq=1.4:amm=off:anc=none:bsr=on:fsr=off:gs=on:ile=on:nm=64:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:updr=off_0");
      return;

    case SMT_UFDT:
      quick.push("dis+1011_2_add=large:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:cond=on:gs=on:ile=on:irw=on:nm=64:newcnf=on:nwc=1:urr=on_0");
      quick.push("lrs+11_8:1_add=large:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=fast:gs=on:gsaa=full_model:inw=on:ile=on:lcm=predicate:nm=4:newcnf=on:nwc=1:stl=30:sp=reverse_arity:tha=off:urr=on_224");
      quick.push("dis+11_4_add=large:afp=100000:afq=1.2:anc=none:fsr=off:gs=on:gsem=on:ile=on:lcm=predicate:nm=64:nwc=1.2:sas=z3:tac=light:tar=off:updr=off_1");
      quick.push("ott+1003_14_av=off:fsr=off:fde=unused:ile=on:lcm=predicate:nm=0:newcnf=on:nwc=1:sp=occurrence:uhcvi=on_11");
      quick.push("dis-11_4:1_aac=none:add=large:afp=4000:afq=1.2:anc=none:fsr=off:ile=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1:sas=z3:sp=occurrence_25");
      quick.push("lrs+1_8_av=off:bd=off:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=off:ile=on:lcm=reverse:nm=6:newcnf=on:nwc=1:stl=30:sp=reverse_arity:tar=off:urr=ec_only_0");
      quick.push("dis+1011_2:3_add=large:afr=on:afp=40000:afq=1.0:anc=none:br=off:cond=on:gs=on:gsem=on:ile=on:irw=on:lma=on:lwlo=on:nwc=1:sos=on:sac=on:sp=occurrence:tac=axiom:tar=off:urr=on:updr=off_96");
      quick.push("dis+1002_3_add=off:afr=on:amm=off:anc=none:cond=on:ile=on:lma=on:nm=64:nwc=1:nicw=on:sac=on:sp=reverse_arity:tac=axiom:tar=off:updr=off_240");
      quick.push("dis+1004_8_av=off:cond=on:er=filter:fde=unused:ile=on:lma=on:nm=64:newcnf=on:nwc=1:sp=reverse_arity_23");
      quick.push("lrs+11_1_afr=on:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:cond=on:gsp=input_only:gs=on:ile=on:irw=on:nm=6:nwc=1:stl=30:sos=all:sac=on:urr=on_299");
      quick.push("dis+1011_10_av=off:er=filter:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=64:nwc=5:sp=occurrence:tac=light:tar=off:updr=off_0");
      quick.push("lrs+10_3:1_av=off:cond=on:fde=none:ile=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=reverse_arity:tar=off:uhcvi=on_131");
      quick.push("dis+1011_12_afp=100000:afq=1.0:amm=sco:anc=none:fsr=off:fde=unused:gsp=input_only:ile=on:irw=on:nm=64:nwc=1.2:sac=on:sp=occurrence:tac=axiom:tar=off:uhcvi=on_72");
      quick.push("ott+1_5:1_afr=on:afp=4000:afq=1.2:amm=off:anc=none:bs=unit_only:br=off:cond=on:fsr=off:gs=on:gsem=on:ile=on:nm=64:newcnf=on:nwc=1:sac=on:sp=reverse_arity:urr=on:updr=off_573");
      quick.push("dis+1011_4_add=large:afr=on:afp=4000:afq=1.4:anc=none:cond=on:ep=RS:fsr=off:gs=on:gsaa=from_current:ile=on:lwlo=on:nm=64:nwc=1:sos=all:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_143");
      quick.push("ott+1_8:1_add=large:afp=10000:afq=1.0:amm=sco:anc=none:bd=off:bsr=on:fsr=off:fde=unused:ile=on:irw=on:nm=0:newcnf=on:nwc=1:sas=z3:sp=occurrence:updr=off:uhcvi=on_99");
      quick.push("dis+1004_16_av=off:fsr=off:fde=unused:ile=on:irw=on:nm=0:newcnf=on:nwc=1.1:sp=reverse_arity:urr=on_181");
      quick.push("dis+1003_8_afr=on:anc=none:bd=preordered:ile=on:nm=64:newcnf=on:nwc=1:sas=z3:sac=on:sp=reverse_arity:updr=off:uhcvi=on_240");
      quick.push("dis+1003_2:1_afr=on:afp=100000:afq=1.1:anc=none:cond=on:fde=unused:ile=on:lma=on:newcnf=on:nwc=1:sp=occurrence:tar=off:uhcvi=on_284");
      quick.push("lrs-1_12_av=off:bd=off:er=filter:fsr=off:ile=on:irw=on:lma=on:lwlo=on:nm=32:nwc=2:stl=30:sp=occurrence:updr=off_0");
      quick.push("dis+2_12_av=off:bsr=on:fsr=off:ile=on:lma=on:nwc=1:sos=all:sp=occurrence:tar=off:urr=on:updr=off_0");
      quick.push("dis+1010_2_add=off:afr=on:afp=40000:afq=1.1:amm=sco:anc=none:ile=on:irw=on:lma=on:nm=64:nwc=1:sas=z3:sac=on:sp=reverse_arity:tac=light:tar=off:updr=off_0");
      quick.push("lrs+1011_3_add=large:afr=on:afp=100000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sac=on:tar=off_291");
      quick.push("dis+11_5_add=large:afr=on:afp=10000:afq=1.2:anc=none:gs=on:gsem=on:ile=on:irw=on:lma=on:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:sp=reverse_arity:urr=on:updr=off_0");
      quick.push("dis+1011_1_add=off:afp=1000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:ile=on:lma=on:nm=64:newcnf=on:nwc=1:sos=all:sac=on:sp=occurrence:urr=on_0");
      quick.push("ott+10_4:1_av=off:br=off:cond=fast:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:ile=on:lcm=reverse:nm=64:nwc=1:sos=theory:sp=occurrence:tac=light:tar=off:urr=on:uhcvi=on_0");
      quick.push("dis+1010_1_av=off:ile=on:irw=on:nm=2:nwc=1:sas=z3:sp=occurrence:tar=off:urr=on_205");
      quick.push("lrs+11_1_add=off:afp=100000:afq=1.4:amm=off:anc=none:bsr=on:fsr=off:gs=on:ile=on:nm=64:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:updr=off_185");
      quick.push("lrs+1010_5:4_afp=100000:afq=1.2:anc=none:cond=on:fsr=off:ile=on:irw=on:nm=64:nwc=1:stl=30:sac=on:sp=occurrence:urr=on_288");
      quick.push("lrs-11_4:1_afp=100000:afq=1.2:amm=off:anc=all_dependent:bs=unit_only:fsr=off:fde=none:gs=on:gsem=on:ile=on:lma=on:nm=64:nwc=1:stl=30:sp=reverse_arity:updr=off:uhcvi=on_232");
      quick.push("lrs-1_1_aac=none:add=off:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:gsp=input_only:gs=on:gsem=off:ile=on:lma=on:nm=64:nwc=1.5:sas=z3:stl=30:urr=on_286");
      quick.push("dis+1010_5_add=off:afp=100000:afq=1.0:amm=sco:anc=none:fsr=off:fde=none:gsp=input_only:gs=on:gsaa=from_current:ile=on:nm=64:nwc=1:sas=z3:tar=off:updr=off_0");
      quick.push("lrs+10_3:2_av=off:bce=on:cond=on:er=filter:fsr=off:fde=unused:gs=on:gsem=on:ile=on:irw=on:nm=6:nwc=1:stl=30:sos=all:tac=light:tar=off:updr=off:uhcvi=on_10");
      quick.push("lrs+10_5:1_av=off:fde=unused:ile=on:lwlo=on:nwc=1.1:stl=90:sp=occurrence:urr=on_382");
      quick.push("lrs-11_4_acc=on:afr=on:afp=40000:afq=1.4:amm=off:anc=none:br=off:bce=on:cond=fast:fde=none:gs=on:ile=on:irw=on:nm=0:newcnf=on:nwc=1.1:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=on:updr=off_277");
      quick.push("dis+11_3_add=large:afr=on:afp=4000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=on:ile=on:irw=on:lma=on:nm=64:nwc=1:tac=light:tar=off_0");
      quick.push("ins+11_3_av=off:gs=on:gsem=on:ile=on:igbrr=0.9:igrr=1/64:igrp=1400:igs=1004:igwr=on:nm=6:nwc=2.5:sp=occurrence:urr=on_269");
      return;

    case SMT_LIA:
      quick.push("dis+1011_8_afp=10000:afq=1.2:amm=sco:anc=none:bce=on:gs=on:gsem=off:ile=on:lma=on:nm=16:newcnf=on:nwc=2.5:sas=z3:sos=all:sac=on:sp=occurrence:updr=off_12");
      quick.push("lrs+10_20_add=off:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bs=unit_only:bce=on:fde=unused:gs=on:gsaa=full_model:gsem=on:ile=on:nm=16:newcnf=on:nwc=1:sas=z3:stl=30:sp=occurrence:tha=off:thi=all:updr=off_161");
      quick.push("lrs+1002_128_aac=none:acc=model:add=large:afr=on:afp=1000:afq=1.1:anc=all_dependent:bd=preordered:ccuc=first:cond=fast:fde=unused:ile=on:irw=on:lma=on:newcnf=on:nwc=1:nicw=on:stl=30:sos=all:sac=on_15");
      return;

    case SMT_UFNIA:
      quick.push("lrs+11_5:4_av=off:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=32:newcnf=on:nwc=1.3:stl=30:sp=reverse_arity:updr=off_63");
      quick.push("lrs+1002_5:4_add=large:afr=on:afp=40000:afq=2.0:anc=none:cond=on:inw=on:ile=on:nm=64:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:tha=off:updr=off_109");
      quick.push("dis+11_10_av=off:cond=on:fsr=off:inw=on:ile=on:irw=on:lma=on:nm=0:nwc=1.7:sd=4:ss=axioms:sp=occurrence:thf=on_0");
      quick.push("dis+1011_8_av=off:bd=off:bsr=on:bce=on:cond=on:fsr=off:fde=unused:ile=on:nm=64:nwc=1.1:sd=10:ss=axioms:st=1.5:sos=all:sp=reverse_arity:tha=off_569");
      quick.push("ott+1003_5_av=off:cond=on:fde=none:inw=on:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.5:ss=axioms:st=5.0:updr=off_0");
      quick.push("ott+1010_7_av=off:fsr=off:fde=none:lma=on:nm=2:newcnf=on:nwc=1.3:sos=on:sp=reverse_arity:uhcvi=on_194");
      quick.push("dis+10_10_av=off:gs=on:gsem=off:inw=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sos=on:sp=reverse_arity_0");
      quick.push("lrs+11_1_add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:fsr=off:gs=on:gsem=on:inw=on:ile=on:nm=64:newcnf=on:nwc=1:stl=30:sp=reverse_arity:tha=off:thf=on:updr=off_197");
      quick.push("lrs+1002_2:1_add=off:afr=on:afp=4000:afq=1.2:amm=off:br=off:fsr=off:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:urr=on:uhcvi=on_0");
      quick.push("lrs-11_5_add=off:afr=on:afp=100000:afq=1.0:anc=all:bs=unit_only:cond=fast:fsr=off:ile=on:irw=on:lcm=reverse:lwlo=on:nwc=1.7:nicw=on:stl=30:sos=on:sac=on:sp=reverse_arity:tha=off:urr=on_0");
      quick.push("lrs+1010_1_av=off:fde=unused:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_128");
      quick.push("dis+10_2_av=off:fsr=off:ile=on:lcm=reverse:lma=on:nm=16:newcnf=on:nwc=1.7:sos=all:sp=reverse_arity:tha=off:updr=off_0");
      quick.push("dis+10_28_av=off:cond=on:fsr=off:gsp=input_only:gs=on:ile=on:lma=on:nm=64:nwc=1:sos=all:sp=occurrence:tha=off:thf=on:updr=off_17");
      quick.push("lrs+1011_3:1_add=off:afr=on:afp=4000:afq=2.0:amm=off:anc=none:bce=on:ep=RS:gs=on:ile=on:lma=on:nm=64:newcnf=on:nwc=1.2:stl=30:sp=occurrence:tha=off_5");
      quick.push("dis+11_3_av=off:cond=on:fsr=off:ile=on:irw=on:nm=64:newcnf=on:nwc=1:sp=reverse_arity:tha=off:updr=off:uhcvi=on_117");
      quick.push("lrs+11_8:1_add=off:afr=on:amm=off:anc=none:fsr=off:inw=on:ile=on:nm=2:newcnf=on:nwc=1.2:sas=z3:stl=30:sp=occurrence_0");
      quick.push("ott-11_16_av=off:cond=fast:er=filter:fde=none:gsp=input_only:ile=on:irw=on:lcm=predicate:nm=16:nwc=1.2:sos=all:sp=reverse_arity:tha=off:thi=full:updr=off_0");
      quick.push("dis+2_2_afr=on:afp=100000:afq=1.2:amm=off:anc=none:bsr=on:cond=on:gs=on:gsem=on:inw=on:ile=on:irw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=1.1:sas=z3:sac=on:tha=off:updr=off_58");
      quick.push("lrs+1002_5_av=off:cond=fast:fsr=off:fde=unused:gs=on:ile=on:lma=on:lwlo=on:nm=64:nwc=1.7:stl=30:sp=reverse_arity_0");
      quick.push("ott+11_2_av=off:inw=on:ile=on:irw=on:lcm=reverse:lma=on:nm=6:nwc=1.5:sp=occurrence:updr=off_158");
      quick.push("ott-11_10_av=off:cond=on:gs=on:irw=on:lcm=predicate:nm=2:newcnf=on:nwc=1:sos=all:tha=off:updr=off_0");
      quick.push("lrs+10_10_av=off:br=off:er=filter:fsr=off:fde=none:irw=on:lcm=reverse:lma=on:lwlo=on:nm=0:newcnf=on:nwc=1:stl=30:tha=off:urr=on:updr=off_0");
      quick.push("lrs+10_3:1_acc=model:afp=10000:afq=2.0:anc=none:ccuc=first:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sos=all_0");
      quick.push("lrs+11_3:1_av=off:lma=on:nm=2:newcnf=on:nwc=1.3:stl=30:sp=reverse_arity:tha=off:thf=on_0");
      quick.push("dis+10_2_add=off:amm=off:anc=none:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:ile=on:irw=on:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off:updr=off:uhcvi=on_75");
      quick.push("dis+1002_2:3_av=off:bs=on:bce=on:cond=fast:ile=on:nm=2:newcnf=on:nwc=1:sp=occurrence:tha=off:thi=strong_79");
      quick.push("lrs+4_3_av=off:bd=preordered:fde=none:inw=on:ile=on:nm=64:newcnf=on:nwc=1:stl=30:tha=off:thf=on:updr=off:uhcvi=on_8");
      quick.push("ott+1011_5:1_add=off:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:bsr=on:inw=on:ile=on:lma=on:nm=2:nwc=1.5:sas=z3:sos=theory:thf=on:updr=off_0");
      quick.push("lrs+11_6_av=off:bsr=on:cond=fast:fde=none:gs=on:gsem=off:irw=on:nm=0:newcnf=on:nwc=1:stl=30:sos=on_0");
      quick.push("dis+1003_4:1_add=large:afp=10000:afq=1.4:amm=off:anc=none:bd=off:cond=fast:fsr=off:fde=none:gs=on:ile=on:lma=on:nm=64:nwc=1.2:sas=z3:sp=reverse_arity:tha=off:urr=ec_only_19");
      quick.push("ott+4_2:1_av=off:bd=off:bs=on:cond=on:gs=on:gsem=on:ile=on:irw=on:nm=64:newcnf=on:nwc=4:sp=occurrence:thf=on_0");
      quick.push("lrs+10_5:4_av=off:bd=off:fsr=off:fde=none:lcm=reverse:lma=on:newcnf=on:nwc=1:stl=30:tha=off:urr=on:updr=off_173");
      quick.push("dis-1_128_av=off:bs=on:fde=unused:ile=on:irw=on:nm=32:nwc=1.1:sos=all:tha=off:thi=full:uwa=one_side_constant:uhcvi=on_355");
      quick.push("lrs-10_12_av=off:bd=off:fsr=off:ile=on:nm=4:nwc=1.2:stl=30:sd=7:ss=axioms:st=5.0:sp=reverse_arity_0");
      quick.push("lrs+11_5:1_afr=on:afp=10000:afq=1.2:amm=off:anc=none:fsr=off:gs=on:inw=on:ile=on:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off_150");
      quick.push("dis+10_5_av=off:bd=off:fsr=off:irw=on:lwlo=on:nm=0:newcnf=on:nwc=1:sp=occurrence:tha=off:updr=off_0");
      quick.push("lrs+1010_5:4_aac=none:add=off:afp=40000:afq=1.2:amm=sco:anc=none:fsr=off:ile=on:lcm=predicate:nm=64:nwc=1:stl=30:ss=axioms:st=1.2:sac=on:sp=reverse_arity:updr=off_0");
      quick.push("lrs-11_2:3_av=off:bd=off:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=60:sp=reverse_arity_0");
      quick.push("ott+11_5:4_aac=none:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:bce=on:cond=on:fsr=off:fde=unused:ile=on:irw=on:lma=on:nm=6:newcnf=on:nwc=1:nicw=on:sas=z3:tha=off:updr=off_31");
      quick.push("dis+1_4_av=off:bd=off:cond=fast:ile=on:lcm=reverse:lma=on:nm=2:nwc=1.1:tha=off:updr=off_0");
      quick.push("lrs+10_2:1_add=off:afp=4000:afq=2.0:amm=sco:anc=none:bs=unit_only:br=off:cond=on:inw=on:ile=on:lma=on:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:urr=on:updr=off_0");
      quick.push("lrs+11_1_av=off:bd=off:bsr=on:cond=on:fsr=off:ile=on:nm=64:newcnf=on:nwc=1:stl=30:tha=off:updr=off_0");
      quick.push("lrs+2_8:1_add=off:afp=40000:afq=1.0:anc=none:fde=unused:gs=on:ile=on:irw=on:lcm=reverse:nm=64:nwc=3:sas=z3:stl=30:sp=occurrence:urr=on:uhcvi=on_13");
      quick.push("dis+11_3_afr=on:afp=40000:afq=2.0:amm=off:anc=none:bd=off:cond=fast:fsr=off:fde=unused:ile=on:lma=on:nm=64:nwc=1:sos=all:sac=on:sp=reverse_arity:tha=off_0");
      quick.push("lrs+11_3:1_av=off:cond=on:inw=on:ile=on:irw=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=reverse_arity:tha=off:updr=off_0");
      quick.push("ott+3_3_av=off:cond=on:gsp=input_only:gs=on:ile=on:nm=64:nwc=1:tha=off:thi=all:updr=off:uhcvi=on_0");
      quick.push("lrs+11_4_av=off:bd=off:fde=unused:ile=on:lwlo=on:nm=32:nwc=1:stl=90:sd=5:ss=axioms:sp=occurrence:thi=strong:uhcvi=on_0");
      quick.push("dis+1011_32_av=off:bd=off:inw=on:irw=on:lwlo=on:nm=16:nwc=3:sd=2:ss=axioms:st=5.0:sp=occurrence:tha=off_0");
      quick.push("lrs+1002_1024_add=large:afr=on:amm=off:anc=none:cond=on:fsr=off:ile=on:nm=64:nwc=1.3:stl=30:sd=7:ss=axioms:st=1.2:sp=occurrence_0");
      quick.push("lrs-1_1_av=off:bce=on:cond=fast:er=filter:fsr=off:gsp=input_only:gs=on:ile=on:lcm=reverse:lma=on:nm=6:nwc=1:stl=30:sos=all:sp=reverse_arity:tha=off_0");
      quick.push("lrs-2_10_av=off:fsr=off:ile=on:nwc=1:stl=30:ss=axioms:st=2.0:sos=all:tha=off:uhcvi=on_0");
      quick.push("lrs-1_2_av=off:bsr=on:gs=on:gsem=on:inw=on:ile=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:tha=off_0");
      quick.push("lrs+1011_7_av=off:cond=on:fsr=off:gs=on:gsem=on:ile=on:irw=on:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:tha=off:thf=on_0");
      quick.push("lrs+2_10_add=off:afp=100000:afq=1.1:amm=sco:anc=none:cond=on:gs=on:gsaa=full_model:lcm=reverse:lma=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off_0");
      quick.push("dis+11_4:1_av=off:cond=on:fsr=off:gsp=input_only:ile=on:nm=64:nwc=1:sas=z3:sd=1:ss=axioms:st=3.0:tha=off:thf=on:urr=ec_only_0");
      quick.push("ott+1010_4_av=off:cond=on:fsr=off:lma=on:nm=64:newcnf=on:nwc=1:sp=occurrence:tha=off_0");
      quick.push("lrs+3_10_av=off:bs=unit_only:cond=on:fde=none:ile=on:irw=on:nm=64:nwc=1:stl=30:sos=all:tha=off:thi=strong:updr=off_0");
      quick.push("dis+1002_1_afr=on:afp=1000:afq=1.1:amm=sco:anc=none:cond=on:fsr=off:ile=on:lma=on:nm=4:nwc=1:tha=off:updr=off_6");
      quick.push("ott+11_3:1_av=off:cond=on:er=filter:fsr=off:ile=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=all:tha=off:uhcvi=on_0");
      quick.push("dis+1010_1_av=off:lma=on:newcnf=on:nwc=1:sd=4:ss=axioms:sos=on:sp=reverse_arity_196");
      quick.push("lrs+1002_8_afp=10000:afq=2.0:amm=sco:anc=none:bs=on:cond=on:fsr=off:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1.3:sas=z3:stl=30:sp=reverse_arity:urr=on_37");
      quick.push("lrs-1_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:lcm=reverse:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sp=reverse_arity:tha=off:thf=on:urr=on_210");
      quick.push("lrs+1002_32_av=off:cond=on:fsr=off:gsp=input_only:ile=on:nm=64:newcnf=on:nwc=4:stl=30:sp=reverse_arity_0");
      quick.push("dis+1010_1_afr=on:afp=40000:afq=2.0:amm=off:anc=none:gs=on:ile=on:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off_10");
      quick.push("ott+10_10_av=off:bs=unit_only:cond=on:er=known:fsr=off:irw=on:lcm=reverse:lma=on:nm=64:newcnf=on:nwc=1:sp=occurrence:tha=off:updr=off_0");
      quick.push("lrs+11_3:2_av=off:bd=off:br=off:fde=none:gs=on:gsem=off:inw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=60:sp=occurrence:tha=off:urr=on:uhcvi=on_0");
      quick.push("ott-1_2_aac=none:add=large:afp=4000:afq=1.4:anc=none:bd=off:bs=unit_only:cond=on:fde=none:gsp=input_only:gs=on:gsaa=full_model:gsem=off:inw=on:irw=on:nm=4:newcnf=on:nwc=1:sas=z3:sac=on:sp=reverse_arity:tha=off:thi=full:uwa=all:urr=on:updr=off_0");
      quick.push("lrs+4_5:4_av=off:bd=off:cond=on:fsr=off:irw=on:lwlo=on:nm=0:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_143");
      quick.push("ott+1_5:1_av=off:bs=unit_only:br=off:gs=on:gsem=off:inw=on:ile=on:nm=64:newcnf=on:nwc=1:sd=4:ss=axioms:st=1.5:sp=occurrence:tha=off:urr=on:uhcvi=on_173");
      quick.push("ott+1010_5:4_add=off:afr=on:afp=1000:afq=1.4:amm=sco:anc=none:bd=off:irw=on:lma=on:nm=64:nwc=1:sos=theory:sp=reverse_arity:updr=off_0");
      quick.push("lrs+1010_8:1_av=off:br=off:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:inw=on:ile=on:irw=on:lma=on:nm=4:nwc=5:stl=30:sos=on:tha=off:thf=on:urr=on_44");
      quick.push("lrs-11_2:3_av=off:br=off:fsr=off:gsp=input_only:inw=on:ile=on:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:tha=off:urr=on:updr=off:uhcvi=on_0");
      quick.push("ott+11_1_av=off:ile=on:nm=64:newcnf=on:nwc=1:tha=off:updr=off_0");
      quick.push("dis+1011_7_afp=4000:afq=1.1:bd=off:bs=unit_only:bsr=on:fsr=off:fde=none:gs=on:gsem=on:lcm=reverse:nm=2:newcnf=on:nwc=1.2:sp=reverse_arity:tha=off:updr=off_0");
      quick.push("lrs+4_64_av=off:bd=off:cond=on:fsr=off:ile=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sp=occurrence_0");
      quick.push("lrs+1011_3:2_add=off:afr=on:afp=10000:afq=1.2:amm=off:anc=all:bd=off:bsr=on:br=off:fde=unused:gs=on:inw=on:irw=on:nm=64:newcnf=on:nwc=1:stl=30:sp=reverse_arity:tha=off:uwa=interpreted_only:urr=on_6");
      quick.push("ott+1011_4_afp=4000:afq=1.1:amm=off:anc=none:bs=unit_only:cond=fast:fsr=off:fde=none:gsp=input_only:ile=on:irw=on:nm=32:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off_45");
      quick.push("dis-11_32_av=off:bd=off:bs=unit_only:cond=fast:er=filter:ile=on:lcm=predicate:nm=32:nwc=5:sos=all:sp=occurrence:tha=off:thi=strong:updr=off:uhcvi=on_0");
      quick.push("dis+3_50_av=off:bd=off:bs=unit_only:cond=on:nm=64:newcnf=on:nwc=1:sp=reverse_arity:tha=off_0");
      quick.push("lrs+11_8_av=off:bs=unit_only:bsr=on:cond=on:er=filter:fsr=off:fde=unused:gsp=input_only:ile=on:nm=6:nwc=1.1:stl=30:sos=all:tha=off:uhcvi=on_0");
      quick.push("lrs+10_7_add=large:afr=on:afp=100000:afq=1.1:anc=all_dependent:bs=on:cond=on:fsr=off:fde=none:gs=on:ile=on:irw=on:nm=64:nwc=1.5:nicw=on:stl=30:sos=all:sac=on:sp=occurrence:tha=off:thi=all:uwa=all:urr=ec_only:updr=off:uhcvi=on_0");
      quick.push("lrs+1003_4:1_av=off:bd=preordered:cond=on:fde=unused:gs=on:ile=on:irw=on:nm=64:nwc=1.2:stl=90:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_322");
      quick.push("dis+11_5:1_av=off:br=off:cond=on:fsr=off:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=0:newcnf=on:nwc=1:tha=off:urr=on_45");
      quick.push("ott+1_10_av=off:ep=RSTC:fsr=off:ile=on:lma=on:newcnf=on:nwc=1:sos=on:tha=off:updr=off_227");
      quick.push("dis+1010_2:1_afp=40000:afq=1.1:anc=none:gsp=input_only:ile=on:irw=on:nm=6:nwc=1:sac=on:tha=off:updr=off_8");
      quick.push("lrs-4_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:cond=on:fde=unused:gs=on:gsem=off:inw=on:ile=on:irw=on:lcm=reverse:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sos=all:sp=occurrence:uwa=ground:urr=on:updr=off:uhcvi=on_132");
      quick.push("dis+1002_1_av=off:bd=off:br=off:cond=on:fsr=off:fde=unused:newcnf=on:nwc=1:sd=5:ss=axioms:st=1.2:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_8");
      quick.push("lrs+1011_2:3_av=off:bsr=on:cond=fast:fsr=off:gsp=input_only:ile=on:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1:stl=30:tha=off:updr=off_87");
      quick.push("lrs+11_5_add=off:afp=40000:afq=1.2:anc=all_dependent:br=off:cond=on:er=filter:fsr=off:fde=unused:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=64:nwc=1:nicw=on:sas=z3:stl=30:ss=axioms:st=2.0:sos=all:sac=on:urr=on_0");
      quick.push("lrs+1011_32_add=large:afp=10000:afq=1.0:amm=sco:anc=none:bs=on:bsr=on:cond=fast:er=filter:fsr=off:inw=on:irw=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:stl=30:sac=on:tha=off:thi=strong:updr=off_0");
      quick.push("dis+1_4:1_acc=on:add=large:afp=4000:afq=1.2:amm=sco:anc=none:ccuc=small_ones:ile=on:lwlo=on:nm=64:nwc=1:tha=off:urr=ec_only:updr=off_228");
      quick.push("lrs+1002_1_av=off:bd=off:fsr=off:fde=none:nm=2:newcnf=on:nwc=1:stl=30:sp=reverse_arity:uhcvi=on_26");
      quick.push("lrs-11_5:4_afp=4000:afq=1.4:amm=sco:anc=none:bd=off:br=off:gs=on:gsem=off:inw=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sos=all:sp=occurrence:urr=on_0");
      quick.push("ott-1_5_av=off:bd=off:cond=fast:er=filter:fsr=off:nwc=1.5:sp=occurrence:tha=off_0");
      quick.push("ott+1002_5:1_add=large:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:br=off:cond=on:fsr=off:gs=on:inw=on:irw=on:lma=on:nm=0:newcnf=on:nwc=1:nicw=on:sos=all:tha=off:urr=on_74");
      quick.push("dis+11_2_afp=40000:afq=2.0:amm=off:anc=none:cond=on:fsr=off:gs=on:gsem=off:inw=on:nm=64:newcnf=on:nwc=1:sas=z3:sp=occurrence:updr=off_12");
      quick.push("lrs+1002_1_av=off:bd=off:bsr=on:cond=on:ile=on:lma=on:nm=64:nwc=1:stl=30:sos=on:sp=reverse_arity_18");
      quick.push("dis-1_2:1_add=large:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:inw=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:tha=off:updr=off_0");
      quick.push("dis+10_3_av=off:ile=on:lcm=reverse:nm=64:newcnf=on:nwc=1:sos=all:sp=reverse_arity:tha=off:updr=off_0");
      quick.push("lrs+1010_1_add=off:afp=40000:afq=1.1:amm=off:anc=none:bd=off:fsr=off:inw=on:ile=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30:sp=occurrence_158");
      quick.push("ott+1004_1_acc=model:afp=4000:afq=1.1:amm=off:anc=all_dependent:cond=on:er=known:fde=unused:gs=on:ile=on:lma=on:nm=2:nwc=1:sp=reverse_arity:tha=off:uwa=all:urr=on:uhcvi=on_0");
      quick.push("lrs+4_3:1_add=off:afp=1000:afq=2.0:anc=none:gs=on:gsem=on:ile=on:lma=on:nm=2:nwc=5:sas=z3:stl=30:sac=on:sp=occurrence:updr=off_8");
      quick.push("ott+1010_2_add=off:amm=sco:bd=off:bce=on:cond=fast:fsr=off:fde=unused:ile=on:nm=64:nwc=1.1:sos=all:sac=on:sp=reverse_arity_0");
      quick.push("lrs+11_5:1_av=off:bd=off:bsr=on:cond=on:gs=on:inw=on:irw=on:lcm=reverse:lma=on:nm=2:newcnf=on:nwc=1.3:stl=30:sp=occurrence:updr=off_0");
      quick.push("ott-1_3:1_av=off:bsr=on:br=off:bce=on:cond=on:fsr=off:fde=unused:irw=on:nm=2:newcnf=on:nwc=2.5:sos=on:sp=occurrence:tha=off:thi=overlap:urr=on:updr=off:uhcvi=on_148");
      quick.push("dis+10_3_add=large:afp=4000:afq=1.4:amm=off:anc=none:cond=on:ep=RS:gs=on:gsaa=from_current:inw=on:ile=on:lma=on:nm=2:newcnf=on:nwc=1:sac=on:tha=off:updr=off_3");
      quick.push("dis+1010_6_av=off:cond=on:er=filter:fsr=off:nm=64:newcnf=on:nwc=1.3:sp=reverse_arity_222");
      quick.push("lrs+11_5:1_av=off:cond=on:gs=on:inw=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:sp=reverse_arity:tha=off:updr=off_0");
      quick.push("dis+1003_28_acc=model:add=large:afp=10000:afq=1.1:amm=off:anc=none:bd=off:ccuc=first:fsr=off:gs=on:gsaa=from_current:ile=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence:tha=off:uwa=ground:uhcvi=on_86");
      quick.push("lrs+10_10_av=off:gs=on:gsem=on:inw=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.1:stl=30:updr=off_8");
      quick.push("lrs-1_2:1_add=off:afp=4000:afq=1.1:amm=sco:anc=none:bd=off:fsr=off:ile=on:irw=on:lcm=reverse:nm=64:nwc=1:sas=z3:stl=30:sos=all:sp=occurrence:urr=on_0");
      quick.push("lrs+11_4_add=large:afp=1000:afq=1.0:amm=sco:anc=none:gs=on:gsem=off:ile=on:irw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sp=reverse_arity_0");
      quick.push("lrs+11_1_afr=on:afp=4000:afq=1.2:amm=sco:anc=none:fsr=off:gs=on:gsem=on:ile=on:irw=on:nm=2:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:tha=off:thf=on:uwa=interpreted_only:urr=on:updr=off_0");
      quick.push("ott+1011_3_av=off:bd=off:bs=on:bsr=on:fsr=off:ile=on:irw=on:lma=on:nm=6:nwc=1.2:sp=occurrence:tha=off_0");
      quick.push("lrs+1011_3:1_av=off:cond=on:gs=on:gsem=off:inw=on:ile=on:irw=on:nm=4:nwc=1:stl=30:sp=reverse_arity:tha=off:urr=on_0");
      quick.push("lrs+1011_64_afp=1000:afq=2.0:anc=none:bd=off:bs=on:bce=on:cond=fast:ile=on:lcm=reverse:lwlo=on:nm=64:nwc=4:nicw=on:stl=60:sd=5:ss=axioms:st=5.0:sp=reverse_arity:uhcvi=on_0");
      quick.push("lrs+10_50_av=off:cond=fast:fde=none:lcm=reverse:nm=64:newcnf=on:nwc=1:stl=30:sp=occurrence:tha=off:uhcvi=on_264");
      quick.push("lrs-11_4:1_aac=none:add=off:afp=10000:afq=1.2:anc=none:fsr=off:ile=on:lma=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:urr=on:updr=off_16");
      quick.push("lrs+2_4_av=off:bd=off:fsr=off:lcm=reverse:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sp=occurrence:tha=off_0");
      quick.push("lrs+1004_5:1_av=off:cond=on:fde=none:irw=on:lcm=reverse:lwlo=on:nm=64:newcnf=on:nwc=1:stl=60:sos=on:sp=reverse_arity:updr=off:uhcvi=on_215");
      quick.push("lrs+1011_3_av=off:bd=off:bs=unit_only:bsr=on:bce=on:cond=fast:fde=unused:gsp=input_only:ile=on:lma=on:nm=16:nwc=10:stl=60:sd=10:ss=axioms:st=1.2:sp=reverse_arity:tha=off:updr=off:uhcvi=on_0");
      quick.push("dis+11_4_add=large:afr=on:afp=40000:afq=2.0:anc=none:fsr=off:gs=on:gsem=off:ile=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:tha=off:thf=on_0");
      quick.push("lrs+11_2:1_afp=1000:afq=1.4:amm=off:anc=none:inw=on:ile=on:irw=on:nm=64:nwc=1:stl=30:sac=on:tha=off:urr=on_73");
      quick.push("dis+1002_3:2_afp=1000:afq=1.2:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:ile=on:irw=on:nm=64:nwc=2.5:sas=z3:sac=on:sp=occurrence:tha=off:uwa=ground:updr=off_0");
      return;

    case SMT_ALIA:
      quick.push("ott-11_24_afr=on:afp=4000:afq=1.0:amm=off:anc=none:bs=unit_only:fsr=off:gsp=input_only:gs=on:gsem=off:ile=on:lma=on:lwlo=on:nm=16:nwc=1.3:nicw=on:sas=z3:sac=on:tha=off:thi=strong:uwa=one_side_constant:urr=on_0");
      quick.push("dis+10_3_afp=100000:afq=2.0:anc=none:cond=on:fsr=off:gs=on:ile=on:irw=on:nm=64:nwc=1:sas=z3:sp=reverse_arity:tha=off_0");
      quick.push("dis-1_20_afr=on:afp=4000:afq=2.0:amm=off:anc=none:bsr=on:fsr=off:inw=on:ile=on:irw=on:lma=on:lwlo=on:nwc=1.1:sas=z3:tha=off_0");
      quick.push("lrs+2_4_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bd=off:bce=on:fde=none:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:stl=30:tha=off:thi=strong:uwa=one_side_interpreted:urr=on:updr=off:uhcvi=on_3");
      quick.push("lrs+1011_12_add=large:afp=4000:afq=2.0:amm=off:anc=none:bs=on:bsr=on:bce=on:cond=fast:fsr=off:ile=on:lwlo=on:nm=64:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:thi=all:uwa=one_side_interpreted:urr=ec_only:updr=off_0");
      quick.push("lrs-1_128_aac=none:add=off:afp=40000:afq=1.0:amm=off:anc=none:fsr=off:inw=on:ile=on:lcm=reverse:lma=on:nm=16:nwc=10:sas=z3:stl=30:sac=on:updr=off_195");
      quick.push("ott-3_2:1_add=off:afr=on:afp=100000:afq=2.0:bsr=on:fsr=off:fde=none:gs=on:ile=on:irw=on:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:nicw=on:sas=z3:sos=all:urr=ec_only_211");
      quick.push("lrs+4_1024_afp=1000:afq=1.2:amm=off:anc=none:bd=off:bs=unit_only:cond=on:fsr=off:fde=none:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:stl=30:sp=occurrence:tha=off:thf=on:urr=on:uhcvi=on_0");
      quick.push("dis-4_8_afr=on:afp=4000:afq=1.0:amm=sco:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:gsem=off:inw=on:irw=on:nm=16:newcnf=on:nwc=1.1:sas=z3:sp=reverse_arity:tha=off:thf=on:urr=on:updr=off_0");
      return;

    case SMT_UFIDL:
      quick.push("dis+11_3_add=large:afp=100000:afq=1.4:amm=off:anc=none:fsr=off:gs=on:ile=on:irw=on:lma=on:nm=32:nwc=1:tha=off:updr=off_1");
      quick.push("dis+10_3_afr=on:afp=1000:afq=1.0:anc=none:cond=on:fsr=off:gs=on:ile=on:irw=on:lwlo=on:nm=32:nwc=1:sos=all:sp=occurrence:urr=on_3");
      return;

    case SMT_LRA:
      quick.push("dis+1_5:1_add=off:afp=40000:afq=1.2:anc=none:bd=off:cond=on:fsr=off:gs=on:ile=on:nm=64:nwc=4:sas=z3:updr=off_69");
      quick.push("ott-4_1_add=off:afp=40000:afq=1.0:anc=none:bce=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:gsem=on:ile=on:irw=on:lcm=reverse:lma=on:nm=6:newcnf=on:nwc=1.5:sas=z3:sos=all:sp=occurrence:updr=off:uhcvi=on_1");
      quick.push("dis+4_5_av=off:cond=on:fsr=off:gs=on:gsem=on:ile=on:irw=on:lwlo=on:nm=6:nwc=1:sos=on:sp=reverse_arity:updr=off_5");
      quick.push("dis+11_2_add=large:afr=on:afp=1000:afq=1.1:anc=none:gs=on:gsaa=full_model:ile=on:irw=on:lma=on:nm=16:nwc=1:sas=z3:sos=on:sac=on:sp=occurrence:thi=strong:uhcvi=on_72");
      quick.push("dis+1002_1_afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:gs=on:gsem=on:ile=on:lma=on:nm=64:nwc=1:sas=z3:sos=on:updr=off_8");
      return;

    case SMT_NIA:
      quick.push("dis+11_10_add=off:afr=on:afp=100000:afq=1.2:amm=off:anc=none:cond=on:gs=on:gsem=on:inw=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=10:sas=z3:sac=on:sp=reverse_arity_1");
      return;

    case SMT_UFLRA:
      quick.push("dis+11_4_afp=4000:afq=1.4:amm=sco:anc=none:gs=on:ile=on:lma=on:nm=64:nwc=1.7:sas=z3:sac=on:sp=occurrence_1");
      return;

    case SMT_AUFNIRA:
      quick.push("dis+1002_5_add=large:afr=on:afp=4000:afq=1.4:amm=off:anc=none:fsr=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sos=all:sac=on:sp=occurrence:updr=off_6");
      quick.push("lrs+10_8_afr=on:afp=4000:afq=1.1:amm=sco:anc=none:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:stl=30:sac=on:tha=off:urr=on:updr=off_2");
      quick.push("lrs+1_3:2_aac=none:afr=on:afp=40000:afq=1.0:anc=none:bs=unit_only:lma=on:nm=64:newcnf=on:nwc=3:sas=z3:stl=30:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_15");
      quick.push("dis+1010_8_add=large:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:fsr=off:gs=on:ile=on:irw=on:nm=64:nwc=1.5:sas=z3:sac=on:sp=reverse_arity_3");
      quick.push("dis+11_2_add=large:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:fde=unused:gs=on:gsaa=full_model:ile=on:nm=64:nwc=1:sas=z3:sos=all:sac=on_6");
      quick.push("dis+1011_24_av=off:fsr=off:inw=on:ile=on:irw=on:nm=64:nwc=1:sos=all:tha=off:updr=off_8");
      quick.push("lrs+1_3:1_acc=model:add=large:afp=40000:afq=1.2:anc=none:bd=off:bsr=on:ccuc=first:fsr=off:inw=on:irw=on:lma=on:nm=64:newcnf=on:nwc=2:stl=30:sp=reverse_arity:updr=off_13");
      quick.push("lrs+11_3_afr=on:afp=40000:afq=1.1:anc=none:fsr=off:gs=on:gsem=off:inw=on:lma=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:stl=30:sos=all:sac=on:sp=occurrence:updr=off_2");
      quick.push("lrs+1010_24_afp=40000:afq=2.0:amm=off:anc=none:cond=fast:gs=on:gsem=off:inw=on:ile=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:tha=off:thf=on:updr=off:uhcvi=on_2");
      quick.push("lrs+1002_3_afr=on:afp=40000:afq=2.0:anc=none:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:inw=on:ile=on:irw=on:lma=on:nm=2:nwc=1.1:nicw=on:sas=z3:stl=30:sac=on:updr=off:uhcvi=on_7");
      quick.push("lrs+11_3:2_add=off:afp=40000:afq=1.0:anc=none:fsr=off:fde=none:gs=on:inw=on:irw=on:lcm=reverse:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sos=all:sp=reverse_arity:thi=strong_1");
      quick.push("lrs+10_24_av=off:bd=off:cond=on:gs=on:gsem=off:inw=on:ile=on:irw=on:nm=64:nwc=2.5:stl=30:sp=occurrence_3");
      quick.push("lrs+11_5:1_add=large:afr=on:afp=1000:afq=1.0:amm=off:anc=none:bd=off:gs=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:urr=ec_only_192");
      quick.push("lrs+10_24_add=off:afp=100000:afq=1.2:amm=sco:anc=none:cond=on:fsr=off:gs=on:ile=on:nm=64:nwc=1:stl=30:sp=occurrence:tha=off:thf=on_45");
      quick.push("lrs+11_4:1_add=large:afr=on:afp=40000:afq=2.0:amm=off:anc=none:cond=on:gs=on:gsem=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sac=on:tha=off:urr=on:updr=off_288");
      quick.push("lrs+1003_3:1_av=off:bsr=on:cond=fast:fde=unused:inw=on:ile=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sos=all:sp=occurrence:tha=off:updr=off:uhcvi=on_125");
      quick.push("lrs+1011_7_av=off:cond=on:gs=on:ile=on:nm=64:nwc=3:stl=30:updr=off_166");
      quick.push("lrs+10_3:1_afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:ile=on:irw=on:lma=on:lwlo=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity_93");
      quick.push("ott+1004_8:1_afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:fde=unused:ile=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sp=reverse_arity:tha=off:updr=off_146");
      return;
      
    case SMT_AUFLIA:
      quick.push("dis+10_4_add=off:afp=4000:afq=1.1:amm=sco:anc=none:fsr=off:gs=on:ile=on:lma=on:nm=64:nwc=1:sas=z3:sac=on:tha=off:urr=on:updr=off_2");
      return;
      
    case SMT_NRA:
      quick.push("dis+11_4_add=off:afp=1000:afq=2.0:amm=sco:anc=none:fsr=off:gs=on:gsem=off:ile=on:nm=64:nwc=1.7:sas=z3:urr=on_1");
      quick.push("dis+11_5_av=off:cond=on:fsr=off:ile=on:lwlo=on:nm=64:nwc=3:sp=reverse_arity:updr=off_4");
      quick.push("dis+11_3_afr=on:afp=40000:afq=2.0:anc=none:fsr=off:gs=on:lma=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:sos=all:sac=on:sp=occurrence:urr=on_2");
      quick.push("dis+1011_4:1_anc=none:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:ile=on:lma=on:lwlo=on:nm=64:nwc=1:sas=z3:sac=on:sp=occurrence_9");
      quick.push("lrs+1011_3_add=large:afp=1000:afq=1.1:anc=none:cond=on:fsr=off:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:stl=30:sos=all:sac=on_182");
      return;

    case SMT_UF:
      quick.push("fmb+10_1_av=off:fmbes=contour:fmbsr=1.3:ile=on:nm=2:newcnf=on:updr=off_45");
      quick.push("ott+11_3_afr=on:afp=10000:afq=1.4:amm=off:anc=none:bsr=on:cond=on:er=known:ile=on:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1:sac=on_1");
      quick.push("ott+1011_8:1_add=off:afr=on:afp=40000:afq=1.2:amm=off:anc=none:bd=off:fsr=off:ile=on:nm=64:newcnf=on:nwc=1.1:sas=z3:sp=reverse_arity:updr=off_55");
      quick.push("lrs+1011_3:1_add=large:afr=on:afp=40000:afq=1.0:anc=none:cond=on:ile=on:irw=on:lma=on:lwlo=on:nm=64:nwc=1.1:sas=z3:stl=30:sac=on:updr=off_115");
      quick.push("ott+2_4:1_aac=none:add=off:afp=10000:afq=1.1:amm=off:anc=none:bs=on:gs=on:gsem=off:ile=on:irw=on:nm=64:newcnf=on:nwc=1:sas=z3:sp=reverse_arity_130");
      quick.push("dis+11_50_add=large:afp=10000:afq=1.2:anc=none:fsr=off:gs=on:gsem=off:ile=on:irw=on:nm=64:newcnf=on:nwc=1:sac=on_4");
      quick.push("ott+11_8:1_acc=model:add=off:afr=on:afp=100000:afq=2.0:amm=off:anc=none:ccuc=first:cond=on:fde=none:gs=on:gsaa=from_current:gsem=on:ile=on:lwlo=on:nm=2:nwc=1:sos=all:urr=on_27");
      quick.push("dis+2_4_add=large:afr=on:afp=40000:afq=2.0:anc=none:bd=off:ile=on:irw=on:nm=16:nwc=1:nicw=on:sas=z3:sos=on:sp=reverse_arity:updr=off_45");
      quick.push("ott+11_1_add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:cond=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sp=occurrence:urr=ec_only_149");
      quick.push("ott+2_6_add=large:afr=on:afp=4000:afq=2.0:amm=sco:anc=all:bs=on:bce=on:cond=fast:fde=none:gs=on:gsem=off:ile=on:nm=64:newcnf=on:nwc=1:sac=on:urr=on:updr=off_4");
      quick.push("lrs+10_2:1_av=off:cond=on:fde=none:gs=on:gsem=off:ile=on:irw=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on_167");
      quick.push("lrs+1011_1_av=off:bd=off:ile=on:irw=on:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1:stl=30:sp=occurrence_108");
      quick.push("dis+1002_2_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:ep=RS:ile=on:nm=64:nwc=1:sac=on:sp=reverse_arity:uhcvi=on_22");
      quick.push("lrs+10_3:1_afr=on:afp=100000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:ile=on:nm=64:newcnf=on:nwc=1:stl=30:sac=on:urr=on:uhcvi=on_212");
      quick.push("dis+1011_8:1_add=off:afp=10000:afq=1.0:amm=off:anc=none:bd=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sac=on:sp=reverse_arity:updr=off_91");
      quick.push("lrs+1010_1_add=off:afp=1000:afq=1.0:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:ile=on:lwlo=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sp=occurrence_192");
      quick.push("lrs+10_2_av=off:bd=off:er=known:fsr=off:lwlo=on:nm=64:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:urr=ec_only_27");
      quick.push("dis+1004_4:1_av=off:br=off:cond=on:ep=RST:fsr=off:ile=on:lma=on:nm=2:newcnf=on:nwc=1.1:sp=occurrence:urr=on_71");
      quick.push("dis+10_1_add=off:afp=4000:afq=1.4:amm=sco:anc=none:cond=on:ep=RSTC:gs=on:gsem=on:ile=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:sos=on:sac=on:sp=reverse_arity_25");
      quick.push("dis+4_16_acc=model:add=large:afr=on:afp=40000:afq=2.0:amm=off:anc=none:bs=on:ccuc=small_ones:fsr=off:ile=on:nm=4:newcnf=on:nwc=1:nicw=on:sp=reverse_arity_13");
      quick.push("dis+11_5_add=large:afr=on:afp=1000:afq=1.0:anc=none:bsr=on:fsr=off:nm=64:newcnf=on:nwc=1:updr=off_3");
      quick.push("ott+1003_5_av=off:bd=off:bs=on:er=known:fde=none:gs=on:gsem=off:ile=on:nwc=2.5:sos=all:sp=occurrence:urr=on_237");
      quick.push("lrs+11_2_add=large:afr=on:amm=sco:anc=none:bsr=on:gs=on:gsem=off:irw=on:lma=on:nm=16:newcnf=on:nwc=1:stl=30:sac=on:sp=occurrence:urr=on:updr=off_270");
      quick.push("dis+1011_8_av=off:bd=off:bs=unit_only:bsr=on:cond=on:irw=on:nm=64:newcnf=on:nwc=1_35");
      quick.push("dis+10_3:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:bd=off:cond=on:ile=on:nm=2:nwc=2.5:sas=z3:sac=on:sp=occurrence_91");
      quick.push("lrs+10_128_add=off:afr=on:amm=sco:anc=none:bsr=on:cond=on:ile=on:irw=on:nm=2:nwc=2:nicw=on:sas=z3:stl=30:updr=off_96");
      quick.push("lrs+11_2_av=off:br=off:ep=R:ile=on:lma=on:nm=64:nwc=1:stl=30:urr=on_41");
      quick.push("lrs+11_5_av=off:cond=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:updr=off_22");
      quick.push("fmb+10_1_av=off:bce=on:fmbes=contour:fmbsr=2.0:ile=on:nm=2_595");
      quick.push("lrs+11_3:1_av=off:bsr=on:cond=on:fsr=off:ile=on:irw=on:lma=on:nm=64:nwc=1.1:stl=30:sp=reverse_arity:updr=off_22");
      quick.push("dis+11_24_acc=on:afr=on:amm=sco:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:newcnf=on:nwc=1:updr=off_8");
      quick.push("lrs+11_4:1_av=off:bd=off:bs=unit_only:cond=on:fsr=off:fde=none:ile=on:irw=on:lwlo=on:nm=4:nwc=1.1:stl=30:sp=reverse_arity_95");
      quick.push("dis+2_3_acc=on:add=off:afr=on:afp=100000:afq=1.2:amm=off:anc=none:bs=unit_only:br=off:ccuc=first:cond=on:er=filter:ile=on:nm=6:nwc=1:urr=on_53");
      quick.push("lrs+11_2:1_av=off:cond=on:er=known:gsp=input_only:ile=on:lma=on:nm=64:nwc=1:stl=30:sos=theory:sp=reverse_arity:urr=on:updr=off_7");
      quick.push("lrs+1_32_av=off:bd=off:bs=unit_only:er=known:gsp=input_only:gs=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=on:sp=reverse_arity:urr=ec_only_88");
      quick.push("dis+10_1_afp=4000:afq=2.0:amm=sco:anc=none:bd=off:cond=on:er=known:lcm=reverse:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:sos=on:sac=on:sp=occurrence:urr=ec_only_39");
      quick.push("dis+11_50_aac=none:acc=model:add=large:afr=on:afp=4000:afq=2.0:anc=none:ccuc=first:er=known:fde=unused:gsp=input_only:gs=on:gsaa=full_model:ile=on:irw=on:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_5");
      quick.push("dis+1011_8:1_av=off:ile=on:lma=on:nm=32:newcnf=on:nwc=1:sp=occurrence_161");
      quick.push("lrs+1010_8:1_add=off:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:gsp=input_only:gs=on:gsem=on:ile=on:irw=on:lma=on:nm=64:nwc=2:stl=30:updr=off_128");
      quick.push("dis+1002_5_av=off:cond=on:fsr=off:ile=on:nm=64:newcnf=on:nwc=1.1:sp=reverse_arity_20");
      quick.push("ott+4_4_av=off:bd=off:er=filter:ile=on:irw=on:lma=on:nm=64:nwc=1:sos=on:sp=reverse_arity:updr=off_140");
      quick.push("lrs+10_3_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:cond=on:er=known:ile=on:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sos=all:sac=on:updr=off_118");
      quick.push("dis+1011_4:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bsr=on:fsr=off:ile=on:nm=64:nwc=5:sas=z3:sp=reverse_arity:urr=ec_only:updr=off_255");
      quick.push("dis+1011_2_acc=model:add=large:afp=40000:afq=1.0:anc=none:bd=off:bsr=on:ccuc=first:cond=on:er=known:fsr=off:ile=on:lma=on:nm=64:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence_132");
      quick.push("fmb+10_1_av=off:bce=on:fmbsr=1.3:fde=none:nm=64:newcnf=on_761");
      quick.push("lrs+1011_3:2_av=off:bd=off:bsr=on:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=64:nwc=1.5:sas=z3:stl=30:sp=reverse_arity_222");
      quick.push("dis+2_4_acc=on:add=large:afp=100000:afq=1.1:amm=sco:anc=none:ccuc=first:cond=on:fsr=off:gs=on:ile=on:lcm=reverse:nm=64:newcnf=on:nwc=1.1:nicw=on_280");
      quick.push("lrs-1_2:3_aac=none:add=off:afr=on:afp=40000:afq=2.0:amm=off:cond=on:fsr=off:fde=none:gs=on:gsaa=from_current:ile=on:irw=on:lwlo=on:nm=2:nwc=1.2:stl=60:sos=theory:sp=occurrence_120");
      quick.push("dis+1010_5:1_av=off:cond=on:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=0:newcnf=on:nwc=1:urr=on:updr=off_74");
      quick.push("lrs+10_3:2_av=off:bd=off:bsr=on:cond=on:fsr=off:gs=on:gsem=off:nm=64:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:urr=on_163");
      quick.push("lrs+11_5:1_add=off:afr=on:afp=4000:afq=1.1:anc=none:bsr=on:fsr=off:ile=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=reverse_arity:urr=on:updr=off_172");
      quick.push("ott+10_2:1_av=off:bce=on:cond=fast:fde=none:irw=on:nm=32:newcnf=on:nwc=1:sos=theory:updr=off_207");
      quick.push("ott+1_5:1_afp=4000:afq=1.1:anc=none:bd=off:cond=on:ile=on:nm=64:nwc=1:sas=z3:sac=on:sp=reverse_arity:urr=on:updr=off_154");
      quick.push("lrs+1002_3_av=off:bs=unit_only:bsr=on:ile=on:nm=64:nwc=1:stl=30:sos=theory:sp=reverse_arity_216");
      quick.push("dis+4_6_av=off:bd=off:bs=on:ile=on:irw=on:lma=on:nm=64:nwc=1_229");
      quick.push("lrs+1002_3_acc=on:amm=sco:anc=none:ccuc=small_ones:gs=on:gsem=on:ile=on:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:stl=30:urr=on_239");
      quick.push("dis+1_4_av=off:bd=off:fsr=off:nm=64:newcnf=on:nwc=1:sp=reverse_arity_243");
      quick.push("ott-10_4_av=off:bd=preordered:fsr=off:fde=none:ile=on:irw=on:nm=2:newcnf=on:nwc=1:updr=off:uhcvi=on_244");
      quick.push("fmb+10_1_av=off:bce=on:fmbes=contour:fmbsr=1.4:fde=unused:updr=off_808");
      quick.push("ott+4_4_av=off:cond=on:gs=on:gsem=on:nm=2:nwc=1.7:updr=off_40");
      quick.push("lrs+11_3:2_av=off:cond=on:gs=on:gsem=off:ile=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:st=5.0:updr=off_78");
      return;
      
    case SMT_AUFLIRA:
      quick.push("lrs+1010_4_av=off:bd=off:bs=unit_only:bsr=on:gs=on:inw=on:ile=on:lma=on:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_6");
      quick.push("dis-11_7_add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:cond=on:fsr=off:ile=on:irw=on:nm=6:nwc=10:sas=z3:sp=occurrence:updr=off_0");
      quick.push("dis+1010_8_add=off:afp=1000:afq=1.0:anc=none:bd=off:fsr=off:ile=on:irw=on:nm=64:nwc=1.7:sas=z3:sac=on:tha=off:thf=on:updr=off_0");
      quick.push("dis+1011_4_afr=on:afp=4000:afq=1.4:anc=none:fsr=off:gs=on:gsem=on:ile=on:lma=on:nm=64:nwc=1:sas=z3:sac=on:tha=off:updr=off_8");
      quick.push("ott+11_3:2_aac=none:add=large:afr=on:afp=1000:afq=1.4:amm=sco:anc=none:bs=on:bsr=on:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=predicate:lma=on:nm=16:nwc=1.5:nicw=on:sas=z3:sac=on:sp=reverse_arity:tha=off:thi=all:urr=on:updr=off_0");
      quick.push("dis+11_4:1_aac=none:add=off:afr=on:afp=100000:afq=2.0:amm=off:anc=all_dependent:bd=preordered:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=4:newcnf=on:nwc=2.5:sas=z3:sos=on:sac=on:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_0");
      quick.push("dis+1002_5:1_aac=none:afr=on:afp=4000:afq=1.1:amm=sco:anc=none:bsr=on:br=off:cond=on:fsr=off:gsp=input_only:gs=on:gsem=on:inw=on:ile=on:irw=on:lma=on:nm=32:newcnf=on:nwc=1.1:sas=z3:sp=reverse_arity:tha=off:urr=on_0");
      quick.push("dis+1011_32_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=sco:bs=on:bsr=on:br=off:fde=unused:gs=on:gsaa=full_model:ile=on:lcm=predicate:nm=6:newcnf=on:nwc=1.5:sas=z3:sos=all:sac=on:tha=off:thi=all:uwa=one_side_constant:urr=on_0");
      quick.push("ott+1002_2_aac=none:add=large:afr=on:afp=10000:afq=2.0:anc=none:bs=unit_only:br=off:bce=on:cond=fast:fsr=off:gsp=input_only:irw=on:nm=32:newcnf=on:nwc=1.2:sas=z3:sos=all:sac=on:sp=occurrence:tha=off:urr=on:updr=off:uhcvi=on_0");
      quick.push("lrs+1010_2_anc=none:fsr=off:gs=on:irw=on:newcnf=on:nwc=1:sas=z3:stl=30:sos=on:sp=occurrence:updr=off_4");
      quick.push("dis+1003_12_add=large:afr=on:afp=4000:afq=1.4:anc=none:bd=off:bs=unit_only:bsr=on:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:ile=on:irw=on:lma=on:nm=32:nwc=1.3:sas=z3:sac=on:sp=occurrence:tha=off:thi=overlap:urr=on_0");
      quick.push("lrs+1003_4:1_aac=none:afr=on:afp=1000:afq=1.1:amm=off:bd=off:bce=on:cond=on:fde=unused:gs=on:gsem=on:ile=on:lwlo=on:nm=64:nwc=1:sas=z3:stl=60:sos=all:sac=on:tha=off:urr=on:updr=off_0");
      quick.push("dis+1002_2:1_afr=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bsr=on:cond=on:fsr=off:gs=on:ile=on:irw=on:lma=on:nm=4:nwc=1:sas=z3:sos=all:sac=on:sp=occurrence:tha=off:urr=on:updr=off:uhcvi=on_0");
      quick.push("dis+11_6_add=large:afr=on:afp=1000:afq=1.0:amm=sco:anc=all_dependent:bs=on:fsr=off:fde=unused:gsp=input_only:gs=on:gsaa=from_current:gsem=on:ile=on:lma=on:lwlo=on:nm=4:nwc=3:sas=z3:sos=on:sac=on:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_0");
      quick.push("lrs-1_4:1_add=large:afr=on:afp=4000:afq=1.2:anc=none:gs=on:gsem=on:ile=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:updr=off_0");
      quick.push("dis+1010_64_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:bce=on:fde=unused:gsp=input_only:gs=on:gsaa=full_model:gsem=off:ile=on:irw=on:lma=on:nm=6:nwc=1.1:nicw=on:sas=z3:sos=all:sac=on:tha=off:urr=on:uhcvi=on_0");
      quick.push("dis+1002_1_aac=none:add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=all:bs=on:bsr=on:cond=on:fsr=off:fde=unused:gsp=input_only:gs=on:gsem=on:irw=on:nm=4:nwc=4:nicw=on:sas=z3:sos=on:sac=on:tha=off:uwa=interpreted_only:urr=on:uhcvi=on_0");
      quick.push("dis+4_14_afp=10000:afq=1.2:amm=off:bd=off:cond=on:gsp=input_only:irw=on:lma=on:nm=4:nwc=4:nicw=on:sas=z3:sac=on:sp=occurrence:tha=off:urr=on:updr=off_0");
      quick.push("dis+1003_2:3_afp=4000:afq=2.0:amm=off:anc=all_dependent:bs=on:bsr=on:br=off:cond=on:fde=unused:gs=on:gsem=off:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1.5:sas=z3:sac=on:sp=occurrence:tha=off:urr=on:updr=off:uhcvi=on_0");
      quick.push("dis+2_3_add=off:afp=40000:afq=1.1:anc=none:cond=on:gs=on:inw=on:ile=on:lcm=reverse:nm=64:newcnf=on:nwc=1:sas=z3:sp=reverse_arity:tha=off:urr=on:updr=off_43");
      quick.push("lrs+1010_20_add=large:afr=on:afp=4000:afq=1.4:amm=sco:anc=none:bd=preordered:bs=unit_only:fsr=off:fde=unused:gs=on:ile=on:lcm=reverse:nm=2:nwc=4:sas=z3:stl=120:sac=on:sp=occurrence:tha=off:urr=on:updr=off:uhcvi=on_791");
      quick.push("dis+1011_3_aac=none:afp=1000:afq=1.2:anc=all:fde=none:gs=on:gsem=on:inw=on:ile=on:lcm=predicate:lma=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:tha=off:urr=on_344");
      quick.push("dis+1002_5:4_afr=on:afp=1000:afq=1.2:anc=none:cond=on:ile=on:irw=on:lwlo=on:nm=64:nwc=1:sas=z3:sac=on:sp=reverse_arity:tha=off:updr=off_33");
      return;

    case SMT_UFLIA:
      return;

    case SMT_QF_ABV:
    case SMT_QF_ALIA:
    case SMT_QF_ANIA:
    case SMT_QF_AUFBV:
    case SMT_QF_AUFLIA:
    case SMT_QF_AUFNIA:
    case SMT_QF_AX:
    case SMT_QF_BV:
    case SMT_QF_IDL:
    case SMT_QF_LIA:
    case SMT_QF_LIRA:
    case SMT_QF_LRA:
    case SMT_QF_NIA:
    case SMT_QF_NIRA:
    case SMT_QF_NRA:
    case SMT_QF_RDL:
    case SMT_QF_UF:
    case SMT_QF_UFBV:
    case SMT_QF_UFIDL:
    case SMT_QF_UFLIA:
    case SMT_QF_UFLRA:
    case SMT_QF_UFNIA:
    case SMT_QF_UFNRA:
      throw UserErrorException("Kein Kinderspiel, Bruder, use Z3 for quantifier-free problems!");

    case SMT_ALL:
    case SMT_BV:
    case SMT_UFBV:
      return;

    case SMT_UNDEFINED:
      throw UserErrorException("This version cannot be used with this logic!");
    }

} // getSchedule


#endif //!COMPILER_MSVC
