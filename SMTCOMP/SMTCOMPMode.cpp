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
 * This function solves a single problem. It makes the following steps:
 * <ol><li>find the main and the fallback schedules depending on the problem
 *          properties</li>
 *     <li>run the main schedule using runSchedule()</li>
 *     <li>if the proof is not found, checks if all the remaining time
 *         was used: if not, it runs the fallback strategy using
 *         runSchedule() with the updated time limit</li></ol>
 * Once the problem is proved, the runSchedule() function does not return
 * and the process terminates.
 *
 * If a slice contains sine_selection value different from off, theory axioms
 * will be selected using SInE from the common axioms included in the batch file
 * (all problem axioms, including the included ones, will be used as a base
 * for this selection).
 *
 * If the sine_selection is off, all the common axioms will be just added to the
 * problem axioms. All this is done in the @b runSlice(Options&) function.
 * @param terminationTime the time in milliseconds since the prover starts when
 *        the strategy should terminate
 * @param timeLimit in milliseconds
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
 * This function solves a single problem. It parses the problem, spawns a
 * writer process for output and creates a pipe to communicate with it.
 * Then it calls performStrategy(terminationTime) that performs the
 * actual proof search.
 */
bool SMTCOMPMode::searchForProof()
{
  CALL("SMTCOMPMode::searchForProof");

  env.timer->makeChildrenIncluded();
  TimeCounter::reinitialize();

  prb = UIHelper::getInputProblem(*env.options); 

  Shell::Property* property = prb->getProperty();

  if (property->atoms()<=1000000) {
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
    time++;
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
    case SMT_ALIA:
      quick.push("lrs+4_8:1_er=filter:gs=on:gsem=on:lma=on:nm=16:nwc=3:nicw=on:sas=z3:stl=30:ssac=none:sfr=on:ssfp=10000:ssfq=1.0:ssnc=none:urr=on:updr=off_15");
      quick.push("lrs-11_32_bd=off:fsr=off:gsp=input_only:gs=on:irw=on:inst=on:lma=on:nm=64:nwc=1:nicw=on:sas=z3:stl=30:ssfp=10000:ssfq=1.4:smm=off:ssnc=none:tha=off:urr=on_47");
      quick.push("lrs-11_2_bs=unit_only:bsr=on:gs=on:gsem=off:irw=on:nm=32:nwc=1:sas=z3:stl=30:sos=theory:sac=on:sfr=on:ssfp=1000:ssfq=1.0:smm=off:ssnc=none:urr=on_36");
      quick.push("dis-11_10_bs=on:bsr=on:fsr=off:gs=on:irw=on:inst=on:lcm=reverse:lma=on:nm=64:nwc=1.7:sas=z3:sdd=large:sfr=on:ssfp=1000:ssfq=2.0:smm=sco:ssnc=none:sp=reverse_arity:tha=off:thf=on:updr=off_37");
      quick.push("lrs+1010_10_cond=on:fsr=off:gs=on:gsem=off:inst=on:lcm=reverse:lma=on:nm=64:nwc=1:nicw=on:sas=z3:stl=30:sdd=off:sfr=on:ssfp=40000:ssfq=1.4:smm=off:ssnc=none:tha=off:thf=on:urr=on_141");
      quick.push("lrs+1011_8:1_bd=off:bsr=on:gs=on:inst=on:nwc=2.5:nicw=on:sas=z3:stl=120:sos=theory:sac=on:sdd=large:sfr=on:ssfp=1000:ssfq=2.0:smm=sco:ssnc=none_81");
      break;
    case SMT_AUFLIA:
      quick.push("dis+1_3_fsr=off:gs=on:nm=64:nwc=1:sas=z3:sac=on:sfr=on:ssfp=100000:ssfq=1.1:smm=sco:ssnc=none:sp=reverse_arity:tha=off:updr=off_2");
      quick.push("lrs+4_3:1_bs=on:fsr=off:gs=on:gsem=off:ile=on:inst=on:lma=on:nm=64:nwc=2.5:nicw=on:sas=z3:stl=30:sos=theory:sac=on:sdd=large:ssfp=10000:ssfq=1.2:smm=off:ssnc=none:sp=reverse_arity:urr=ec_only:updr=off_36");
      break;
    case SMT_AUFLIRA:
      quick.push("dis+1010_7_fsr=off:inst=on:nm=4:nwc=2:sas=z3:sac=on:ssac=none:sdd=large:ssfp=10000:ssfq=1.4:smm=off:sp=occurrence:tha=off:updr=off_44");
      quick.push("dis-11_12_cond=on:gsp=input_only:irw=on:lwlo=on:nm=32:nwc=1:sas=z3:sos=all:sac=on:sfr=on:ssfp=4000:ssfq=1.0:ssnc=none:tha=off_38");
      quick.push("dis+1011_5_fsr=off:gs=on:ile=on:irw=on:nm=64:nwc=1:sas=z3:ssfp=10000:ssfq=1.4:smm=sco:ssnc=none:sp=reverse_arity:tha=off_5");
      quick.push("lrs+1011_5_bd=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sdd=large:sfr=on:ssfp=100000:ssfq=1.1:smm=off:ssnc=none:sp=reverse_arity:urr=on:updr=off_2");
      quick.push("lrs+11_3:2_cond=on:gs=on:gsem=on:inw=on:ile=on:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sdd=large:sfr=on:ssfp=100000:ssfq=1.0:smm=sco:ssnc=none:sp=reverse_arity:urr=on:updr=off_4");
      quick.push("lrs+11_28_bd=off:bsr=on:fsr=off:gs=on:gsem=off:inw=on:ile=on:lma=on:nwc=1:sas=z3:stl=120:sos=on:sdd=off:sfr=on:ssfp=40000:ssfq=1.2:smm=off:sp=reverse_arity:tha=off_1198");
      quick.push("lrs+1011_3:2_bsr=on:cond=fast:gs=on:gsem=off:inw=on:inst=on:nm=64:nwc=2:stl=30:sac=on:ssac=none:ssnc=none:sp=occurrence_75");
      break;
    case SMT_AUFNIRA:
      quick.push("lrs+11_2:3_bd=off:cond=on:gs=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sac=on:sdd=large:ssfp=40000:ssfq=2.0:smm=sco:ssnc=none:sp=reverse_arity_1");
      quick.push("lrs+11_4_fsr=off:gs=on:ile=on:nm=64:nwc=1:sas=z3:stl=30:sac=on:sdd=off:sfr=on:ssfp=1000:ssfq=1.1:smm=sco:ssnc=none:tha=off_2");
      quick.push("lrs+1002_4_bd=off:fsr=off:gs=on:irw=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sos=all:sac=on:sdd=large:sfr=on:ssfp=4000:ssfq=1.4:ssnc=none:sp=occurrence:tha=off:updr=off_1");
      quick.push("lrs+1011_3:2_bsr=on:cond=fast:gs=on:gsem=off:inw=on:inst=on:nm=64:nwc=2:stl=30:sac=on:ssac=none:ssnc=none:sp=occurrence_15");
      quick.push("dis+10_24_fsr=off:ile=on:lma=on:nm=64:nwc=2:sas=z3:sdd=large:sfr=on:ssfp=1000:ssfq=1.1:smm=sco:ssnc=none:thf=on_2");
      quick.push("dis+10_5_gs=on:gsem=on:inw=on:ile=on:inst=on:lwlo=on:nm=64:nwc=1:nicw=on:sas=z3:sac=on:ssfp=100000:ssfq=1.0:smm=off:ssnc=none:sp=reverse_arity:tha=off:thf=on_29");
      quick.push("dis-10_8:1_cond=on:ile=on:irw=on:nm=64:nwc=4:sas=z3:sos=theory:ssnc=none:updr=off_74");
      quick.push("lrs+11_3:2_bd=off:cond=on:gs=on:gsem=off:ile=on:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sos=all:sac=on:ssfp=1000:ssfq=2.0:smm=sco:ssnc=none:sp=occurrence:urr=ec_only:updr=off_300");
      quick.push("ott+10_8:1_cond=on:ile=on:irw=on:nm=64:newcnf=on:nwc=1:spl=off:sp=reverse_arity:tha=off:urr=on_140");
      quick.push("lrs+10_4_cond=on:fsr=off:lwlo=on:nm=64:nwc=1:stl=30:spl=off:sp=reverse_arity:tha=off:updr=off_91");
      quick.push("lrs-11_1_cond=on:gsp=input_only:gs=on:gsem=off:inw=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sdd=large:sfr=on:ssfp=10000:ssfq=1.1:smm=off:ssnc=none:tha=off:thf=on:updr=off_111");
      quick.push("lrs-11_3_cond=on:inst=on:lma=on:nm=32:nwc=1:stl=30:sscc=model:sdd=off:ssfp=40000:ssfq=1.4:smm=off:ssnc=none:sp=occurrence:tha=off:updr=off_142");
      break;
    case SMT_LIA:
      quick.push("dis+11_4_fsr=off:gs=on:gsem=off:ile=on:irw=on:nm=64:newcnf=on:nwc=1:sas=z3:sos=all:sdd=large:sfr=on:ssfp=40000:ssfq=1.2:ssnc=none:sp=occurrence:updr=off_10");
      quick.push("dis+11_5_gs=on:lma=on:nm=64:nwc=1:sas=z3:sac=on:ssfp=1000:ssfq=1.0:smm=off:ssnc=none:updr=off_2");
      quick.push("dis+1011_4_cond=on:irw=on:lma=on:nm=64:nwc=1:sos=all:spl=off:sp=occurrence_32");
      quick.push("dis-1_128_bs=unit_only:ccuc=first:cond=on:gsp=input_only:ile=on:irw=on:inst=on:lma=on:newcnf=on:nwc=1:sscc=model:sfr=on:ssfp=40000:ssfq=2.0:smm=off:sp=reverse_arity:tha=off:urr=ec_only_90");
      quick.push("dis+10_5_cond=on:inw=on:ile=on:inst=on:lma=on:nm=16:newcnf=on:nwc=1:sac=on:sdd=large:sfr=on:ssfp=1000:ssfq=2.0:smm=off:ssnc=none:sp=occurrence:tha=off:updr=off_75");
      quick.push("lrs-1_64_bs=unit_only:bsr=on:fsr=off:gs=on:gsem=off:inw=on:ile=on:inst=on:lcm=predicate:nm=6:newcnf=on:nwc=1:nicw=on:stl=30:sac=on:ssac=none:sdd=off:sfr=on:ssfp=100000:ssfq=1.2:smm=off:ssnc=none:tha=off:uhcvi=on_153");
      break;
    case SMT_LRA:
      quick.push("dis+11_3:2_bd=off:gsp=input_only:gs=on:gsem=on:ile=on:lcm=reverse:nm=2:newcnf=on:nwc=3:nicw=on:sas=z3:ssfp=4000:ssfq=2.0:ssnc=none:sp=occurrence_23");
      quick.push("dis+1_3:2_bd=off:lma=on:nm=32:nwc=2.5:sas=z3:sos=theory:sdd=off:sfr=on:ssfp=1000:ssfq=1.0:smm=off:ssnc=none:sp=reverse_arity_24");
      quick.push("dis-1_4_cond=on:gs=on:gsem=off:irw=on:lcm=reverse:lma=on:nm=2:nwc=1:sas=z3:sos=all:ssfp=10000:ssfq=1.4:ssnc=none:sp=reverse_arity:urr=on_12");
      quick.push("lrs+10_3:1_bd=off:fsr=off:gs=on:gsem=off:inst=on:nm=32:nwc=1.1:sas=z3:stl=30:sdd=off:sfr=on:ssfp=100000:ssfq=1.0:smm=off:ssnc=none:sp=reverse_arity:updr=off_27");
      quick.push("dis+1011_3_cond=on:gs=on:lma=on:lwlo=on:nm=64:nwc=1:sas=z3:sos=on:sfr=on:ssfp=40000:ssfq=1.1:ssnc=none:sp=occurrence:thf=on_30");
      quick.push("lrs+1002_3:2_fsr=off:gs=on:gsem=on:ile=on:lwlo=on:nm=64:nwc=3:stl=30:spl=off:sp=reverse_arity:updr=off_42");
      quick.push("dis+11_3_cond=on:gs=on:inst=on:lcm=reverse:nm=16:nwc=1:sas=z3:sos=on:sdd=large:sfr=on:ssfp=100000:ssfq=2.0:smm=sco:ssnc=none:updr=off_122");
      quick.push("lrs+1010_5:1_bs=on:cond=on:gs=on:gsem=on:irw=on:inst=on:lma=on:nm=0:nwc=1:sas=z3:stl=30:sos=all:sdd=large:sfr=on:ssfp=100000:ssfq=1.2:smm=sco:ssnc=none:updr=off_256");
      break;
    case SMT_NIA:
      quick.push("lrs+1011_3:2_bsr=on:cond=fast:gs=on:gsem=off:inw=on:inst=on:nm=64:nwc=2:stl=30:sac=on:ssac=none:ssnc=none:sp=occurrence_295");
      break;
    case SMT_NRA:      
      quick.push("dis+1011_5_cond=on:gs=on:gsem=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.7:sas=z3:sdd=off:ssfp=1000:ssfq=1.2:smm=off:ssnc=none_3");
      quick.push("lrs+1011_3:2_bsr=on:cond=fast:gs=on:gsem=off:inw=on:inst=on:nm=64:nwc=2:stl=30:sac=on:ssac=none:ssnc=none:sp=occurrence_35");
      quick.push("lrs+1011_2:3_fsr=off:lma=on:nm=64:nwc=3:sas=z3:stl=30:sac=on:sdd=large:ssfp=4000:ssfq=1.2:smm=off:ssnc=none:sp=occurrence_12");
      quick.push("lrs+4_3_cond=on:fsr=off:gs=on:gsem=on:inst=on:lma=on:nm=64:nwc=1:nicw=on:sas=z3:stl=30:sfr=on:ssfp=4000:ssfq=1.1:ssnc=none:sp=occurrence:updr=off_75");
      quick.push("lrs+1011_4_bd=off:bsr=on:gs=on:irw=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:stl=30:sos=on:sac=on:sdd=off:sfr=on:ssfp=10000:ssfq=1.4:smm=sco:ssnc=none_243");
      quick.push("dis+4_4_cond=on:lma=on:nm=64:nwc=1:sas=z3:sac=on:ssfp=1000:ssfq=1.0:smm=off:ssnc=none:sp=occurrence_7");
      break;
    case SMT_UF:
      quick.push("lrs+11_1_bd=off:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sdd=off:sfr=on:ssfp=100000:ssfq=1.1:smm=off:ssnc=none:sp=reverse_arity:urr=on:updr=off_4");
      quick.push("lrs+11_2:1_bsr=on:ile=on:nm=64:newcnf=on:nwc=1:stl=30:spl=off:sp=reverse_arity_6");
      quick.push("fmb+10_1_fmbas=function:ile=on:nm=2:newcnf=on:spl=off_191");
      quick.push("dis+10_5:4_bd=off:cond=on:gsp=input_only:ile=on:nm=2:nwc=1:sdd=large:sfr=on:ssfp=100000:ssfq=1.2:smm=sco:ssnc=none_128");
      quick.push("lrs+1011_1_cond=on:ile=on:nwc=1.2:stl=30:sdd=off:sfr=on:ssfp=4000:ssfq=1.0:urr=ec_only:updr=off_63");
      quick.push("fmb+10_1_fmbas=expand:fmbes=smt:fmbsr=1.1:ile=on:nm=2:spl=off:updr=off_170");
      quick.push("lrs+1011_1_bs=on:cond=on:gs=on:gsem=off:ile=on:nm=6:newcnf=on:nwc=1:sas=z3:stl=30:sdd=off:ssfp=10000:ssfq=1.1:smm=off:ssnc=none:sp=reverse_arity:updr=off_5");
      quick.push("dis+1011_128_ile=on:nwc=1:sos=on:spl=off_10");
      quick.push("ott+1_4_cond=on:gsp=input_only:gs=on:gsem=off:ile=on:irw=on:nm=64:newcnf=on:nwc=1:sd=5:ss=axioms:st=1.5:spl=off:sp=reverse_arity:urr=on_113");
      quick.push("lrs+1011_3:1_bsr=on:fsr=off:ile=on:nm=64:nwc=1:stl=30:spl=off:sp=occurrence:updr=off_22");
      quick.push("dis+2_3_fsr=off:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:sdd=large:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=none:sp=reverse_arity_222");
      quick.push("lrs+1011_1_cond=on:gs=on:gsem=off:irw=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sdd=off:sfr=on:ssfp=100000:ssfq=1.1:smm=off:ssnc=none:updr=off_146");
      quick.push("dis+1_24_bs=on:fsr=off:gsp=input_only:gs=on:gsem=on:nm=4:newcnf=on:nwc=1:sas=z3:smm=off:ssnc=none_43");
      quick.push("fmb+10_1_fmbes=contour:fmbsr=1.6_1605");
      quick.push("lrs+2_5:1_bd=off:bsr=on:br=off:fsr=off:ile=on:nm=4:nwc=1:stl=30:spl=off:sp=reverse_arity:urr=on_169");
      quick.push("lrs+11_4:1_bsr=on:cond=on:fsr=off:ile=on:nm=64:nwc=1:stl=30:spl=off:urr=on:updr=off_43");
      quick.push("lrs+1011_3:2_bsr=on:cond=fast:gs=on:gsem=off:inw=on:inst=on:nm=64:nwc=2:stl=30:sac=on:ssac=none:ssnc=none:sp=occurrence_138");
      quick.push("dis+1002_6_cond=on:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=2:sdd=large:ssfp=10000:ssfq=1.2:smm=sco:ssnc=none:urr=on_119");
      quick.push("lrs+11_1_cond=on:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=6:nwc=1:sas=z3:stl=30:sd=4:ss=axioms:st=5.0:sos=all:spl=off:sp=occurrence:updr=off_90");
      quick.push("ott+11_2_bs=unit_only:fsr=off:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=1:sfr=on:ssfp=1000:ssfq=1.0:ssnc=none:updr=off_255");
      quick.push("ott+2_5:1_gsp=input_only:gs=on:ile=on:lma=on:nm=16:nwc=10:sdd=off:sfr=on:ssfp=4000:ssfq=1.1:smm=off:ssnc=none:sp=occurrence:updr=off_148");
      quick.push("dis+10_14_fsr=off:nm=64:newcnf=on:nwc=1.1:spl=off:urr=ec_only:updr=off_129");
      quick.push("dis+4_3:1_cond=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:sac=on:sdd=large:ssfp=40000:ssfq=1.2:smm=sco:ssnc=none:sp=reverse_arity:urr=on:updr=off_299");
      quick.push("lrs+11_5:1_cond=on:fsr=off:nm=4:nwc=1:sas=z3:stl=30:sos=on:sfr=on:ssfp=1000:ssfq=1.0:smm=off:ssnc=none:sp=reverse_arity:urr=on_23");
      quick.push("ins+10_1_ile=on:irw=on:igbrr=0.7:igpr=on:igrr=32/1:igrpq=2.0:igs=1002:igwr=on:lcm=reverse:nm=16:nwc=2:spl=off:dm=on_46");
      quick.push("ott+10_8_bsr=on:fsr=off:lcm=reverse:lma=on:nm=32:nwc=1.3:nicw=on:sas=z3:sos=on:sac=on:sfr=on:ssfp=10000:ssfq=2.0:smm=off:sp=occurrence:urr=on_122");
      quick.push("dis+4_1_ccuc=first:cond=on:fsr=off:gs=on:ile=on:irw=on:nm=64:nwc=2.5:sac=on:sscc=model:sfr=on:ssfp=100000:ssfq=1.2:smm=off:ssnc=none:urr=ec_only_87");
      quick.push("ins+11_8:1_cond=on:ile=on:igbrr=0.6:igrr=8/1:igrp=4000:igs=1004:igwr=on:lma=on:nm=2:newcnf=on:nwc=4:spl=off:updr=off:dm=on_276");
      quick.push("lrs+1002_24_bd=off:bs=unit_only:cond=on:fsr=off:ile=on:irw=on:lma=on:nm=2:nwc=2:stl=30:sscc=on:sdd=off:ssfp=1000:ssfq=1.1:ssnc=none_106");
      quick.push("ott+1_14_bd=off:cond=on:er=filter:lma=on:nm=64:newcnf=on:nwc=1:spl=off:sp=reverse_arity_171");
      quick.push("lrs+11_2:3_gs=on:lma=on:nm=6:nwc=3:sas=z3:stl=30:sdd=large:ssfp=100000:ssfq=1.0:smm=off:ssnc=none:sp=occurrence_134");
      quick.push("dis+1011_5:1_cond=on:ile=on:irw=on:nm=6:nwc=1:sac=on:sdd=off:sfr=on:ssfp=40000:ssfq=2.0:smm=off:ssnc=none:sp=reverse_arity_254");
      quick.push("ott-10_2:1_bsr=on:ccuc=small_ones:cond=on:ile=on:irw=on:lcm=reverse:nwc=1:nicw=on:sos=on:sscc=model:ssfp=1000:ssfq=1.4:ssnc=none:sp=reverse_arity_261");
      quick.push("lrs+11_5_bd=off:gs=on:gsem=on:ile=on:irw=on:nm=64:nwc=1:stl=30:sos=on:sscc=on:sfr=on:ssfp=100000:ssfq=1.1:ssnc=none:sp=reverse_arity_272");
      quick.push("lrs+4_8_gs=on:ile=on:irw=on:nm=32:nwc=2.5:stl=30:spl=off:updr=off_130");
      quick.push("fmb+10_1_fmbas=expand:fmbsr=1.8:ile=on:nm=4:spl=off_190");
      quick.push("ins+11_4_bd=off:cond=on:ile=on:irw=on:igbrr=0.2:igpr=on:igrr=1/16:igrp=200:igrpq=1.1:igs=1003:igwr=on:nm=2:newcnf=on:nwc=1:spl=off:updr=off_369");
      quick.push("dis+10_128_er=known:fsr=off:gsp=input_only:nm=0:newcnf=on:nwc=4:ssac=none:sdd=large:sfr=on:ssfp=1000:ssfq=1.4:ssnc=none:sp=reverse_arity:updr=off_434");
      quick.push("ins+10_1_br=off:fsr=off:ile=on:irw=on:igbrr=1.0:igrr=1/32:igrp=1400:igrpq=1.2:igs=1010:igwr=on:lma=on:nm=4:nwc=1.1:sos=all:spl=off:sp=reverse_arity:urr=on:dm=on_73");
      break;
    case SMT_UFIDL:
      quick.push("dis+10_5_cond=on:gs=on:gsem=off:irw=on:lwlo=on:nm=64:nwc=1:sos=all:sdd=off:ssfp=40000:ssfq=1.4:smm=off:ssnc=none:sp=reverse_arity:urr=on:updr=off_3");
      quick.push("dis+1010_4_cond=on:lma=on:nm=64:nwc=1.2:sac=on:sdd=large:sfr=on:ssfp=4000:ssfq=1.1:smm=off:ssnc=none:sp=occurrence_3");
      quick.push("dis+1011_10_gs=on:gsem=off:nm=64:nwc=1:sos=all:spl=off:tha=off_15");
      quick.push("dis+1011_32_bs=on:inw=on:nm=64:nwc=1.5:sd=10:ss=axioms:st=3.0:spl=off:tha=off_21");
      break;

    case SMT_UFLIA:
    case SMT_UFLRA:
    case SMT_UFNIA:
      
    case SMT_BV:
    case SMT_UFBV:
      break;
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
    case SMT_UNDEFINED:
      throw UserErrorException("This version cannot be used with this logic!");
    }
    
    fallback.push("dis+11_7_300");
    fallback.push("ott+11_8:1_cond=fast:gs=on:gsem=off:igrpq=1.0:nwc=1:nicw=on:sd=2:ss=axioms:st=1.2:sos=all:sscc=on:sfr=on:ssfp=100000:ssfq=1.0:smm=sco:ssnc=none:urr=on_300");
    fallback.push("lrs+1011_4_cond=fast:gs=on:gsaa=from_current:gsem=off:gsssp=full:igrpq=1.0:nm=0:nwc=1:sas=minisat:sd=3:ss=axioms:st=2.0:sdd=off:sfr=on:ssfp=100000:ssfq=1.2:smm=off:ssnc=none:sp=reverse_arity_300");
    fallback.push("dis+11_4_bsr=unit_only:cond=fast:fde=none:lwlo=on:nm=0:nwc=1.2:spl=off:sp=occurrence_1200");
    fallback.push("lrs+1002_6_ccuc=first:cond=on:fsr=off:igrpq=1.0:nwc=4:nicw=on:sas=minisat:sscc=on:sfr=on:ssfp=40000:ssfq=1.0:smm=sco:ssnc=all_dependent:sp=reverse_arity:urr=ec_only_300");
    fallback.push("ott+1011_4:1_bd=off:bsr=unit_only:cond=fast:fsr=off:fde=none:inw=on:igrpq=1.0:nm=0:nwc=1.1:sas=minisat:sos=on:ssfp=10000:ssfq=1.2:ssnc=none:sp=occurrence_300");
    fallback.push("lrs+4_2:1_ep=R:fde=unused:gs=on:igrpq=1.0:nwc=1:sos=all:sac=on:ssac=none:sser=off:sfr=on:ssfp=10000:ssfq=1.2:ssnc=none:sp=occurrence:updr=off_300");
    fallback.push("lrs+1011_3_bsr=unit_only:cond=on:fsr=off:lwlo=on:nwc=1:sd=3:ss=axioms:st=3.0:spl=off_300");
    fallback.push("lrs+1010_1_bs=unit_only:cond=fast:gs=on:gsem=off:igrpq=1.0:nwc=1:sos=all:spl=off_300");
    fallback.push("dis+1010_3:1_cond=fast:fde=unused:gs=on:igrpq=1.0:nwc=1:sd=2:ss=axioms:sos=on:sdd=large:sser=off:sfr=on:ssfp=100000:ssfq=1.2:updr=off_300");
    fallback.push("lrs+11_5:4_br=off:cond=on:fde=none:gs=on:gsem=on:gsssp=full:igrpq=1.0:nwc=1:sas=minisat:sd=3:ss=axioms:st=3.0:sos=all:sac=on:sser=off:sfr=on:ssfp=1000:ssfq=1.4:ssnc=all:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("dis-3_10_bsr=unit_only:er=filter:fde=unused:igrpq=1.0:lcm=predicate:nm=64:nwc=1:spl=off:sp=occurrence:updr=off_300");
    fallback.push("ott+1010_40_bs=unit_only:cond=fast:nwc=1:sas=minisat:sdd=off:ssfp=10000:ssfq=2.0:smm=sco:ssnc=none:sp=reverse_arity:updr=off_600");
    fallback.push("ins+11_3_cond=fast:fde=none:igbrr=0.8:igrr=1/16:igrp=200:igrpq=1.05:igs=1003:igwr=on:nm=64:nwc=1:sas=minisat:sd=2:ss=axioms:st=3.0:sos=on:spl=off:updr=off_300");
    fallback.push("dis+11_1024_br=off:ep=RSTC:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=off:nwc=1:sac=on:ssfp=40000:ssfq=1.0:ssnc=none:sp=reverse_arity:urr=on_300");
    fallback.push("ins+11_32_br=off:ep=RSTC:inw=on:igbrr=0.9:igrr=1/32:igrp=100:igrpq=2.0:igs=1004:igwr=on:nwc=1:spl=off:urr=on:updr=off:dm=on_300");
    fallback.push("lrs+11_5:1_bd=off:gs=on:gsem=off:gsssp=full:nwc=1.3:sas=minisat:sos=all:sac=on:ssac=none:sscc=model:sdd=large:ssfp=4000:ssfq=1.4:ssnc=none:sp=occurrence_300");
    fallback.push("lrs+1002_2:3_bsr=unit_only:er=known:fde=none:gs=on:gsem=on:nwc=1:sas=minisat:sd=1:ss=axioms:st=1.5:sdd=large:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=none:sp=reverse_arity_300");
    fallback.push("lrs+3_5_bd=preordered:bsr=unit_only:gsp=input_only:gs=on:gsem=on:gsssp=full:lwlo=on:nm=64:nwc=1:sas=minisat:spl=off:sp=occurrence:urr=ec_only:updr=off_900");
    fallback.push("ott+1011_10_cond=fast:fde=none:gsp=input_only:gs=on:gsssp=full:nwc=1:sas=minisat:sd=3:ss=axioms:sos=all:spl=off:sp=occurrence:updr=off_300");
    fallback.push("dis+1002_6_ccuc=first:cond=fast:gsp=input_only:gs=on:gsaa=from_current:gsem=on:gsssp=full:nm=64:nwc=2.5:nicw=on:sas=minisat:sos=on:ssac=none:sscc=on:sdd=large:sfr=on:ssfp=100000:ssfq=1.2:smm=off:sp=occurrence:urr=ec_only:updr=off_300");
    fallback.push("ott+10_5_cond=fast:fde=none:nwc=1:sas=minisat:sos=all:spl=off:sp=occurrence:updr=off_300");
    fallback.push("ins+11_4_cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:gsem=on:igbrr=0.3:igpr=on:igrr=1/8:igrp=100:igrpq=1.5:igwr=on:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:spl=off:dm=on_300");
    fallback.push("lrs+1002_2:3_br=off:fde=unused:gs=on:gsaa=from_current:gsem=on:gsssp=full:igrpq=1.0:nwc=1:sas=minisat:sac=on:sser=off:sfr=on:ssfp=100000:ssfq=2.0:ssnc=none:sp=reverse_arity:urr=on_300");
    fallback.push("dis+11_7_fde=none:igrpq=1.0:nm=0:nwc=1:sd=3:ss=axioms:st=2.0:spl=off:sp=occurrence:urr=on:updr=off_300");
    fallback.push("ott+11_5_nwc=1:sd=7:ss=axioms:st=2.0:sac=on:sfr=on:ssfp=40000:ssfq=1.2:ssnc=none_900");
    fallback.push("dis+11_2_fde=none:gsp=input_only:gs=on:gsem=on:nwc=1:sd=2:ss=axioms:st=1.2:sos=all:spl=off:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("lrs+1002_3_ep=RST:er=known:fsr=off:gs=on:gsaa=from_current:igrpq=1.0:nwc=1:sas=minisat:sd=2:ss=axioms:st=5.0:sos=on:sfr=on:ssfp=100000:ssfq=1.4:smm=sco:ssnc=none:sp=occurrence_300");
    fallback.push("lrs+11_8:1_br=off:cond=on:fsr=off:fde=none:gs=on:inw=on:igrpq=1.0:lwlo=on:nwc=1.5:sser=off:ssfp=10000:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=on_300");
    fallback.push("lrs-2_5_cond=on:fde=none:igrpq=1.0:lcm=predicate:nwc=1:sd=2:ss=axioms:st=3.0:sos=on:sdd=off:ssfp=100000:ssfq=1.4:ssnc=none_300");
    fallback.push("dis+11_4_cond=fast:fsr=off:gs=on:gsaa=from_current:gsem=on:nwc=1:sas=minisat:sd=10:ss=axioms:st=5.0:sos=all:sser=off:ssfp=4000:ssfq=1.0:ssnc=none:sp=occurrence_300");
    fallback.push("ins+11_5_fde=unused:igpr=on:igrr=1/16:igrp=200:igrpq=1.1:igs=1010:igwr=on:nwc=1:sos=all:spl=off_900");
    fallback.push("lrs-1_2:1_bd=preordered:bsr=on:br=off:cond=on:gs=on:lcm=reverse:nwc=1:sd=2:ss=axioms:sos=on:sdd=large:sser=off:ssfp=100000:ssfq=2.0:ssnc=none:sp=occurrence:urr=on:updr=off_300");
    fallback.push("lrs+11_2_br=off:cond=on:fde=none:gs=on:gsaa=full_model:igrpq=1.0:lwlo=on:nwc=2:sas=minisat:ssfp=100000:ssfq=1.4:smm=sco:ssnc=none:sp=occurrence:urr=on_300");
    fallback.push("dis-4_2_cond=on:fde=unused:igrpq=1.0:lcm=reverse:nwc=1:sos=on:spl=off:sp=reverse_arity:updr=off_300");
    fallback.push("dis+4_3:1_gs=on:nwc=1:sd=1:ss=axioms:sos=all:spl=off:updr=off_300");
    fallback.push("dis+1002_4_cond=fast:fde=unused:gsp=input_only:gs=on:gsem=on:igrpq=1.0:nm=64:nwc=1:sas=minisat:sos=on:sscc=model:sser=off:sfr=on:ssfp=4000:ssfq=1.4:ssnc=none:updr=off_300");
    fallback.push("lrs+4_40_bsr=unit_only:cond=fast:fde=none:gs=on:gsem=on:igrpq=1.0:lwlo=on:nwc=1.2:sd=7:ss=axioms:st=5.0:ssac=none:sdd=off:sfr=on:ssfp=1000:ssfq=1.1:smm=sco:ssnc=all_dependent:sp=reverse_arity:tha=off_600");
    fallback.push("lrs+1010_4:1_cond=fast:fsr=off:fde=unused:gs=on:gsem=on:igrpq=1.0:nm=0:nwc=1:sas=minisat:sd=2:ss=axioms:st=1.5:sos=on:sac=on:sdd=off:sser=off:sfr=on:ssfp=100000:ssfq=1.4:ssnc=none:sp=occurrence_300");
    fallback.push("dis+1011_1_cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:igrpq=1.0:nm=0:nwc=1:sas=minisat:sd=3:ss=axioms:sos=on:ssac=none:sfr=on:ssfp=100000:ssfq=1.2:smm=sco:ssnc=none:sp=occurrence_300");
    fallback.push("lrs+1010_8:1_fsr=off:fde=none:gs=on:gsem=on:gsssp=full:igrpq=1.0:nwc=1.1:sas=minisat:sos=all:ssac=none:sfr=on:ssfp=100000:ssfq=1.0:smm=off:ssnc=all:sp=occurrence:updr=off_300");
    fallback.push("dis+11_5_fde=none:gs=on:gsaa=from_current:gsssp=full:igrpq=1.0:lcm=reverse:nwc=1:sas=minisat:ss=axioms:st=1.5:sos=on:ssfp=4000:ssfq=1.2:smm=sco:ssnc=none_300");
    fallback.push("lrs+1002_4_cond=on:er=filter:fde=unused:gsp=input_only:gs=on:gsssp=full:igrpq=1.0:nwc=10:sas=minisat:spl=off:sp=occurrence_300");
    fallback.push("ott+1011_3_bd=off:fde=unused:nwc=1.5:spl=off:sp=occurrence:updr=off_300");
    fallback.push("ott+1002_5_bsr=on:fsr=off:fde=none:gs=on:gsem=off:lwlo=on:nwc=1:sscc=on:sser=off:ssfp=100000:ssfq=1.1:sp=occurrence_300");
    fallback.push("lrs+10_14_cond=on:gs=on:gsem=off:nwc=1.5:nicw=on:sas=minisat:sac=on:sfr=on:ssfp=4000:ssfq=1.2:ssnc=all:sp=reverse_arity:updr=off_300");
    fallback.push("dis+1010_50_gs=on:gsaa=full_model:gsem=on:nwc=4:nicw=on:sas=minisat:ssac=none:sscc=model:ssfp=100000:ssfq=2.0:smm=off:ssnc=none:sp=reverse_arity:updr=off_300");
    fallback.push("dis+11_5_fsr=off:fde=none:gs=on:gsem=off:gsssp=full:inw=on:inst=on:nwc=1:sser=off:sfr=on:ssfp=10000:ssfq=2.0:ssnc=none:sp=reverse_arity:tha=off_300");
    fallback.push("lrs+10_4_ccuc=first:cond=on:gs=on:gsssp=full:nwc=1:sd=2:ss=axioms:st=1.5:sos=on:sscc=on:sser=off:ssfp=40000:ssfq=1.2:ssnc=none:sp=reverse_arity:updr=off_900");
    fallback.push("ott+1004_28_cond=fast:igrpq=1.0:nwc=1:sos=all:spl=off:updr=off_300");
    fallback.push("lrs-1_4_cond=fast:ep=RST:fde=unused:gs=on:gsem=on:gsssp=full:igrpq=1.0:lwlo=on:nwc=1:sas=minisat:spl=off:urr=ec_only_300");
    fallback.push("lrs+1011_3:1_bsr=unit_only:cond=fast:er=known:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=off:igrpq=1.0:nwc=1:sas=minisat:sdd=large:sser=off:sfr=on:ssfp=100000:ssfq=2.0:updr=off_300");
    fallback.push("ott+1010_3:1_cond=fast:fde=none:igrpq=1.0:nwc=1:sos=all:spl=off_300");
    fallback.push("lrs+1010_2:1_bd=off:bsr=unit_only:cond=fast:fde=none:gs=on:gsem=off:igrpq=1.0:nm=0:nwc=2.5:sac=on:sscc=model:sdd=off:ssfp=100000:ssfq=1.4:smm=off:ssnc=none:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("ott+11_24_cond=fast:ep=RST:fsr=off:fde=none:gs=on:lcm=predicate:nm=64:nwc=1:sas=minisat:ss=axioms:st=5.0:sos=all:spl=off:sp=occurrence_300");
    fallback.push("lrs+2_8:1_cond=fast:er=filter:fde=unused:igrpq=1.0:lcm=predicate:nwc=2.5:sas=minisat:sdd=off:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=none:sp=occurrence:updr=off_600");
    fallback.push("lrs+1011_5_bd=off:br=off:ccuc=small_ones:fde=none:gs=on:gsem=off:igrpq=1.0:nwc=1:sd=1:ss=axioms:sos=on:sscc=model:ssfp=100000:ssfq=1.4:smm=off:ssnc=none:sp=occurrence:urr=on_300");
    fallback.push("dis+1011_4_fde=none:gs=on:igrpq=1.0:nwc=1:sos=on:sdd=off:ssfp=10000:ssfq=1.4:smm=sco:ssnc=none:sp=reverse_arity:updr=off_300");
    fallback.push("ott+2_2_cond=fast:fsr=off:gs=on:nwc=1:sd=1:ss=axioms:st=2.0:sos=on:sac=on:sdd=large:sser=off:sfr=on:ssfp=4000:ssfq=1.4:ssnc=none:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("dis-2_4_cond=fast:ep=RST:er=filter:fde=unused:gs=on:gsem=on:igrpq=1.0:lcm=reverse:nwc=1:sd=3:ss=axioms:sos=on:spl=off:updr=off_300");
    fallback.push("ott+1_3:1_cond=fast:gs=on:gsem=off:igrpq=1.0:nwc=1:sas=minisat:sos=all:ssfp=10000:ssfq=1.1:smm=sco:ssnc=none:sp=occurrence:urr=on:updr=off_300");
    fallback.push("lrs+10_2_bsr=unit_only:cond=fast:gsp=input_only:gs=on:gsssp=full:lcm=reverse:lwlo=on:nwc=1:sas=minisat:sos=on:spl=off:sp=reverse_arity_300");
    fallback.push("dis+1010_8_bd=off:bsr=on:ccuc=first:cond=fast:er=known:fsr=off:gs=on:gsssp=full:lcm=reverse:nm=0:nwc=1:sas=minisat:sd=2:ss=axioms:st=5.0:sscc=on:sdd=off:ssfp=100000:ssfq=1.1:urr=ec_only:updr=off_300");
    fallback.push("lrs+10_1_bd=off:fde=none:gsp=input_only:lcm=predicate:nm=0:nwc=1:sos=on:spl=off:updr=off_300");
    fallback.push("dis+11_4_fde=unused:gs=on:gsaa=from_current:nwc=2.5:sac=on:sdd=large:sser=off:ssfp=100000:ssfq=1.4:ssnc=none_300");
    fallback.push("lrs+11_3:2_cond=fast:fsr=off:fde=none:gs=on:igrpq=1.0:nm=0:nwc=1.7:sd=2:ss=axioms:st=2.0:spl=off:urr=on_300");
    fallback.push("lrs-3_2:1_bsr=unit_only:fde=none:gs=on:gsssp=full:nm=0:nwc=1.5:sas=minisat:sos=all:sac=on:smm=sco:ssnc=none:sp=occurrence_300");
    fallback.push("lrs+10_8_br=off:fsr=off:gsp=input_only:gs=on:gsem=off:igrpq=1.0:nwc=1:sas=minisat:spl=off:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("dis+2_5:4_fde=none:igrpq=1.0:nwc=1:sd=2:ss=axioms:sos=on:ssfp=40000:ssfq=2.0_300");
    fallback.push("lrs+1002_7_ccuc=first:cond=on:fde=none:gs=on:gsssp=full:igrpq=1.0:nwc=1:sas=minisat:sd=3:ss=axioms:sscc=model:sser=off:ssfp=1000:ssfq=2.0:ssnc=none:sp=reverse_arity_900");
    fallback.push("ins+10_1_spl=off_300");
    fallback.push("lrs+11_28_cond=on:gs=on:gsaa=from_current:gsem=on:gsssp=full:igrpq=1.0:lwlo=on:nm=64:nwc=1.7:sac=on:sdd=off:sfr=on:ssfp=40000:ssfq=1.1:smm=off:ssnc=none:urr=on:updr=off_300");
    fallback.push("lrs+1_3:1_cond=fast:gsp=input_only:gs=on:gsaa=from_current:gsem=off:igrpq=1.0:nwc=1:sd=2:ss=axioms:st=1.2:sos=on:sac=on:sdd=off:sfr=on:ssfp=100000:ssfq=1.2:smm=sco:ssnc=none:sp=reverse_arity_300");
    fallback.push("dis+3_3:2_cond=on:fde=none:gs=on:gsem=on:nm=64:nwc=1:sos=on:sac=on:sdd=off:sfr=on:ssfp=10000:ssfq=1.2:smm=off:ssnc=none:sp=occurrence_300");
    fallback.push("dis+1010_5:1_cond=fast:ep=RSTC:er=known:fde=unused:igrpq=1.0:nm=0:nwc=2:spl=off_300");
    fallback.push("lrs+1002_3_bd=off:bs=on:bsr=unit_only:cond=fast:fsr=off:igrpq=1.0:lcm=predicate:nwc=1.5:sos=on:sdd=off:sser=off:sfr=on:sp=reverse_arity_300");
    fallback.push("dis+10_1024_cond=fast:fde=none:gs=on:gsem=off:nwc=1:sd=7:ss=axioms:st=5.0:sos=all:spl=off:sp=reverse_arity_300");
    fallback.push("lrs+4_3:1_bs=on:bsr=unit_only:ccuc=small_ones:cond=fast:er=filter:fsr=off:lcm=predicate:nm=1024:nwc=1:sas=minisat:sos=on:sac=on:sscc=on:ssfp=1000:ssfq=1.2:smm=sco:ssnc=all_dependent:sp=reverse_arity:updr=off_300");
    fallback.push("dis+11_5_fde=none:igrpq=1.0:nwc=1:sas=minisat:sd=1:ss=axioms:st=5.0:sos=all:sdd=large:sser=off:sfr=on:ssfp=100000:ssfq=2.0:ssnc=none_300");
    fallback.push("ott+2_8_bsr=unit_only:cond=fast:fde=none:gs=on:igrpq=1.0:lwlo=on:nwc=1:sas=minisat:spl=off_300");
    fallback.push("ins+11_3_cond=on:fde=none:gs=on:gsem=off:gsssp=full:igbrr=1.0:igrr=1/16:igrp=100:igrpq=1.05:igs=1:igwr=on:nwc=1:sas=minisat:sos=on:spl=off:sp=occurrence:urr=on_300");
    fallback.push("dis+11_20_fsr=off:fde=unused:gs=on:gsssp=full:igrpq=1.0:nm=0:nwc=1.3:nicw=on:sdd=large:sfr=on:ssfp=4000:ssfq=1.0:smm=off:ssnc=all:sp=reverse_arity_300");
    fallback.push("lrs+3_4:1_bs=unit_only:bsr=on:cond=on:er=known:fde=none:lcm=predicate:lwlo=on:nwc=1.5:sas=minisat:sos=all:sfr=on:ssfp=100000:ssfq=1.1:smm=sco:ssnc=all_dependent:sp=occurrence:updr=off_2100");
    fallback.push("ins+10_1_igbrr=0.6:igrpq=1.5:igs=1002:nwc=1:spl=off:sp=reverse_arity:tha=off:dm=on_600");
    fallback.push("lrs+1010_2:1_bd=preordered:bs=on:cond=fast:fde=none:gs=on:inw=on:igrpq=1.0:lwlo=on:nwc=1:sas=minisat:sos=all:spl=off_600");
    fallback.push("lrs+11_3_gs=on:nwc=1.3:spl=off:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("ott+11_4:1_bd=off:bsr=unit_only:cond=on:fsr=off:lcm=reverse:nwc=1:sas=minisat:sos=on:spl=off:urr=on:updr=off_300");
    fallback.push("ott+1_4_er=filter:fsr=off:nwc=1:sdd=large:sser=off:sfr=on:ssfp=40000:ssfq=1.0:ssnc=none:sp=reverse_arity_300");
    fallback.push("dis+1010_5:1_fde=none:igrpq=1.0:lwlo=on:nm=0:nwc=1:sas=minisat:sos=on:sdd=off:sfr=on:ssfp=1000:ssfq=1.1:ssnc=none:sp=reverse_arity:tha=off_300");
    fallback.push("lrs+1003_7_cond=fast:igrpq=1.0:nwc=1:sd=4:ss=axioms:sos=all:spl=off:updr=off_300");
    fallback.push("dis+1010_1_fde=none:gs=on:gsem=off:gsssp=full:igrpq=1.0:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:sfr=on:smm=off:ssnc=all:sp=reverse_arity:updr=off_300");
    fallback.push("dis+2_2:1_cond=on:er=filter:fde=none:gs=on:gsem=on:igrpq=1.0:nwc=1:sac=on:sdd=large:ssfp=10000:ssfq=1.2:smm=off:sp=occurrence_300");
    fallback.push("dis+11_3_cond=fast:fsr=off:gs=on:gsem=off:gsssp=full:inw=on:nwc=1.7:sas=minisat:sdd=off:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:sp=occurrence:urr=on:updr=off_300");
    fallback.push("ott+11_14_bd=preordered:fsr=off:gs=on:gsem=off:igrpq=1.0:nwc=2:ssfp=4000:ssfq=1.2:smm=off:ssnc=none:sp=reverse_arity:updr=off_300");
    fallback.push("dis+1003_8:1_bd=off:bs=unit_only:cond=fast:fsr=off:fde=none:gsp=input_only:igrpq=1.0:lcm=reverse:nwc=1:sas=minisat:sos=all:ssac=none:sscc=on:sdd=off:sfr=on:smm=sco:ssnc=none:sp=reverse_arity_300");
    fallback.push("dis+11_5_cond=on:fsr=off:fde=none:gsp=input_only:igrpq=1.0:lcm=reverse:nm=0:nwc=4:sfr=on:ssfp=100000:ssfq=1.0:smm=sco:ssnc=none:updr=off_300");
    fallback.push("ott+1010_3:1_bd=off:bs=unit_only:bsr=unit_only:fsr=off:gs=on:gsaa=from_current:nwc=1.7:sser=off:ssfp=10000:ssfq=1.2:ssnc=none:sp=occurrence:urr=ec_only_300");
    fallback.push("ott+1_2_cond=fast:er=filter:fsr=off:fde=none:gs=on:gsem=off:gsssp=full:igrpq=1.0:nwc=1:sas=minisat:sd=1:ss=axioms:st=1.2:sac=on:sdd=large:sfr=on:ssfp=40000:ssfq=1.0:smm=sco:ssnc=none_300");
    fallback.push("ott-11_4_br=off:cond=on:gs=on:gsem=off:gsssp=full:igrpq=1.0:nwc=5:sas=minisat:sac=on:sdd=large:sfr=on:ssfp=4000:ssfq=2.0:ssnc=all:sp=occurrence:urr=on:updr=off_300");
    fallback.push("lrs+10_2_bd=off:bsr=unit_only:ccuc=first:cond=fast:fsr=off:fde=none:gs=on:gsem=on:nwc=1.5:nicw=on:sos=all:sac=on:ssac=none:sscc=model:sfr=on:ssfp=10000:ssfq=2.0:smm=off:ssnc=none:sp=occurrence:updr=off_2400");
    fallback.push("dis+1011_2_fde=unused:gs=on:igrpq=1.0:nwc=1:sac=on:ssfp=40000:ssfq=1.1:smm=off:ssnc=none:sp=reverse_arity:urr=ec_only_300");
    fallback.push("lrs+3_5:1_bd=off:bs=unit_only:bsr=unit_only:br=off:ccuc=small_ones:er=known:fsr=off:fde=unused:gs=on:nm=0:nwc=1.1:sd=3:ss=axioms:sos=on:sscc=model:sdd=off:sser=off:ssfp=4000:ssfq=1.4:sp=occurrence:urr=on:updr=off_300");
    fallback.push("lrs+1004_2:1_cond=fast:fde=none:gs=on:gsem=off:igrpq=1.0:nwc=1:sd=2:ss=axioms:sos=on:spl=off:sp=reverse_arity:updr=off_300");
    fallback.push("dis+1010_4:1_cond=fast:fsr=off:igrpq=1.0:nm=0:nwc=1:sas=minisat:sac=on:sdd=large:sfr=on:ssfp=40000:ssfq=2.0:smm=sco:ssnc=none:sp=occurrence:urr=ec_only_300");
    fallback.push("lrs-11_2_cond=on:fde=unused:gs=on:igrpq=1.0:nwc=3:sdd=off:sfr=on:ssfp=100000:ssfq=1.4:smm=sco:ssnc=all_300");
    fallback.push("lrs+1011_8_br=off:cond=fast:fsr=off:fde=none:igrpq=1.0:nwc=1:sas=minisat:sd=2:ss=axioms:sos=all:spl=off:urr=on_300");
    fallback.push("lrs+11_4:1_fsr=off:fde=unused:gs=on:gsem=off:igrpq=1.0:nwc=1:sas=minisat:spl=off:sp=reverse_arity:urr=ec_only_300");
    fallback.push("ott+4_8_bsr=unit_only:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:igrpq=1.0:nwc=1:sos=all:sac=on:ssfp=100000:ssfq=1.1:smm=off:ssnc=none:sp=reverse_arity_300");
    fallback.push("dis+11_8_bs=unit_only:nwc=1:sd=10:ss=axioms:st=1.5:spl=off:sp=occurrence:updr=off_900");
    fallback.push("dis+1003_3:2_bd=off:bsr=unit_only:nwc=1.3:sas=minisat:sac=on:sdd=large:sser=off:sfr=on:ssfp=1000:ssfq=1.2:ssnc=none:updr=off_300");
    fallback.push("dis+1003_3_bs=unit_only:cond=fast:gs=on:gsaa=full_model:igrpq=1.0:lwlo=on:nwc=1.5:sas=minisat:sd=1:ss=axioms:st=2.0:sac=on:sdd=large:sfr=on:ssfp=100000:ssfq=1.2:ssnc=none:sp=reverse_arity:updr=off_300");
    fallback.push("dis+11_4:1_br=off:ccuc=first:fsr=off:fde=none:igrpq=1.0:nm=0:nwc=1:sos=all:sscc=model:sdd=off:sser=off:ssfp=10000:ssfq=1.1:ssnc=all_dependent:sp=occurrence:urr=on:updr=off_300");
    fallback.push("dis+4_64_bs=unit_only:cond=on:er=known:fde=unused:gs=on:gsem=off:igrpq=1.0:nwc=1.2:sas=minisat:ssac=none:sser=off:sfr=on:ssfp=10000:ssfq=2.0:ssnc=all:sp=reverse_arity:updr=off_300");
    fallback.push("ott+11_2:1_cond=on:gs=on:gsssp=full:lwlo=on:nwc=1:sas=minisat:sos=all:spl=off:sp=occurrence:tha=off_300");
    fallback.push("ott+11_6_cond=fast:fsr=off:fde=unused:gs=on:gsem=off:gsssp=full:inw=on:igrpq=1.0:nwc=1.5:sas=minisat:spl=off:sp=occurrence:urr=on_300");
    fallback.push("lrs+1011_2:1_br=off:cond=fast:fde=none:gs=on:gsssp=full:nwc=1:sos=all:sac=on:sdd=off:ssfp=1000:ssfq=2.0:smm=sco:ssnc=none:urr=on_300");
    fallback.push("lrs+11_2_bd=off:ccuc=first:cond=on:fde=unused:gs=on:gsem=off:nwc=1:sos=all:sscc=model:sdd=large:sser=off:ssfp=4000:ssfq=1.1:ssnc=none:sp=occurrence:updr=off_300");
    fallback.push("dis+1002_2_cond=on:gs=on:inw=on:nwc=1:sas=minisat:sos=on:sac=on:sdd=large:sser=off:sfr=on:ssfp=4000:ssfq=1.2:ssnc=none:sp=reverse_arity_300");
    fallback.push("ins+11_3_bsr=unit_only:fde=none:gs=on:gsem=off:igbrr=0.0:igrr=1/16:igrpq=1.5:igs=1004:igwr=on:lcm=reverse:nm=0:nwc=1:sos=all:spl=off:updr=off:dm=on_300");
    fallback.push("ott+1011_1024_bd=preordered:bs=on:cond=on:nwc=1:spl=off:updr=off_300");
    fallback.push("ott-1_2:3_bs=unit_only:bsr=unit_only:fde=none:gs=on:gsem=on:gsssp=full:nwc=1:sas=minisat:sos=on:sdd=large:sfr=on:ssfp=1000:ssfq=1.4:smm=off:ssnc=all:sp=occurrence_300");
    fallback.push("lrs+4_64_fsr=off:igrpq=1.0:nwc=1.5:sas=minisat:spl=off:sp=occurrence_300");
    fallback.push("lrs+1_5:4_cond=on:fsr=off:fde=none:gs=on:gsem=on:igrpq=1.0:lwlo=on:nm=64:nwc=1:sos=all:spl=off_600");
    fallback.push("lrs-4_4_cond=fast:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=off:gsssp=full:lcm=reverse:nwc=1:sas=minisat:sd=4:ss=axioms:sos=on:sac=on:ssac=none:sdd=large:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:sp=reverse_arity_300");
    fallback.push("dis+10_3_cond=fast:fsr=off:gs=on:gsaa=from_current:nwc=1:sas=minisat:sac=on:ssfp=10000:ssfq=1.0:smm=sco:ssnc=none:sp=occurrence:tha=off_300");
    fallback.push("lrs+11_1_br=off:fde=unused:gs=on:gsem=off:inw=on:nwc=1:sas=minisat:sac=on:sscc=model:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("dis+1010_5:1_bs=unit_only:ccuc=small_ones:cond=on:fsr=off:fde=none:gs=on:gsem=off:nm=0:nwc=3:sos=on:sac=on:sscc=on:ssfp=40000:ssfq=1.2:smm=sco:ssnc=all_dependent:sp=occurrence:urr=ec_only_300");
    fallback.push("lrs+10_8:1_bd=preordered:bs=on:ccuc=first:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=on:gsssp=full:nwc=1:nicw=on:sas=minisat:sos=on:sscc=on:sser=off:sfr=on:ssfp=4000:ssfq=1.0:ssnc=none:sp=reverse_arity:urr=on_1200");
    fallback.push("dis+11_5_bd=off:cond=fast:fde=unused:gs=on:gsem=on:igrpq=1.0:lwlo=on:nwc=1:sos=on:sac=on:sdd=off:sser=off:sfr=on:ssfp=10000:ssfq=2.0:ssnc=none:sp=reverse_arity:urr=on_300");
    fallback.push("lrs+10_50_bd=off:bs=unit_only:bsr=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:nwc=1.3:nicw=on:sos=all:sdd=off:sser=off:sfr=on:ssfp=10000:ssfq=2.0:ssnc=none:sp=occurrence_300");
    fallback.push("lrs+1011_12_bs=on:bsr=unit_only:cond=on:gs=on:gsaa=from_current:gsssp=full:nwc=1.1:sas=minisat:sos=all:sac=on:sdd=off:sser=off:sfr=on:ssfp=100000:ssfq=1.2:ssnc=none:sp=reverse_arity:updr=off_600");
    fallback.push("ott+11_20_bs=unit_only:fsr=off:gsp=input_only:gs=on:gsaa=full_model:gsem=off:gsssp=full:nwc=1:sac=on:ssfp=1000:ssfq=2.0:ssnc=none:sp=occurrence_600");
    fallback.push("lrs+4_5_cond=fast:fsr=off:fde=none:gs=on:gsaa=from_current:igrpq=1.0:nwc=1:sd=5:ss=axioms:st=1.2:sac=on:sdd=off:sser=off:sfr=on:ssfp=4000:ssfq=2.0:ssnc=none:sp=occurrence_900");
    fallback.push("lrs+1011_4_cond=fast:gs=on:gsaa=from_current:gsem=off:gsssp=full:nwc=1:sd=5:ss=axioms:st=3.0:sac=on:sdd=off:sser=off:sfr=on:ssfp=1000:ssfq=1.0:ssnc=none_900");
} // getSchedule


#endif //!COMPILER_MSVC
