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

#define SLOWNESS 1.15
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
  if(terminationTime <= 0){ return false; }
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
  if(coreNumber < 1){ coreNumber = 1; }
  unsigned requested = env.options->multicore();
  int parallelProcesses = min(coreNumber,requested);

  // if requested is 0 then use (sensible) max
  if(parallelProcesses == 0){
    if(coreNumber >=8){ coreNumber = coreNumber-2; }
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
    env.beginOutput();
    SMTCOMPMode::lineOutput() << " found a proof after proof output" << endl;
    env.endOutput();
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
    Property::Category cat = property.category();
    unsigned long prop = property.props();
    unsigned atoms = property.atoms();
    
#if VZ3
    // quick.push("dis+1011_5_fsr=off:gs=on:gsaa=full_model:gsssp=full:nwc=1:sas=z3:sos=on:ssfp=40000:ssfq=2.0:smm=sco:ssnc=all:tha=off:updr=off_1");
    // quick.push("dis+10_3_br=off:cond=fast:fde=none:gs=on:gsem=on:gsssp=full:inw=on:nwc=1:sas=minisat:sos=all:sac=on:sdd=large:ssfp=100000:ssfq=1.1:ssnc=none:sp=reverse_arity:urr=on_1");
    // quick.push("lrs+1002_3_fde=none:gs=on:nwc=1:sas=z3:stl=30:sos=on:sdd=large:sser=off:ssfp=4000:ssfq=1.1:ssnc=all:tha=off:updr=off_21");
    // quick.push("dis+11_5_cond=fast:fsr=off:gs=on:gsem=on:gsssp=full:nwc=1:sac=on:ssfp=100000:ssfq=1.2:smm=sco:ssnc=none:sp=occurrence:thf=on_1");
    // quick.push("dis+1010_5:1_fde=none:lwlo=on:nm=0:nwc=1:sas=minisat:sos=on:sdd=off:sfr=on:ssfp=1000:ssfq=1.1:ssnc=none:sp=reverse_arity:tha=off_12");
    // quick.push("lrs+1010_2:1_bd=off:bsr=unit_only:cond=fast:fde=none:gs=on:gsem=off:nm=0:nwc=2.5:stl=30:sac=on:sscc=model:sdd=off:ssfp=100000:ssfq=1.4:smm=off:ssnc=none:sp=reverse_arity:urr=on:updr=off_28");
    // quick.push("dis+11_4_cond=fast:fsr=off:gs=on:gsaa=from_current:gsem=on:nwc=1:sas=minisat:sd=10:ss=axioms:st=5.0:sos=all:sser=off:ssfp=4000:ssfq=1.0:ssnc=none:sp=occurrence_55");
    // quick.push("lrs-10_3:2_bs=unit_only:bsr=unit_only:ccuc=small_ones:cond=fast:gsp=input_only:gs=on:gsaa=from_current:inst=on:nm=0:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:ssac=none:sscc=on:ssfp=100000:ssfq=1.1:smm=sco:sp=reverse_arity:tha=off:thf=on_24");
    // quick.push("dis+10_5_bd=off:cond=fast:fsr=off:fde=unused:gsp=input_only:gs=on:gsem=off:nwc=1:sas=minisat:sos=on:sfr=on:ssfp=10000:ssfq=1.1:smm=off:ssnc=none:sp=occurrence:urr=ec_only:updr=off_2");
    // quick.push("lrs+2_8:1_cond=fast:er=filter:fde=unused:lcm=predicate:nwc=2.5:sas=minisat:stl=60:sdd=off:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=none:sp=occurrence:updr=off_9");
    // quick.push("ott+11_2:1_cond=on:gs=on:gsssp=full:lwlo=on:nwc=1:sas=minisat:sos=all:spl=off:sp=occurrence:tha=off_12");
    // quick.push("lrs+11_8:1_br=off:cond=on:fsr=off:fde=none:gs=on:inw=on:lwlo=on:nwc=1.5:stl=30:sser=off:ssfp=10000:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=on_99");
    // quick.push("lrs+4_3:1_bd=off:fsr=off:fde=none:gs=on:gsem=on:lcm=reverse:nwc=2.5:nicw=on:sas=z3:stl=30:sscc=model:sser=off:sfr=on:ssfp=1000:ssfq=1.1:ssnc=none:sp=reverse_arity:updr=off_10");
    // quick.push("dis+1010_12_bd=off:gs=on:gsaa=from_current:gsem=on:nm=0:nwc=4:sas=z3:sser=off:ssfp=4000:ssfq=1.2:ssnc=all:sp=occurrence:tha=off_16");
    // quick.push("dis+10_1024_cond=fast:fde=none:gs=on:gsem=off:nwc=1:sd=7:ss=axioms:st=5.0:sos=all:spl=off:sp=reverse_arity_12");
    // quick.push("ott+1003_3:1_br=off:cond=fast:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=on:inw=on:nwc=1:sas=z3:sos=all:ssfp=4000:ssfq=2.0:smm=off:ssnc=all_dependent:sp=occurrence:tha=off:urr=on_4");
    // quick.push("ins+11_32_br=off:ep=RSTC:inw=on:igbrr=0.9:igrr=1/32:igrp=100:igrpq=2.0:igs=1004:igwr=on:nwc=1:spl=off:urr=on:updr=off:dm=on_163");
    // quick.push("lrs+11_5:1_bd=off:gs=on:gsem=off:gsssp=full:nwc=1.3:sas=minisat:stl=30:sos=all:sac=on:ssac=none:sscc=model:sdd=large:ssfp=4000:ssfq=1.4:ssnc=none:sp=occurrence_117");
    // quick.push("lrs+1010_1_bs=on:bsr=unit_only:ccuc=first:cond=fast:gs=on:gsaa=from_current:inw=on:nwc=1:sas=z3:stl=30:sos=on:sac=on:sscc=on:sdd=large:ssfp=100000:ssfq=1.4:smm=sco:ssnc=none:sp=reverse_arity:tha=off:thf=on_45");
    // quick.push("dis+11_1_cond=on:fsr=off:lcm=reverse:nwc=2.5:spl=off:sp=reverse_arity:updr=off_74");
    // quick.push("dis+1002_5:1_bsr=unit_only:cond=fast:er=filter:fsr=off:fde=unused:lcm=reverse:nm=0:nwc=4:sas=z3:ssac=none:sdd=off:sser=off:sfr=on:ssfp=100000:ssfq=1.1:sp=reverse_arity:tha=off:urr=ec_only:updr=off_8");
    // quick.push("ott-11_4_br=off:cond=on:gs=on:gsem=off:gsssp=full:nwc=5:sas=minisat:sac=on:sdd=large:sfr=on:ssfp=4000:ssfq=2.0:ssnc=all:sp=occurrence:urr=on:updr=off_48");
    // quick.push("dis+1003_3:2_bd=off:bsr=unit_only:nwc=1.3:sas=minisat:sac=on:sdd=large:sser=off:sfr=on:ssfp=1000:ssfq=1.2:ssnc=none:updr=off_23");
    // quick.push("lrs+1011_2:3_fsr=off:gs=on:gsaa=from_current:gsem=on:gsssp=full:nm=0:nwc=5:sas=z3:stl=30:sscc=on:ssfp=40000:ssfq=1.0:smm=sco:ssnc=none:sp=reverse_arity:tha=off:updr=off_267");
    // quick.push("lrs+4_40_bsr=unit_only:cond=fast:fde=none:gs=on:gsem=on:lwlo=on:nwc=1.2:stl=60:sd=7:ss=axioms:st=5.0:ssac=none:sdd=off:sfr=on:ssfp=1000:ssfq=1.1:smm=sco:ssnc=all_dependent:sp=reverse_arity:tha=off_263");
    // quick.push("dis+10_3_cond=fast:fsr=off:gs=on:gsaa=from_current:nwc=1:sas=minisat:sac=on:ssfp=10000:ssfq=1.0:smm=sco:ssnc=none:sp=occurrence:tha=off_206");
    // quick.push("lrs+1010_2:1_bd=preordered:bs=on:cond=fast:fde=none:gs=on:inw=on:lwlo=on:nwc=1:sas=minisat:stl=60:sos=all:spl=off_216");
    // quick.push("ins+10_1_igbrr=0.6:igrpq=1.5:igs=1002:nwc=1:spl=off:sp=reverse_arity:tha=off:dm=on_562");
    // quick.push("dis+11_7_16");
    // quick.push("ins+11_5_cond=on:gs=on:gsem=off:igbrr=0.3:igpr=on:igrr=1/32:igrp=200:igrpq=2.0:igs=1004:igwr=on:nwc=1:sos=all:spl=off:sp=occurrence:dm=on_18");
    
    // By keeping the following code we will add the vampire strategies to vampireZ3
    // When solving smt-lib problems (with 30 minute time limits) this could help!
#endif
    
    // for theory problems, we make the schedule before the main choice
    if (prop & (524288ul | 1048576ul | 2097152ul)) { // theories
        if (prop == 13107200ul) {
            quick.push("dis+11_4_cond=fast:fsr=off:gs=on:gsaa=from_current:gsem=on:nwc=1:sas=minisat:sd=10:ss=axioms:st=5.0:sos=all:sser=off:ssfp=4000:ssfq=1.0:ssnc=none:sp=occurrence_55");
            quick.push("dis+1_1024_bs=on:cond=fast:fde=none:inst=on:nwc=1:spl=off:sp=reverse_arity:tha=off:thf=on:urr=on:uhcvi=on_772");
            quick.push("lrs+1_2_bs=on:bsr=on:fsr=off:fde=none:gs=on:nm=64:nwc=5:sas=minisat:stl=150:ssac=none:sfr=on:smm=off:ssnc=all:sp=reverse_arity:tha=off_1394");
        }
        else {
            quick.push("ins+11_5_cond=on:gs=on:gsem=off:igbrr=0.3:igpr=on:igrr=1/32:igrp=200:igrpq=2.0:igs=1004:igwr=on:nwc=1:sos=all:spl=off:sp=occurrence:dm=on_18");
            quick.push("dis+1011_5_fsr=off:gs=on:gsaa=full_model:gsssp=full:nwc=1:sas=z3:sos=on:ssfp=40000:ssfq=2.0:smm=sco:ssnc=all:tha=off:updr=off_1");
            quick.push("dis+1002_5:1_bsr=unit_only:cond=fast:er=filter:fsr=off:fde=unused:lcm=reverse:nm=0:nwc=4:sas=z3:ssac=none:sdd=off:sser=off:sfr=on:ssfp=100000:ssfq=1.1:sp=reverse_arity:tha=off:urr=ec_only:updr=off_8");
            quick.push("lrs+4_3:1_bd=off:fsr=off:fde=none:gs=on:gsem=on:lcm=reverse:nwc=2.5:nicw=on:sas=z3:stl=30:sscc=model:sser=off:sfr=on:ssfp=1000:ssfq=1.1:ssnc=none:sp=reverse_arity:updr=off_1");
            quick.push("lrs+1004_5:1_gs=on:gsaa=from_current:gsssp=full:nm=0:nwc=5:sas=z3:stl=60:ssac=none:sdd=off:sser=off:ssfp=40000:ssfq=1.1:ssnc=all_dependent_9");
            quick.push("dis+11_3_cond=fast:fsr=off:gs=on:gsem=off:gsssp=full:inw=on:nwc=1.7:sas=minisat:sdd=off:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:sp=occurrence:urr=on:updr=off_4");
            quick.push("lrs+1002_3_fde=none:gs=on:nwc=1:sas=z3:stl=30:sos=on:sdd=large:sser=off:ssfp=4000:ssfq=1.1:ssnc=all:tha=off:updr=off_21");
            quick.push("dis+4_128_cond=fast:fsr=off:fde=unused:gs=on:gsem=on:inst=on:lcm=predicate:nwc=1:sas=minisat:sdd=large:sser=off:sfr=on:ssfp=40000:ssfq=2.0:ssnc=none:tha=off:updr=off:uhcvi=on_6");
            quick.push("dis+11_8:1_bsr=unit_only:gs=on:gsssp=full:nm=0:nwc=1:nicw=on:sas=minisat:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_1");
            quick.push("ott+1010_128_cond=fast:fde=unused:gs=on:gsssp=full:nm=1024:nwc=1.1:sas=z3:sos=on:ssac=none:sscc=model:sdd=large:sser=off:ssfp=4000:ssfq=1.1:ssnc=all_dependent:sp=occurrence:tha=off_8");
            quick.push("ott-11_4_br=off:cond=on:gs=on:gsem=off:gsssp=full:nwc=5:sas=minisat:sac=on:sdd=large:sfr=on:ssfp=4000:ssfq=2.0:ssnc=all:sp=occurrence:urr=on:updr=off_48");
            quick.push("lrs+10_40_bd=off:bs=unit_only:bsr=unit_only:ccuc=first:fsr=off:gs=on:gsem=on:lcm=reverse:nwc=3:nicw=on:sas=z3:stl=30:sac=on:ssac=none:sscc=model:sdd=off:sfr=on:smm=off:ssnc=none:sp=occurrence:tha=off_12");
            quick.push("dis+10_1024_cond=fast:fde=none:gs=on:gsem=off:nwc=1:sd=7:ss=axioms:st=5.0:sos=all:spl=off:sp=reverse_arity_12");
            quick.push("lrs-10_2:1_bsr=unit_only:gs=on:gsaa=from_current:lcm=reverse:nwc=1.1:nicw=on:sas=z3:stl=90:ssac=none:sscc=on:sdd=large:ssfp=10000:ssfq=1.1:smm=sco:sp=occurrence:tha=off:urr=ec_only_11");
            quick.push("ins+11_32_br=off:ep=RSTC:inw=on:igbrr=0.9:igrr=1/32:igrp=100:igrpq=2.0:igs=1004:igwr=on:nwc=1:spl=off:urr=on:updr=off:dm=on_163");
            quick.push("lrs+11_2:1_bd=off:bsr=on:br=off:fsr=off:fde=none:gs=on:gsem=off:nwc=1:sas=z3:stl=30:sos=all:sdd=off:ssfp=40000:ssfq=1.1:smm=sco:ssnc=all:thf=on:urr=on:updr=off_46");
            quick.push("lrs+1010_5:4_bd=off:bs=unit_only:fde=none:gs=on:gsaa=full_model:gsem=on:inw=on:nwc=1.3:sas=z3:stl=30:sos=all:sfr=on:ssfp=4000:ssfq=1.1:smm=sco:sp=occurrence_71");
            quick.push("lrs+1002_3:1_cond=on:fde=unused:inst=on:nm=1024:nwc=2:sas=minisat:stl=30:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:sp=occurrence:tha=off:updr=off_14");
            quick.push("lrs+1010_1_bs=on:bsr=unit_only:ccuc=first:cond=fast:gs=on:gsaa=from_current:inw=on:nwc=1:sas=z3:stl=30:sos=on:sac=on:sscc=on:sdd=large:ssfp=100000:ssfq=1.4:smm=sco:ssnc=none:sp=reverse_arity:tha=off:thf=on_45");
            quick.push("lrs+4_32_bsr=unit_only:cond=on:er=filter:fde=unused:gs=on:gsssp=full:inst=on:lcm=predicate:nm=64:nwc=1.1:stl=30:ss=priority:st=2.0:sos=on:sdd=off:ssfp=10000:ssfq=1.2:smm=sco:sp=occurrence:urr=on:updr=off:uhcvi=on_85");
            quick.push("lrs+11_5:1_bd=off:gs=on:gsem=off:gsssp=full:nwc=1.3:sas=minisat:stl=30:sos=all:sac=on:ssac=none:sscc=model:sdd=large:ssfp=4000:ssfq=1.4:ssnc=none:sp=occurrence_117");
            quick.push("ott+11_2:1_cond=on:gs=on:gsssp=full:lwlo=on:nwc=1:sas=minisat:sos=all:spl=off:sp=occurrence:tha=off_12");
            quick.push("lrs+2_8:1_cond=fast:er=filter:fde=unused:lcm=predicate:nwc=2.5:sas=minisat:stl=60:sdd=off:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=none:sp=occurrence:updr=off_9");
            quick.push("dis+1010_5:1_fde=none:lwlo=on:nm=0:nwc=1:sas=minisat:sos=on:sdd=off:sfr=on:ssfp=1000:ssfq=1.1:ssnc=none:sp=reverse_arity:tha=off_12");
            quick.push("dis+1003_3:2_bd=off:bsr=unit_only:nwc=1.3:sas=minisat:sac=on:sdd=large:sser=off:sfr=on:ssfp=1000:ssfq=1.2:ssnc=none:updr=off_23");
            quick.push("lrs+11_1_br=off:fde=unused:gs=on:gsem=off:inw=on:nwc=1:sas=minisat:stl=30:sac=on:sscc=model:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=on:updr=off_3");
            quick.push("lrs+1010_2:1_bd=off:bsr=unit_only:cond=fast:fde=none:gs=on:gsem=off:nm=0:nwc=2.5:stl=30:sac=on:sscc=model:sdd=off:ssfp=100000:ssfq=1.4:smm=off:ssnc=none:sp=reverse_arity:urr=on:updr=off_28");
            quick.push("dis+1004_8:1_bd=off:bsr=unit_only:ccuc=first:cond=fast:fde=unused:nm=0:nwc=1.2:sas=minisat:sscc=on:sfr=on:ssfp=1000:ssfq=2.0:ssnc=none:urr=on_92");
            quick.push("lrs+1011_2:3_fsr=off:gs=on:gsaa=from_current:gsem=on:gsssp=full:nm=0:nwc=5:sas=z3:stl=30:sscc=on:ssfp=40000:ssfq=1.0:smm=sco:ssnc=none:sp=reverse_arity:tha=off:updr=off_267");
            quick.push("ott-1_5:1_ccuc=first:fsr=off:gs=on:lcm=reverse:nm=64:nwc=1.1:nicw=on:ssac=none:sscc=on:sfr=on:ssfp=10000:ssfq=1.2:smm=sco:ssnc=none:sp=reverse_arity:urr=on_109");
            quick.push("lrs+1004_1_cond=fast:fde=unused:gs=on:gsem=off:gsssp=full:lwlo=on:nwc=2.5:sas=minisat:stl=150:spl=off:tha=off:thf=on:urr=ec_only:uhcvi=on_1008");
            quick.push("dis+1010_12_bd=off:gs=on:gsaa=from_current:gsem=on:nm=0:nwc=4:sas=z3:sser=off:ssfp=4000:ssfq=1.2:ssnc=all:sp=occurrence:tha=off_16");
            quick.push("dis+11_1_cond=on:fsr=off:lcm=reverse:nwc=2.5:spl=off:sp=reverse_arity:updr=off_74");
        }
        
        // add very long final fallback strategy
        fallback.push("lrs+1010_2:1_bd=off:bsr=unit_only:cond=fast:fde=none:gs=on:gsem=off:igrpq=1.0:nm=0:nwc=2.5:sac=on:sscc=model:sdd=off:ssfp=100000:ssfq=1.4:smm=off:ssnc=none:sp=reverse_arity:urr=on:updr=off_300");
        fallback.push("dis+1003_2:1_bd=off:bs=unit_only:cond=fast:fde=unused:gsp=input_only:gs=on:gsem=off:inw=on:inst=on:nm=0:nwc=3:sas=z3:sos=all:sscc=model:sdd=off:sser=off:sfr=on:ssfp=4000:ssfq=1.1:sp=occurrence:tha=off_300");
        fallback.push("lrs+11_5:1_bd=off:gs=on:gsem=off:gsssp=full:nwc=1.3:sas=minisat:sos=all:sac=on:ssac=none:sscc=model:sdd=large:ssfp=4000:ssfq=1.4:ssnc=none:sp=occurrence_300");
        fallback.push("ins+11_32_br=off:ep=RSTC:inw=on:igbrr=0.9:igrr=1/32:igrp=100:igrpq=2.0:igs=1004:igwr=on:nwc=1:spl=off:urr=on:updr=off:dm=on_300");
        fallback.push("dis+11_4_cond=fast:fsr=off:gs=on:gsaa=from_current:gsem=on:nwc=1:sas=minisat:sd=10:ss=axioms:st=5.0:sos=all:sser=off:ssfp=4000:ssfq=1.0:ssnc=none:sp=occurrence_300");
        fallback.push("lrs+1_2_bs=on:bsr=on:fsr=off:fde=none:gs=on:nm=64:nwc=5:sas=minisat:ssac=none:sfr=on:smm=off:ssnc=all:sp=reverse_arity:tha=off_1500");
        fallback.push("lrs+11_8:1_br=off:cond=on:fsr=off:fde=none:gs=on:inw=on:igrpq=1.0:lwlo=on:nwc=1.5:sser=off:ssfp=10000:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=on_300");
        fallback.push("lrs+1011_2:3_fsr=off:gs=on:gsaa=from_current:gsem=on:gsssp=full:nm=0:nwc=5:sas=z3:sscc=on:ssfp=40000:ssfq=1.0:smm=sco:ssnc=none:sp=reverse_arity:tha=off:updr=off_300");
        fallback.push("dis+1010_12_bd=off:gs=on:gsaa=from_current:gsem=on:nm=0:nwc=4:sas=z3:sser=off:ssfp=4000:ssfq=1.2:ssnc=all:sp=occurrence:tha=off_300");
        fallback.push("lrs+1004_5:1_gs=on:gsaa=from_current:gsssp=full:nm=0:nwc=5:sas=z3:ssac=none:sdd=off:sser=off:ssfp=40000:ssfq=1.1:ssnc=all_dependent_600");
        fallback.push("lrs+11_2:1_bd=off:bsr=on:br=off:fsr=off:fde=none:gs=on:gsem=off:nwc=1:sas=z3:sos=all:sdd=off:ssfp=40000:ssfq=1.1:smm=sco:ssnc=all:thf=on:urr=on:updr=off_300");
        fallback.push("dis+4_128_cond=fast:fsr=off:fde=unused:gs=on:gsem=on:inst=on:lcm=predicate:nwc=1:sas=minisat:sdd=large:sser=off:sfr=on:ssfp=40000:ssfq=2.0:ssnc=none:tha=off:updr=off:uhcvi=on_300");
        fallback.push("lrs+4_3:1_bd=off:fsr=off:fde=none:gs=on:gsem=on:lcm=reverse:nwc=2.5:nicw=on:sas=z3:sscc=model:sser=off:sfr=on:ssfp=1000:ssfq=1.1:ssnc=none:sp=reverse_arity:updr=off_300");
        fallback.push("lrs+1010_5:4_bd=off:bs=unit_only:fde=none:gs=on:gsaa=full_model:gsem=on:inw=on:nwc=1.3:sas=z3:sos=all:sfr=on:ssfp=4000:ssfq=1.1:smm=sco:sp=occurrence_300");
        fallback.push("dis+1004_8:1_bd=off:bsr=unit_only:ccuc=first:cond=fast:fde=unused:nm=0:nwc=1.2:sas=minisat:sscc=on:sfr=on:ssfp=1000:ssfq=2.0:ssnc=none:urr=on_300");
        fallback.push("dis+10_1024_cond=fast:fde=none:gs=on:gsem=off:nwc=1:sd=7:ss=axioms:st=5.0:sos=all:spl=off:sp=reverse_arity_300");
        fallback.push("dis+1_1024_bs=on:cond=fast:fde=none:inst=on:nwc=1:spl=off:sp=reverse_arity:tha=off:thf=on:urr=on:uhcvi=on_900");
        fallback.push("lrs-10_2:1_bsr=unit_only:gs=on:gsaa=from_current:lcm=reverse:nwc=1.1:nicw=on:sas=z3:ssac=none:sscc=on:sdd=large:ssfp=10000:ssfq=1.1:smm=sco:sp=occurrence:tha=off:urr=ec_only_900");
        fallback.push("lrs+1010_1_bs=on:bsr=unit_only:ccuc=first:cond=fast:gs=on:gsaa=from_current:inw=on:nwc=1:sas=z3:sos=on:sac=on:sscc=on:sdd=large:ssfp=100000:ssfq=1.4:smm=sco:ssnc=none:sp=reverse_arity:tha=off:thf=on_300");
        fallback.push("lrs+4_32_bsr=unit_only:cond=on:er=filter:fde=unused:gs=on:gsssp=full:inst=on:lcm=predicate:nm=64:nwc=1.1:ss=priority:st=2.0:sos=on:sdd=off:ssfp=10000:ssfq=1.2:smm=sco:sp=occurrence:urr=on:updr=off:uhcvi=on_300");
        fallback.push("ins+11_5_cond=on:gs=on:gsem=off:igbrr=0.3:igpr=on:igrr=1/32:igrp=200:igrpq=2.0:igs=1004:igwr=on:nwc=1:sos=all:spl=off:sp=occurrence:dm=on_300");
        fallback.push("dis+1011_5_fsr=off:gs=on:gsaa=full_model:gsssp=full:nwc=1:sas=z3:sos=on:ssfp=40000:ssfq=2.0:smm=sco:ssnc=all:tha=off:updr=off_300");
        fallback.push("ott-1_5:1_ccuc=first:fsr=off:gs=on:lcm=reverse:nm=64:nwc=1.1:nicw=on:ssac=none:sscc=on:sfr=on:ssfp=10000:ssfq=1.2:smm=sco:ssnc=none:sp=reverse_arity:urr=on_300");
        fallback.push("dis+1010_5:1_fde=none:igrpq=1.0:lwlo=on:nm=0:nwc=1:sas=minisat:sos=on:sdd=off:sfr=on:ssfp=1000:ssfq=1.1:ssnc=none:sp=reverse_arity:tha=off_300");
        fallback.push("ott-11_4_br=off:cond=on:gs=on:gsem=off:gsssp=full:igrpq=1.0:nwc=5:sas=minisat:sac=on:sdd=large:sfr=on:ssfp=4000:ssfq=2.0:ssnc=all:sp=occurrence:urr=on:updr=off_300");
        fallback.push("ott+1010_128_cond=fast:fde=unused:gs=on:gsssp=full:nm=1024:nwc=1.1:sas=z3:sos=on:ssac=none:sscc=model:sdd=large:sser=off:ssfp=4000:ssfq=1.1:ssnc=all_dependent:sp=occurrence:tha=off_300");
        fallback.push("ott+11_2:1_cond=on:gs=on:gsssp=full:lwlo=on:nwc=1:sas=minisat:sos=all:spl=off:sp=occurrence:tha=off_300");
        fallback.push("dis+1003_3:2_bd=off:bsr=unit_only:nwc=1.3:sas=minisat:sac=on:sdd=large:sser=off:sfr=on:ssfp=1000:ssfq=1.2:ssnc=none:updr=off_300");
        fallback.push("lrs+10_40_bd=off:bs=unit_only:bsr=unit_only:ccuc=first:fsr=off:gs=on:gsem=on:lcm=reverse:nwc=3:nicw=on:sas=z3:sac=on:ssac=none:sscc=model:sdd=off:sfr=on:smm=off:ssnc=none:sp=occurrence:tha=off_300");
        fallback.push("lrs+2_8:1_cond=fast:er=filter:fde=unused:igrpq=1.0:lcm=predicate:nwc=2.5:sas=minisat:sdd=off:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=none:sp=occurrence:updr=off_600");
        fallback.push("lrs+1002_3:1_cond=on:fde=unused:inst=on:nm=1024:nwc=2:sas=minisat:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:sp=occurrence:tha=off:updr=off_300");
        fallback.push("lrs+1004_1_cond=fast:fde=unused:gs=on:gsem=off:gsssp=full:lwlo=on:nwc=2.5:sas=minisat:spl=off:tha=off:thf=on:urr=ec_only:uhcvi=on_1500");
        fallback.push("dis+11_1_3600");
        return;
    }
    
    switch (cat) {
        case Property::NEQ:
            if (prop == 131079) {
                quick.push("dis+10_2:3_fde=unused:lcm=predicate:nwc=1:sas=minisat:sos=all:sac=on:sdd=off:sfr=on:ssfp=100000:ssfq=1.0:smm=off:ssnc=none:sp=reverse_arity_12");
                quick.push("dis+11_2:1_cond=fast:fsr=off:fde=unused:gs=on:gsem=off:nwc=1:sas=minisat:sos=on:spl=off:sp=reverse_arity:urr=on_9");
                quick.push("dis+11_5:4_cond=fast:fsr=off:nwc=10:spl=off_5");
                quick.push("dis+11_5_bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=off:nwc=4:sdd=off:ssfp=4000:ssfq=1.4:smm=sco:sp=occurrence_2");
                quick.push("lrs+11_5:4_bd=off:gsp=input_only:gs=on:gsem=on:lcm=predicate:nwc=1:sas=minisat:stl=30:sos=all:spl=off:sp=occurrence:urr=on_5");
                quick.push("ins+11_3_cond=on:igbrr=0.5:igrr=1/16:igrp=4000:igrpq=1.1:igs=1:igwr=on:nwc=4:spl=off:sp=reverse_arity:dm=on_6");
                quick.push("lrs+11_5:4_bd=off:cond=on:fde=unused:nwc=3:stl=30:spl=off:sp=occurrence:updr=off_68");
                quick.push("dis+11_2:3_cond=on:er=known:gs=on:nwc=1.5:sdd=off:sfr=on:ssfp=4000:ssfq=2.0:ssnc=none_272");
                quick.push("lrs+10_8:1_bsr=unit_only:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=off:nwc=1:stl=30:sos=on:spl=off:sp=occurrence:urr=on_1");
                quick.push("ott+1004_5:1_bd=off:bsr=unit_only:cond=fast:fsr=off:nwc=1:sos=all:spl=off_13");
                quick.push("lrs+1011_10_cond=on:gsp=input_only:nwc=1.5:stl=30:spl=off:sp=occurrence:updr=off_195");
                quick.push("dis+11_4_cond=fast:ep=R:gs=on:gsaa=from_current:gsem=on:nwc=1:sas=minisat:ssfp=1000:ssfq=1.4:smm=sco:ssnc=none:sp=occurrence:updr=off_277");
                quick.push("ins+11_5_cond=fast:gsp=input_only:igbrr=0.7:igrr=1/4:igs=1003:igwr=on:lcm=reverse:nwc=1:sos=all:spl=off:urr=ec_only_58");
                quick.push("dis+11_3:2_bs=unit_only:cond=on:fde=unused:lcm=reverse:nwc=1:sos=all:spl=off_178");
                quick.push("dis+11_7_268");
                quick.push("lrs+2_4:1_fsr=off:fde=none:gsp=input_only:lcm=predicate:lwlo=on:nwc=1.2:stl=90:spl=off:sp=occurrence:urr=ec_only:updr=off_444");
                quick.push("dis+11_5_cond=on:gs=on:gsem=on:nwc=1:sos=on:sac=on:sdd=large:ssfp=4000:ssfq=1.1:smm=sco:ssnc=none:sp=occurrence:updr=off_13");
            }
            else if (prop == 3) {
                quick.push("dis+11_5:4_bd=off:cond=on:gs=on:gsssp=full:nwc=1:sas=minisat:sos=on:spl=off:sp=occurrence_3");
                quick.push("ott+1003_3:1_bsr=unit_only:fsr=off:fde=unused:gs=on:gsem=on:nwc=10:sac=on:sdd=large:sfr=on:ssfp=40000:ssfq=1.0:smm=sco:ssnc=none:urr=on_6");
                quick.push("lrs-11_2_bs=unit_only:cond=fast:lcm=predicate:nwc=1:sas=minisat:stl=30:sos=on:spl=off:sp=occurrence:updr=off_1");
                quick.push("dis+1011_2_cond=on:ep=RST:gs=on:gsem=on:nwc=1:sac=on:ssfp=100000:ssfq=1.1:smm=off:ssnc=none:urr=ec_only_7");
                quick.push("dis+11_4_fde=unused:gs=on:gsem=on:gsssp=full:lcm=reverse:lwlo=on:nwc=4:sas=minisat:sdd=off:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=none:sp=reverse_arity_13");
                quick.push("ins+4_3_bsr=unit_only:fde=unused:igrr=1/2:igrp=2000:igrpq=2.0:igs=1002:igwr=on:lcm=predicate:nwc=1:sd=7:ss=axioms:st=1.2:sos=all:spl=off:sp=reverse_arity:dm=on_53");
                quick.push("dis+1011_2:1_cond=fast:gsp=input_only:gs=on:nwc=1:sas=minisat:sos=all:spl=off_46");
                quick.push("lrs+11_2_bd=off:fsr=off:gs=on:gsaa=full_model:gsem=off:gsssp=full:lcm=reverse:nwc=1:sas=minisat:stl=30:sos=on:sdd=large:sfr=on:ssfp=4000:ssfq=2.0:smm=sco:ssnc=none:updr=off_5");
                quick.push("lrs+11_5:4_bsr=unit_only:cond=on:fde=none:gs=on:nwc=1:stl=30:sd=3:ss=axioms:st=3.0:spl=off:sp=reverse_arity_88");
                quick.push("lrs+11_5_cond=fast:er=filter:nwc=1:stl=30:sos=all:spl=off:urr=ec_only_67");
                quick.push("dis+11_5_cond=on:gs=on:gsem=on:nwc=1:sos=on:sac=on:sdd=large:ssfp=4000:ssfq=1.1:smm=sco:ssnc=none:sp=occurrence:updr=off_1");
                quick.push("lrs+1002_3:1_bd=off:bsr=unit_only:fde=none:gs=on:gsem=on:nwc=1:stl=30:sd=1:ss=axioms:spl=off:sp=occurrence_2");
                quick.push("dis+1010_4_bs=unit_only:cond=fast:fsr=off:fde=unused:nwc=1:sos=on:sdd=off:sfr=on:ssfp=10000:ssfq=2.0:sp=reverse_arity:updr=off_40");
                quick.push("dis+11_4_fsr=off:fde=none:gs=on:gsaa=from_current:nwc=1:sfr=on:ssfp=1000:ssfq=2.0:ssnc=none:urr=on:updr=off_2");
                quick.push("dis+1_20_bs=unit_only:fsr=off:gs=on:gsem=on:gsssp=full:nwc=1.7:sas=minisat:spl=off:sp=occurrence_28");
                quick.push("dis+10_3_gs=on:gsem=on:gsssp=full:nwc=1:sas=minisat:sd=3:ss=axioms:sos=all:sdd=off:sfr=on:ssfp=4000:ssfq=1.0:smm=sco:ssnc=none:updr=off_2");
                quick.push("dis+11_5_gs=on:gsem=on:nwc=1:sd=1:ss=axioms:st=3.0:sac=on:sdd=large:ssfp=1000:ssfq=2.0:smm=sco:ssnc=none:sp=occurrence_79");
                quick.push("ins+11_5_ep=RST:fsr=off:fde=none:gs=on:gsem=on:igbrr=0.8:igpr=on:igrr=1/32:igrp=200:igrpq=1.5:igs=1010:igwr=on:nwc=1:sas=minisat:sos=on:spl=off:dm=on_32");
                quick.push("lrs+1003_5_bd=off:bsr=on:cond=on:fsr=off:fde=none:gsp=input_only:lwlo=on:nwc=1:stl=30:sos=all:spl=off:sp=reverse_arity_47");
                quick.push("dis+10_2:3_fde=unused:lcm=predicate:nwc=1:sas=minisat:sos=all:sac=on:sdd=off:sfr=on:ssfp=100000:ssfq=1.0:smm=off:ssnc=none:sp=reverse_arity_63");
                quick.push("lrs+2_4:1_fsr=off:fde=none:gsp=input_only:lcm=predicate:lwlo=on:nwc=1.2:stl=90:spl=off:sp=occurrence:urr=ec_only:updr=off_211");
                quick.push("lrs+1011_10_cond=on:gsp=input_only:nwc=1.5:stl=30:spl=off:sp=occurrence:updr=off_163");
                quick.push("dis+1004_3_fsr=off:fde=none:nwc=1:sas=minisat:sd=1:ss=axioms:st=1.5:sos=all:spl=off:sp=reverse_arity_83");
                quick.push("ins+11_3_cond=on:igbrr=0.5:igrr=1/16:igrp=4000:igrpq=1.1:igs=1:igwr=on:nwc=4:spl=off:sp=reverse_arity:dm=on_96");
                quick.push("dis+10_24_gs=on:nwc=1:sas=minisat:sd=3:ss=axioms:sos=on:spl=off:sp=reverse_arity:updr=off_163");
                quick.push("lrs-11_3:1_bd=off:ccuc=small_ones:cond=fast:gs=on:gsaa=from_current:nwc=1:sas=minisat:stl=30:sos=all:sscc=on:sdd=large:sser=off:ssfp=40000:ssfq=1.0:ssnc=none:sp=reverse_arity:updr=off_17");
            }
            else {
                quick.push("dis+1010_4_bs=unit_only:cond=fast:fsr=off:fde=unused:nwc=1:sos=on:sdd=off:sfr=on:ssfp=10000:ssfq=2.0:sp=reverse_arity:updr=off_11");
                quick.push("dis+11_4_fde=unused:gs=on:gsem=on:gsssp=full:lcm=reverse:lwlo=on:nwc=4:sas=minisat:sdd=off:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=none:sp=reverse_arity_30");
                quick.push("dis+1011_2_bs=unit_only:cond=fast:er=filter:fsr=off:fde=unused:nwc=2.5:ssac=none:ssfp=4000:ssfq=1.0:smm=off:sp=occurrence:updr=off_18");
                quick.push("lrs+1011_8_bd=preordered:cond=on:fsr=off:fde=none:gs=on:gsssp=full:lcm=reverse:nwc=1.7:sas=minisat:stl=30:spl=off:sp=reverse_arity:urr=ec_only_8");
                quick.push("ins+4_3_bsr=unit_only:fde=unused:igrr=1/2:igrp=2000:igrpq=2.0:igs=1002:igwr=on:lcm=predicate:nwc=1:sd=7:ss=axioms:st=1.2:sos=all:spl=off:sp=reverse_arity:dm=on_61");
                quick.push("dis+11_5_gs=on:gsem=on:nwc=1:sd=1:ss=axioms:st=3.0:sac=on:sdd=large:ssfp=1000:ssfq=2.0:smm=sco:ssnc=none:sp=occurrence_2");
                quick.push("lrs+11_5:4_bsr=unit_only:cond=on:fde=none:gs=on:nwc=1:stl=30:sd=3:ss=axioms:st=3.0:spl=off:sp=reverse_arity_1");
                quick.push("ins+11_5_br=off:cond=fast:ep=RS:igbrr=0.9:igrr=1/128:igrp=400:igs=1003:igwr=on:nwc=1:sas=minisat:spl=off:urr=on:dm=on_7");
                quick.push("ott+1011_2_er=known:fde=none:nwc=1:spl=off:sp=occurrence_141");
                quick.push("lrs+11_2_bd=off:fsr=off:gs=on:gsaa=full_model:gsem=off:gsssp=full:lcm=reverse:nwc=1:sas=minisat:stl=30:sos=on:sdd=large:sfr=on:ssfp=4000:ssfq=2.0:smm=sco:ssnc=none:updr=off_26");
                quick.push("dis+1011_2_cond=on:ep=RST:gs=on:gsem=on:nwc=1:sac=on:ssfp=100000:ssfq=1.1:smm=off:ssnc=none:urr=ec_only_5");
                quick.push("dis+11_5_cond=on:gs=on:gsem=on:nwc=1:sos=on:sac=on:sdd=large:ssfp=4000:ssfq=1.1:smm=sco:ssnc=none:sp=occurrence:updr=off_1");
                quick.push("lrs+2_4:1_fsr=off:fde=none:gsp=input_only:lcm=predicate:lwlo=on:nwc=1.2:stl=90:spl=off:sp=occurrence:urr=ec_only:updr=off_233");
                quick.push("dis+11_3:2_bs=unit_only:cond=on:fde=unused:lcm=reverse:nwc=1:sos=all:spl=off_268");
                quick.push("lrs+1010_10_bd=off:fsr=off:fde=none:nwc=4:sas=minisat:stl=30:ssac=none:sdd=off:sser=off:ssfp=4000:ssfq=1.4:sp=occurrence:urr=ec_only:updr=off_294");
                quick.push("lrs+1011_128_bsr=unit_only:cond=fast:lwlo=on:nwc=2:stl=30:sos=all:spl=off:urr=on:updr=off_50");
                quick.push("lrs+11_2:1_bs=unit_only:bsr=unit_only:fsr=off:fde=none:gsp=input_only:lcm=reverse:lwlo=on:nwc=1:stl=60:sos=on:spl=off:urr=ec_only_208");
                quick.push("lrs+11_5:4_bd=off:cond=on:fde=unused:nwc=3:stl=30:spl=off:sp=occurrence:updr=off_188");
                quick.push("lrs+1011_10_cond=on:gsp=input_only:nwc=1.5:stl=30:spl=off:sp=occurrence:updr=off_213");
                quick.push("dis+1010_6_bd=off:bsr=unit_only:ccuc=first:cond=fast:fsr=off:fde=unused:lwlo=on:nwc=1:sas=minisat:sos=on:sac=on:sscc=model:sdd=large:sser=off:ssfp=1000:ssfq=1.1:ssnc=all_dependent_130");
                quick.push("dis+11_7_182");
                quick.push("dis+10_2:3_fde=unused:lcm=predicate:nwc=1:sas=minisat:sos=all:sac=on:sdd=off:sfr=on:ssfp=100000:ssfq=1.0:smm=off:ssnc=none:sp=reverse_arity_221");
            }
            break;
            
        case Property::HEQ:
            quick.push("lrs+11_1_bd=off:bsr=unit_only:fsr=off:fde=unused:gs=on:gsaa=full_model:gsem=off:gsssp=full:lwlo=on:nwc=1:sas=minisat:stl=30:ssfp=10000:ssfq=1.1:smm=off:ssnc=none:sp=occurrence:updr=off_20");
            quick.push("lrs+11_2:3_cond=on:gs=on:gsem=on:lwlo=on:nwc=1.7:sas=minisat:stl=30:spl=off:updr=off_123");
            quick.push("ott+11_24_bd=off:bsr=unit_only:fsr=off:gs=on:gsaa=full_model:gsem=off:gsssp=full:nwc=3:sdd=off:sfr=on:ssfp=4000:ssfq=1.1:ssnc=none:sp=occurrence_2");
            quick.push("dis+1011_5_cond=fast:fsr=off:gs=on:gsaa=full_model:nwc=1:sas=minisat:sos=all:sdd=off:ssfp=4000:ssfq=1.2:smm=off:ssnc=none:sp=occurrence:urr=ec_only:updr=off_1");
            quick.push("dis+1010_24_cond=fast:ep=RS:fde=unused:lwlo=on:nwc=1.5:sas=minisat:sser=off:sfr=on:ssfp=1000:ssfq=1.1:ssnc=none_2");
            quick.push("ins+11_4_cond=fast:fsr=off:igbrr=0.8:igpr=on:igrr=1/8:igrp=200:igrpq=1.5:igs=1003:igwr=on:nwc=10:spl=off:sp=occurrence:updr=off_304");
            quick.push("lrs+11_3:1_bd=off:fde=none:gs=on:lwlo=on:nwc=2:sas=minisat:stl=90:sac=on:sdd=off:sfr=on:ssfp=4000:ssfq=1.4:smm=sco:ssnc=none:sp=occurrence_64");
            quick.push("lrs+10_5_bd=preordered:cond=on:fde=none:lcm=reverse:lwlo=on:nwc=1.7:stl=30:spl=off:sp=occurrence_9");
            quick.push("ins+10_4_cond=on:fsr=off:fde=none:igbrr=0.6:igrr=1/32:igrp=2000:igrpq=1.05:igs=1002:igwr=on:nwc=5:spl=off:sp=occurrence:updr=off:dm=on_175");
            quick.push("lrs+11_10_gs=on:gsem=on:lcm=reverse:nwc=1:stl=30:sac=on:sfr=on:ssfp=10000:ssfq=1.0:ssnc=none:updr=off_132");
            quick.push("dis+11_5:4_fsr=off:fde=none:gs=on:gsem=off:nwc=1:sac=on:sdd=off:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=none:urr=on_169");
            quick.push("lrs+11_1024_bd=off:fsr=off:gs=on:gsem=on:nwc=1:stl=30:spl=off:sp=occurrence:urr=on_223");
            quick.push("ott+11_5:4_cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=off:nwc=1:sos=all:sdd=large:sfr=on:ssfp=10000:ssfq=2.0:ssnc=none:sp=occurrence:updr=off_195");
            quick.push("dis+11_7_259");
            break;
            
        case Property::PEQ:
            if (prop == 1) {
                quick.push("lrs+11_3_bsr=unit_only:er=known:fsr=off:fde=none:gs=on:gsem=off:gsssp=full:nwc=1.3:sas=minisat:stl=30:sdd=large:smm=sco:ssnc=none_1");
                quick.push("dis+11_7_9");
                quick.push("lrs+10_10_er=known:fde=none:gs=on:gsem=on:nwc=1.7:stl=30:spl=off:updr=off_5");
                quick.push("lrs+11_5:4_bsr=unit_only:ccuc=small_ones:cond=on:fsr=off:nwc=1:sas=minisat:stl=30:sac=on:sscc=on:sdd=off:ssfp=40000:ssfq=2.0:ssnc=none:sp=reverse_arity_3");
                quick.push("dis+1002_3_bsr=unit_only:cond=on:nwc=1.2:nicw=on:sos=all:sdd=large:sser=off:sp=occurrence:updr=off_11");
                quick.push("dis+10_4_bsr=unit_only:gs=on:gsssp=full:nwc=1.5:nicw=on:sas=minisat:sfr=on:ssfp=4000:ssfq=1.2:smm=off:sp=reverse_arity:updr=off_25");
                quick.push("lrs+1011_3_cond=on:fsr=off:fde=none:gs=on:gsssp=full:nwc=1:stl=30:sos=all:spl=off:sp=reverse_arity:updr=off_53");
                quick.push("lrs+10_3:1_bs=on:bsr=unit_only:gs=on:gsem=off:gsssp=full:lwlo=on:nwc=1:sas=minisat:stl=240:spl=off:sp=reverse_arity:updr=off_354");
                quick.push("lrs+11_128_bs=unit_only:fde=unused:gs=on:gsem=off:gsssp=full:nwc=1:nicw=on:sas=minisat:stl=120:sos=on:sac=on:ssac=none:sdd=large:sfr=on:ssfp=40000:ssfq=1.1:smm=sco:ssnc=all_799");
            }
            else if (prop == 131073) {
                quick.push("lrs+10_3:1_bs=on:bsr=unit_only:gs=on:gsem=off:gsssp=full:lwlo=on:nwc=1:sas=minisat:stl=240:spl=off:sp=reverse_arity:updr=off_2277");
            }
            else {
                quick.push("lrs+11_14_bs=unit_only:bsr=unit_only:cond=on:nwc=1:sas=minisat:stl=30:sdd=off:sser=off:ssfp=1000:ssfq=1.1:ssnc=none:sp=occurrence_18");
                quick.push("lrs+11_2_ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:gsssp=full:lwlo=on:nwc=1:nicw=on:sas=minisat:stl=60:sac=on:sscc=model:sdd=off:ssfp=100000:ssfq=1.2:smm=off:ssnc=all_dependent:sp=reverse_arity:updr=off_96");
                quick.push("lrs+2_7_bs=unit_only:bsr=unit_only:cond=on:fsr=off:gs=on:nwc=1.7:sas=minisat:stl=30:sos=on:sac=on:sfr=on:ssfp=100000:ssfq=1.0:smm=off:ssnc=all_dependent_49");
                quick.push("dis+11_5_fsr=off:gs=on:gsem=off:lwlo=on:nwc=1:sos=all:spl=off:sp=reverse_arity_24");
                quick.push("dis+1002_3_bsr=unit_only:cond=on:nwc=1.2:nicw=on:sos=all:sdd=large:sser=off:sp=occurrence:updr=off_49");
                quick.push("dis+11_64_bs=unit_only:cond=on:fde=none:nwc=2:spl=off:updr=off_162");
                quick.push("lrs-1_3_fsr=off:gs=on:gsaa=from_current:gsem=on:lwlo=on:nwc=1.2:sas=minisat:stl=30:sac=on:sdd=off:sfr=on:ssfp=4000:ssfq=2.0:smm=sco:ssnc=none:sp=reverse_arity_131");
                quick.push("dis+10_4_bsr=unit_only:gs=on:gsssp=full:nwc=1.5:nicw=on:sas=minisat:sfr=on:ssfp=4000:ssfq=1.2:smm=off:sp=reverse_arity:updr=off_114");
                quick.push("dis+1_64_bs=unit_only:cond=fast:fde=none:gs=on:gsaa=from_current:gsem=off:nwc=3:nicw=on:sas=minisat:sos=on:sac=on:sdd=large:sfr=on:ssfp=40000:ssfq=1.4:smm=off:ssnc=all_dependent:sp=reverse_arity:updr=off_441");
                quick.push("lrs+11_4_bs=unit_only:cond=fast:fde=none:gs=on:lwlo=on:nwc=1:stl=30:ssfp=1000:ssfq=1.2:ssnc=none:sp=occurrence_262");
                quick.push("ott+10_8_bsr=unit_only:gs=on:gsaa=from_current:gsem=on:nwc=4:sas=minisat:sfr=on:ssfp=4000:ssfq=1.4:smm=off:ssnc=all_536");
                quick.push("lrs+11_128_bs=unit_only:fde=unused:gs=on:gsem=off:gsssp=full:nwc=1:nicw=on:sas=minisat:stl=120:sos=on:sac=on:ssac=none:sdd=large:sfr=on:ssfp=40000:ssfq=1.1:smm=sco:ssnc=all_691");
            }
            break;
            
        case Property::HNE:
            quick.push("dis+1002_5_gs=on:gsem=off:gsssp=full:lwlo=on:nwc=1:sas=minisat:sos=on:sac=on:sdd=large:sfr=on:ssfp=100000:ssfq=1.0:ssnc=none:sp=reverse_arity_1");
            quick.push("lrs+2_50_bs=unit_only:bsr=unit_only:cond=fast:fsr=off:nwc=1:stl=30:spl=off:sp=occurrence_84");
            quick.push("dis+1_64_gsp=input_only:nwc=1.2:sos=all:spl=off:sp=occurrence:updr=off_34");
            quick.push("dis+1_40_bs=unit_only:fsr=off:nwc=1:sas=minisat:sdd=large:ssfp=1000:ssfq=1.1:smm=sco:ssnc=none:sp=reverse_arity:updr=off_110");
            quick.push("lrs+11_3_fsr=off:gs=on:gsssp=full:nwc=2:stl=60:spl=off:sp=occurrence:urr=on:updr=off_35");
            quick.push("lrs+11_1_bs=on:nwc=1.1:stl=30:spl=off:sp=occurrence:urr=ec_only:updr=off_128");
            quick.push("dis+11_2_cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:nwc=5:sac=on:ssac=none:sfr=on:ssfp=4000:ssfq=1.4:smm=off:ssnc=none:sp=reverse_arity_68");
            quick.push("lrs+11_1_bsr=unit_only:cond=on:fsr=off:gs=on:gsem=on:lwlo=on:nwc=2:sas=minisat:stl=90:spl=off_888");
            quick.push("dis+11_8:1_br=off:cond=fast:fsr=off:nwc=1:sos=all:sdd=off:sser=off:sfr=on:ssfp=40000:ssfq=1.1:ssnc=none:sp=occurrence:urr=on:updr=off_223");
            quick.push("dis+1_3_cond=on:fsr=off:nwc=1.1:sas=minisat:spl=off:sp=reverse_arity:urr=ec_only:updr=off_155");
            break;
            
        case Property::NNE:
            quick.push("lrs+11_3_cond=on:fsr=off:lcm=reverse:nwc=1:sas=minisat:stl=30:sos=all:sdd=off:sser=off:sfr=on:ssfp=1000:ssfq=1.4:ssnc=none:sp=occurrence_2");
            quick.push("lrs+10_4_cond=fast:nwc=1:nicw=on:sas=minisat:stl=60:sfr=on:ssfp=10000:ssfq=1.2:smm=off_47");
            quick.push("dis+1003_50_cond=fast:nwc=1:sos=on:spl=off:sp=occurrence_89");
            quick.push("dis+11_64_fsr=off:gsp=input_only:nwc=1.1:sos=all:spl=off:sp=occurrence:updr=off_259");
            quick.push("dis+3_64_cond=fast:lcm=reverse:nwc=1.1:sos=on:spl=off:updr=off_62");
            quick.push("dis+1011_2_nwc=1:sas=minisat:sos=on:spl=off:sp=occurrence_204");
            quick.push("dis+1002_10_bsr=unit_only:cond=fast:nwc=1:sos=all:spl=off:sp=occurrence_136");
            quick.push("dis+11_7_198");
            quick.push("dis-2_5_cond=on:nwc=1:sas=minisat:spl=off:sp=occurrence_228");
            quick.push("lrs+1004_28_nwc=1.1:stl=60:sos=all:spl=off_495");
            break;
            
        case Property::FEQ:
            if (atoms > 1000000) {
                quick.push("dis+11_4_bsr=unit_only:cond=fast:fde=none:lwlo=on:nm=0:nwc=1.2:spl=off:sp=occurrence_1218");
                quick.push("lrs+1011_4_cond=fast:gs=on:gsaa=from_current:gsem=off:gsssp=full:nwc=1:stl=90:sd=5:ss=axioms:st=3.0:sac=on:sdd=off:sser=off:sfr=on:ssfp=1000:ssfq=1.0:ssnc=none_693");
            }
            else if (atoms > 200000) {
                quick.push("lrs+1002_3_ep=RST:er=known:fsr=off:gs=on:gsaa=from_current:nwc=1:sas=minisat:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sfr=on:ssfp=100000:ssfq=1.4:smm=sco:ssnc=none:sp=occurrence_51");
                quick.push("lrs+1002_2:3_bsr=unit_only:er=known:fde=none:gs=on:gsem=on:nwc=1:sas=minisat:stl=30:sd=1:ss=axioms:st=1.5:sdd=large:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=none:sp=reverse_arity_45");
                quick.push("dis-2_4_cond=fast:ep=RST:er=filter:fde=unused:gs=on:gsem=on:lcm=reverse:nwc=1:sd=3:ss=axioms:sos=on:spl=off:updr=off_35");
                quick.push("dis-3_10_bsr=unit_only:er=filter:fde=unused:lcm=predicate:nm=64:nwc=1:spl=off:sp=occurrence:updr=off_187");
                quick.push("ins+11_3_cond=fast:fde=none:igbrr=0.8:igrr=1/16:igrp=200:igrpq=1.05:igs=1003:igwr=on:nm=64:nwc=1:sas=minisat:sd=2:ss=axioms:st=3.0:sos=on:spl=off:updr=off_46");
                quick.push("dis+2_5:4_fde=none:nwc=1:sd=2:ss=axioms:sos=on:ssfp=40000:ssfq=2.0_27");
                quick.push("dis+11_4_cond=fast:fsr=off:gs=on:gsaa=from_current:gsem=on:nwc=1:sas=minisat:sd=10:ss=axioms:st=5.0:sos=all:sser=off:ssfp=4000:ssfq=1.0:ssnc=none:sp=occurrence_55");
                quick.push("lrs+1010_4:1_cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=0:nwc=1:sas=minisat:stl=30:sd=2:ss=axioms:st=1.5:sos=on:sac=on:sdd=off:sser=off:sfr=on:ssfp=100000:ssfq=1.4:ssnc=none:sp=occurrence_21");
                quick.push("dis+11_5_fde=none:gs=on:gsaa=from_current:gsssp=full:lcm=reverse:nwc=1:sas=minisat:ss=axioms:st=1.5:sos=on:ssfp=4000:ssfq=1.2:smm=sco:ssnc=none_124");
                quick.push("lrs-4_4_cond=fast:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=off:gsssp=full:lcm=reverse:nwc=1:sas=minisat:stl=30:sd=4:ss=axioms:sos=on:sac=on:ssac=none:sdd=large:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:sp=reverse_arity_43");
                quick.push("ott+11_8:1_cond=fast:gs=on:gsem=off:nwc=1:nicw=on:sd=2:ss=axioms:st=1.2:sos=all:sscc=on:sfr=on:ssfp=100000:ssfq=1.0:smm=sco:ssnc=none:urr=on_47");
                quick.push("ott+1011_10_cond=fast:fde=none:gsp=input_only:gs=on:gsssp=full:nwc=1:sas=minisat:sd=3:ss=axioms:sos=all:spl=off:sp=occurrence:updr=off_124");
                quick.push("lrs+1004_2:1_cond=fast:fde=none:gs=on:gsem=off:nwc=1:stl=30:sd=2:ss=axioms:sos=on:spl=off:sp=reverse_arity:updr=off_45");
                quick.push("ins+11_4_cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:gsem=on:igbrr=0.3:igpr=on:igrr=1/8:igrp=100:igrpq=1.5:igwr=on:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:spl=off:dm=on_66");
                quick.push("lrs+4_2:1_ep=R:fde=unused:gs=on:nwc=1:stl=30:sos=all:sac=on:ssac=none:sser=off:sfr=on:ssfp=10000:ssfq=1.2:ssnc=none:sp=occurrence:updr=off_281");
                quick.push("lrs-2_5_cond=on:fde=none:lcm=predicate:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=on:sdd=off:ssfp=100000:ssfq=1.4:ssnc=none_98");
                quick.push("dis+4_3:1_gs=on:nwc=1:sd=1:ss=axioms:sos=all:spl=off:updr=off_51");
                quick.push("dis+11_2_fde=none:gsp=input_only:gs=on:gsem=on:nwc=1:sd=2:ss=axioms:st=1.2:sos=all:spl=off:sp=reverse_arity:urr=on:updr=off_197");
                quick.push("lrs-1_2:1_bd=preordered:bsr=on:br=off:cond=on:gs=on:lcm=reverse:nwc=1:stl=30:sd=2:ss=axioms:sos=on:sdd=large:sser=off:ssfp=100000:ssfq=2.0:ssnc=none:sp=occurrence:urr=on:updr=off_135");
                quick.push("ott+11_24_cond=fast:ep=RST:fsr=off:fde=none:gs=on:lcm=predicate:nm=64:nwc=1:sas=minisat:ss=axioms:st=5.0:sos=all:spl=off:sp=occurrence_282");
                quick.push("lrs+1_3:1_cond=fast:gsp=input_only:gs=on:gsaa=from_current:gsem=off:nwc=1:stl=30:sd=2:ss=axioms:st=1.2:sos=on:sac=on:sdd=off:sfr=on:ssfp=100000:ssfq=1.2:smm=sco:ssnc=none:sp=reverse_arity_190");
                quick.push("dis+1003_8:1_bd=off:bs=unit_only:cond=fast:fsr=off:fde=none:gsp=input_only:lcm=reverse:nwc=1:sas=minisat:sos=all:ssac=none:sscc=on:sdd=off:sfr=on:smm=sco:ssnc=none:sp=reverse_arity_150");
                quick.push("lrs+11_3:2_cond=fast:fsr=off:fde=none:gs=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:st=2.0:spl=off:urr=on_227");
            }
            else if (prop == 0) {
                if (atoms >= 1000) {
                    quick.push("dis+11_7_41");
                    quick.push("dis+11_1024_br=off:ep=RSTC:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=off:nwc=1:sac=on:ssfp=40000:ssfq=1.0:ssnc=none:sp=reverse_arity:urr=on_172");
                    quick.push("ott+2_8_bsr=unit_only:cond=fast:fde=none:gs=on:lwlo=on:nwc=1:sas=minisat:spl=off_293");
                    quick.push("dis+4_64_bs=unit_only:cond=on:er=known:fde=unused:gs=on:gsem=off:nwc=1.2:sas=minisat:ssac=none:sser=off:sfr=on:ssfp=10000:ssfq=2.0:ssnc=all:sp=reverse_arity:updr=off_281");
                    quick.push("lrs+3_5_bd=preordered:bsr=unit_only:gsp=input_only:gs=on:gsem=on:gsssp=full:lwlo=on:nm=64:nwc=1:sas=minisat:stl=90:spl=off:sp=occurrence:urr=ec_only:updr=off_778");
                    quick.push("dis+11_4_bsr=unit_only:cond=fast:fde=none:lwlo=on:nm=0:nwc=1.2:spl=off:sp=occurrence_926");
                }
                else {
                    quick.push("dis+11_7_3");
                    quick.push("lrs-11_2_cond=on:fde=unused:gs=on:nwc=3:stl=30:sdd=off:sfr=on:ssfp=100000:ssfq=1.4:smm=sco:ssnc=all_4");
                    quick.push("lrs+11_2_br=off:cond=on:fde=none:gs=on:gsaa=full_model:lwlo=on:nwc=2:sas=minisat:stl=30:ssfp=100000:ssfq=1.4:smm=sco:ssnc=none:sp=occurrence:urr=on_98");
                    quick.push("dis+11_5_fde=none:nwc=1:sas=minisat:sd=1:ss=axioms:st=5.0:sos=all:sdd=large:sser=off:sfr=on:ssfp=100000:ssfq=2.0:ssnc=none_37");
                    quick.push("lrs+1002_2:3_br=off:fde=unused:gs=on:gsaa=from_current:gsem=on:gsssp=full:nwc=1:sas=minisat:stl=30:sac=on:sser=off:sfr=on:ssfp=100000:ssfq=2.0:ssnc=none:sp=reverse_arity:urr=on_4");
                    quick.push("lrs+1011_12_bs=on:bsr=unit_only:cond=on:gs=on:gsaa=from_current:gsssp=full:nwc=1.1:sas=minisat:stl=60:sos=all:sac=on:sdd=off:sser=off:sfr=on:ssfp=100000:ssfq=1.2:ssnc=none:sp=reverse_arity:updr=off_14");
                    quick.push("lrs+10_8:1_bd=preordered:bs=on:ccuc=first:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=on:gsssp=full:nwc=1:nicw=on:sas=minisat:stl=120:sos=on:sscc=on:sser=off:sfr=on:ssfp=4000:ssfq=1.0:ssnc=none:sp=reverse_arity:urr=on_7");
                    quick.push("lrs+1_5:4_cond=on:fsr=off:fde=none:gs=on:gsem=on:lwlo=on:nm=64:nwc=1:stl=60:sos=all:spl=off_80");
                    quick.push("lrs+11_28_cond=on:gs=on:gsaa=from_current:gsem=on:gsssp=full:lwlo=on:nm=64:nwc=1.7:stl=30:sac=on:sdd=off:sfr=on:ssfp=40000:ssfq=1.1:smm=off:ssnc=none:urr=on:updr=off_109");
                    quick.push("ott+11_3:1_br=off:gs=on:gsem=on:nwc=1:sas=minisat:sos=all:spl=off:urr=on:updr=off_135");
                    quick.push("lrs+3_5_bd=preordered:bsr=unit_only:gsp=input_only:gs=on:gsem=on:gsssp=full:lwlo=on:nm=64:nwc=1:sas=minisat:stl=90:spl=off:sp=occurrence:urr=ec_only:updr=off_815");
                    quick.push("lrs+1011_4_cond=fast:gs=on:gsaa=from_current:gsem=off:gsssp=full:nwc=1:stl=90:sd=5:ss=axioms:st=3.0:sac=on:sdd=off:sser=off:sfr=on:ssfp=1000:ssfq=1.0:ssnc=none_402");
                }
            }
            else if (prop == 1) {
                if (atoms > 80) {
                    quick.push("lrs+11_1_br=off:cond=on:er=known:fsr=off:fde=unused:nwc=1:stl=30:sac=on:sdd=off:sfr=on:ssfp=40000:ssfq=1.0:smm=off:ssnc=none:sp=occurrence:urr=on_11");
                    quick.push("ott+1002_5_bsr=on:fsr=off:fde=none:gs=on:gsem=off:lwlo=on:nwc=1:sscc=on:sser=off:ssfp=100000:ssfq=1.1:sp=occurrence_3");
                    quick.push("lrs+1011_3:1_bsr=unit_only:cond=fast:er=known:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=off:nwc=1:sas=minisat:stl=30:sdd=large:sser=off:sfr=on:ssfp=100000:ssfq=2.0:updr=off_5");
                    quick.push("ins+11_3_cond=on:fde=none:gs=on:gsem=off:gsssp=full:igbrr=1.0:igrr=1/16:igrp=100:igrpq=1.05:igs=1:igwr=on:nwc=1:sas=minisat:sos=on:spl=off:sp=occurrence:urr=on_4");
                    quick.push("ott-1_2:3_bs=unit_only:bsr=unit_only:fde=none:gs=on:gsem=on:gsssp=full:nwc=1:sas=minisat:sos=on:sdd=large:sfr=on:ssfp=1000:ssfq=1.4:smm=off:ssnc=all:sp=occurrence_58");
                    quick.push("dis+1011_4_fde=none:gs=on:nwc=1:sos=on:sdd=off:ssfp=10000:ssfq=1.4:smm=sco:ssnc=none:sp=reverse_arity:updr=off_67");
                    quick.push("dis+11_4_cond=fast:fsr=off:fde=none:gs=on:gsssp=full:nwc=1:sas=minisat:ss=axioms:st=2.0:sos=all:sdd=large:sfr=on:ssfp=1000:ssfq=2.0:smm=sco:ssnc=none:updr=off_86");
                    quick.push("dis+1002_4_cond=fast:fde=unused:gsp=input_only:gs=on:gsem=on:nm=64:nwc=1:sas=minisat:sos=on:sscc=model:sser=off:sfr=on:ssfp=4000:ssfq=1.4:ssnc=none:updr=off_6");
                    quick.push("lrs+1010_4_fde=unused:gs=on:gsem=off:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on:sac=on:ssfp=40000:ssfq=1.2:smm=sco:ssnc=none:sp=reverse_arity:urr=on:updr=off_3");
                    quick.push("ott+2_8_bsr=unit_only:cond=fast:fde=none:gs=on:lwlo=on:nwc=1:sas=minisat:spl=off_278");
                    quick.push("lrs+1002_3_bd=off:bs=on:bsr=unit_only:cond=fast:fsr=off:lcm=predicate:nwc=1.5:stl=30:sos=on:sdd=off:sser=off:sfr=on:sp=reverse_arity_32");
                    quick.push("ott+11_5_nwc=1:sd=7:ss=axioms:st=2.0:sac=on:sfr=on:ssfp=40000:ssfq=1.2:ssnc=none_380");
                    quick.push("lrs+10_8_br=off:fsr=off:gsp=input_only:gs=on:gsem=off:nwc=1:sas=minisat:stl=30:spl=off:sp=reverse_arity:urr=on:updr=off_118");
                    quick.push("lrs+3_5_bd=preordered:bsr=unit_only:gsp=input_only:gs=on:gsem=on:gsssp=full:lwlo=on:nm=64:nwc=1:sas=minisat:stl=90:spl=off:sp=occurrence:urr=ec_only:updr=off_394");
                    quick.push("lrs+3_4:1_bs=unit_only:bsr=on:cond=on:er=known:fde=none:lcm=predicate:lwlo=on:nwc=1.5:sas=minisat:stl=210:sos=all:sfr=on:ssfp=100000:ssfq=1.1:smm=sco:ssnc=all_dependent:sp=occurrence:updr=off_1497");
                }
                else {
                    quick.push("lrs+10_50_bd=off:bs=unit_only:bsr=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:nwc=1.3:nicw=on:stl=30:sos=all:sdd=off:sser=off:sfr=on:ssfp=10000:ssfq=2.0:ssnc=none:sp=occurrence_4");
                    quick.push("dis+1003_8:1_bd=off:bs=unit_only:cond=fast:fsr=off:fde=none:gsp=input_only:lcm=reverse:nwc=1:sas=minisat:sos=all:ssac=none:sscc=on:sdd=off:sfr=on:smm=sco:ssnc=none:sp=reverse_arity_2");
                    quick.push("dis+11_7_297");
                    quick.push("ott+1004_28_cond=fast:nwc=1:sos=all:spl=off:updr=off_109");
                    quick.push("lrs+10_14_cond=on:gs=on:gsem=off:nwc=1.5:nicw=on:sas=minisat:stl=30:sac=on:sfr=on:ssfp=4000:ssfq=1.2:ssnc=all:sp=reverse_arity:updr=off_159");
                    quick.push("lrs+11_1_br=off:cond=on:er=known:fsr=off:fde=unused:nwc=1:stl=30:sac=on:sdd=off:sfr=on:ssfp=40000:ssfq=1.0:smm=off:ssnc=none:sp=occurrence:urr=on_78");
                    quick.push("ott+1011_1024_bd=preordered:bs=on:cond=on:nwc=1:spl=off:updr=off_173");
                    quick.push("dis+4_64_bs=unit_only:cond=on:er=known:fde=unused:gs=on:gsem=off:nwc=1.2:sas=minisat:ssac=none:sser=off:sfr=on:ssfp=10000:ssfq=2.0:ssnc=all:sp=reverse_arity:updr=off_174");
                    quick.push("lrs-1_4_cond=fast:ep=RST:fde=unused:gs=on:gsem=on:gsssp=full:lwlo=on:nwc=1:sas=minisat:stl=30:spl=off:urr=ec_only_259");
                    quick.push("lrs+3_4:1_bs=unit_only:bsr=on:cond=on:er=known:fde=none:lcm=predicate:lwlo=on:nwc=1.5:sas=minisat:stl=210:sos=all:sfr=on:ssfp=100000:ssfq=1.1:smm=sco:ssnc=all_dependent:sp=occurrence:updr=off_1609");
                }
            }
            else if (prop == 2) {
                if (atoms <= 17) {
                    quick.push("ott+10_8_bs=on:bsr=unit_only:cond=fast:fde=none:gs=on:gsaa=full_model:gsem=off:gsssp=full:lcm=reverse:nwc=1.3:sas=minisat:sac=on:sdd=off:sser=off:ssfp=4000:ssfq=1.0:ssnc=all_dependent:sp=reverse_arity_3");
                    quick.push("ott+1010_40_bs=unit_only:cond=fast:nwc=1:sas=minisat:sdd=off:ssfp=10000:ssfq=2.0:smm=sco:ssnc=none:sp=reverse_arity:updr=off_185");
                    quick.push("lrs+1002_6_ccuc=first:cond=on:fsr=off:nwc=4:nicw=on:sas=minisat:stl=30:sscc=on:sfr=on:ssfp=40000:ssfq=1.0:smm=sco:ssnc=all_dependent:sp=reverse_arity:urr=ec_only_122");
                    quick.push("lrs+1011_4_cond=fast:gs=on:gsaa=from_current:gsem=off:gsssp=full:nwc=1:stl=90:sd=5:ss=axioms:st=3.0:sac=on:sdd=off:sser=off:sfr=on:ssfp=1000:ssfq=1.0:ssnc=none_864");
                    quick.push("dis+1011_24_cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=64:nwc=1:sos=on:spl=off:sp=occurrence_129");
                    quick.push("dis+11_8_bs=unit_only:nwc=1:sd=10:ss=axioms:st=1.5:spl=off:sp=occurrence:updr=off_238");
                    quick.push("lrs+1011_12_bs=on:bsr=unit_only:cond=on:gs=on:gsaa=from_current:gsssp=full:nwc=1.1:sas=minisat:stl=60:sos=all:sac=on:sdd=off:sser=off:sfr=on:ssfp=100000:ssfq=1.2:ssnc=none:sp=reverse_arity:updr=off_548");
                }
                else {
                    quick.push("dis+1002_3_cond=fast:fsr=off:nwc=2.5:sd=3:ss=axioms:st=1.5:spl=off:updr=off_5");
                    quick.push("lrs+4_64_fsr=off:nwc=1.5:sas=minisat:stl=30:spl=off:sp=occurrence_15");
                    quick.push("lrs+10_14_cond=on:gs=on:gsem=off:nwc=1.5:nicw=on:sas=minisat:stl=30:sac=on:sfr=on:ssfp=4000:ssfq=1.2:ssnc=all:sp=reverse_arity:updr=off_7");
                    quick.push("ott+11_5_nwc=1:sd=7:ss=axioms:st=2.0:sac=on:sfr=on:ssfp=40000:ssfq=1.2:ssnc=none_117");
                    quick.push("ott+10_8_bs=on:bsr=unit_only:cond=fast:fde=none:gs=on:gsaa=full_model:gsem=off:gsssp=full:lcm=reverse:nwc=1.3:sas=minisat:sac=on:sdd=off:sser=off:ssfp=4000:ssfq=1.0:ssnc=all_dependent:sp=reverse_arity_14");
                    quick.push("lrs+11_28_cond=on:gs=on:gsaa=from_current:gsem=on:gsssp=full:lwlo=on:nm=64:nwc=1.7:stl=30:sac=on:sdd=off:sfr=on:ssfp=40000:ssfq=1.1:smm=off:ssnc=none:urr=on:updr=off_106");
                    quick.push("lrs+10_5:4_bsr=unit_only:fde=none:lcm=reverse:nm=64:nwc=10:stl=30:spl=off:sp=occurrence:updr=off_26");
                    quick.push("dis+11_20_fsr=off:fde=unused:gs=on:gsssp=full:nm=0:nwc=1.3:nicw=on:sdd=large:sfr=on:ssfp=4000:ssfq=1.0:smm=off:ssnc=all:sp=reverse_arity_162");
                    quick.push("ott+11_14_bd=preordered:fsr=off:gs=on:gsem=off:nwc=2:ssfp=4000:ssfq=1.2:smm=off:ssnc=none:sp=reverse_arity:updr=off_214");
                    quick.push("ott+4_8_bsr=unit_only:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:nwc=1:sos=all:sac=on:ssfp=100000:ssfq=1.1:smm=off:ssnc=none:sp=reverse_arity_161");
                    quick.push("lrs+4_5_cond=fast:fsr=off:fde=none:gs=on:gsaa=from_current:nwc=1:stl=90:sd=5:ss=axioms:st=1.2:sac=on:sdd=off:sser=off:sfr=on:ssfp=4000:ssfq=2.0:ssnc=none:sp=occurrence_341");
                    quick.push("ott+1010_40_bs=unit_only:cond=fast:nwc=1:sas=minisat:sdd=off:ssfp=10000:ssfq=2.0:smm=sco:ssnc=none:sp=reverse_arity:updr=off_383");
                    quick.push("ott+11_20_bs=unit_only:fsr=off:gsp=input_only:gs=on:gsaa=full_model:gsem=off:gsssp=full:nwc=1:sac=on:ssfp=1000:ssfq=2.0:ssnc=none:sp=occurrence_538");
                    quick.push("lrs+1002_7_ccuc=first:cond=on:fde=none:gs=on:gsssp=full:nwc=1:sas=minisat:stl=90:sd=3:ss=axioms:sscc=model:sser=off:ssfp=1000:ssfq=2.0:ssnc=none:sp=reverse_arity_542");
                }
            }
            else if (prop == 131073) {
                if (atoms > 300) {
                    quick.push("dis+11_5_bd=off:cond=fast:fde=unused:gs=on:gsem=on:lwlo=on:nwc=1:sos=on:sac=on:sdd=off:sser=off:sfr=on:ssfp=10000:ssfq=2.0:ssnc=none:sp=reverse_arity:urr=on_1");
                    quick.push("lrs+1002_3_bd=off:bs=on:bsr=unit_only:cond=fast:fsr=off:lcm=predicate:nwc=1.5:stl=30:sos=on:sdd=off:sser=off:sfr=on:sp=reverse_arity_7");
                    quick.push("dis+1011_2_fde=unused:gs=on:nwc=1:sac=on:ssfp=40000:ssfq=1.1:smm=off:ssnc=none:sp=reverse_arity:urr=ec_only_20");
                    quick.push("dis+11_7_fde=none:nm=0:nwc=1:sd=3:ss=axioms:st=2.0:spl=off:sp=occurrence:urr=on:updr=off_8");
                    quick.push("dis+1010_3:1_cond=fast:fde=unused:gs=on:nwc=1:sd=2:ss=axioms:sos=on:sdd=large:sser=off:sfr=on:ssfp=100000:ssfq=1.2:updr=off_18");
                    quick.push("lrs+1010_8:1_fsr=off:fde=none:gs=on:gsem=on:gsssp=full:nwc=1.1:sas=minisat:stl=30:sos=all:ssac=none:sfr=on:ssfp=100000:ssfq=1.0:smm=off:ssnc=all:sp=occurrence:updr=off_9");
                    quick.push("lrs+4_2:1_ep=R:fde=unused:gs=on:nwc=1:stl=30:sos=all:sac=on:ssac=none:sser=off:sfr=on:ssfp=10000:ssfq=1.2:ssnc=none:sp=occurrence:updr=off_1");
                    quick.push("dis-3_10_bsr=unit_only:er=filter:fde=unused:lcm=predicate:nm=64:nwc=1:spl=off:sp=occurrence:updr=off_109");
                    quick.push("lrs-1_4_cond=fast:ep=RST:fde=unused:gs=on:gsem=on:gsssp=full:lwlo=on:nwc=1:sas=minisat:stl=30:spl=off:urr=ec_only_32");
                    quick.push("dis+1010_5:1_bs=unit_only:ccuc=small_ones:cond=on:fsr=off:fde=none:gs=on:gsem=off:nm=0:nwc=3:sos=on:sac=on:sscc=on:ssfp=40000:ssfq=1.2:smm=sco:ssnc=all_dependent:sp=occurrence:urr=ec_only_2");
                    quick.push("lrs-2_5_cond=on:fde=none:lcm=predicate:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=on:sdd=off:ssfp=100000:ssfq=1.4:ssnc=none_3");
                    quick.push("lrs+11_5:4_br=off:cond=on:fde=none:gs=on:gsem=on:gsssp=full:nwc=1:sas=minisat:stl=30:sd=3:ss=axioms:st=3.0:sos=all:sac=on:sser=off:sfr=on:ssfp=1000:ssfq=1.4:ssnc=all:sp=reverse_arity:urr=on:updr=off_63");
                    quick.push("lrs+1011_3_bsr=unit_only:cond=on:fsr=off:lwlo=on:nwc=1:stl=30:sd=3:ss=axioms:st=3.0:spl=off_7");
                    quick.push("ins+11_3_cond=fast:fde=none:igbrr=0.8:igrr=1/16:igrp=200:igrpq=1.05:igs=1003:igwr=on:nm=64:nwc=1:sas=minisat:sd=2:ss=axioms:st=3.0:sos=on:spl=off:updr=off_18");
                    quick.push("dis+1010_1_fde=none:gs=on:gsem=off:gsssp=full:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:sfr=on:smm=off:ssnc=all:sp=reverse_arity:updr=off_6");
                    quick.push("lrs+11_3:2_cond=fast:fsr=off:fde=none:gs=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:st=2.0:spl=off:urr=on_3");
                    quick.push("ott+1010_40_bs=unit_only:cond=fast:nwc=1:sas=minisat:sdd=off:ssfp=10000:ssfq=2.0:smm=sco:ssnc=none:sp=reverse_arity:updr=off_46");
                    quick.push("dis+1002_4_cond=fast:fde=unused:gsp=input_only:gs=on:gsem=on:nm=64:nwc=1:sas=minisat:sos=on:sscc=model:sser=off:sfr=on:ssfp=4000:ssfq=1.4:ssnc=none:updr=off_25");
                    quick.push("dis+1010_50_gs=on:gsaa=full_model:gsem=on:nwc=4:nicw=on:sas=minisat:ssac=none:sscc=model:ssfp=100000:ssfq=2.0:smm=off:ssnc=none:sp=reverse_arity:updr=off_66");
                    quick.push("dis+11_5_cond=on:fsr=off:fde=none:gsp=input_only:lcm=reverse:nm=0:nwc=4:sfr=on:ssfp=100000:ssfq=1.0:smm=sco:ssnc=none:updr=off_47");
                    quick.push("lrs+11_2_br=off:cond=on:fde=none:gs=on:gsaa=full_model:lwlo=on:nwc=2:sas=minisat:stl=30:ssfp=100000:ssfq=1.4:smm=sco:ssnc=none:sp=occurrence:urr=on_87");
                    quick.push("dis+11_2_fde=none:gsp=input_only:gs=on:gsem=on:nwc=1:sd=2:ss=axioms:st=1.2:sos=all:spl=off:sp=reverse_arity:urr=on:updr=off_76");
                    quick.push("lrs+10_1_bd=off:fde=none:gsp=input_only:lcm=predicate:nm=0:nwc=1:stl=30:sos=on:spl=off:updr=off_52");
                    quick.push("dis-4_2_cond=on:fde=unused:lcm=reverse:nwc=1:sos=on:spl=off:sp=reverse_arity:updr=off_58");
                    quick.push("lrs+11_4:1_fsr=off:fde=unused:gs=on:gsem=off:nwc=1:sas=minisat:stl=30:spl=off:sp=reverse_arity:urr=ec_only_73");
                    quick.push("lrs+1002_7_ccuc=first:cond=on:fde=none:gs=on:gsssp=full:nwc=1:sas=minisat:stl=90:sd=3:ss=axioms:sscc=model:sser=off:ssfp=1000:ssfq=2.0:ssnc=none:sp=reverse_arity_874");
                    quick.push("ott+11_24_cond=fast:ep=RST:fsr=off:fde=none:gs=on:lcm=predicate:nm=64:nwc=1:sas=minisat:ss=axioms:st=5.0:sos=all:spl=off:sp=occurrence_1");
                    quick.push("dis+1011_24_cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=64:nwc=1:sos=on:spl=off:sp=occurrence_10");
                    quick.push("dis+11_8_bs=unit_only:nwc=1:sd=10:ss=axioms:st=1.5:spl=off:sp=occurrence:updr=off_83");
                }
                else {
                    quick.push("dis+1002_4_cond=fast:fde=unused:gsp=input_only:gs=on:gsem=on:nm=64:nwc=1:sas=minisat:sos=on:sscc=model:sser=off:sfr=on:ssfp=4000:ssfq=1.4:ssnc=none:updr=off_3");
                    quick.push("lrs+1011_2:1_br=off:cond=fast:fde=none:gs=on:gsssp=full:nwc=1:stl=30:sos=all:sac=on:sdd=off:ssfp=1000:ssfq=2.0:smm=sco:ssnc=none:urr=on_16");
                    quick.push("ins+11_3_cond=fast:fde=none:igbrr=0.8:igrr=1/16:igrp=200:igrpq=1.05:igs=1003:igwr=on:nm=64:nwc=1:sas=minisat:sd=2:ss=axioms:st=3.0:sos=on:spl=off:updr=off_6");
                    quick.push("lrs+10_2_bsr=unit_only:cond=fast:gsp=input_only:gs=on:gsssp=full:lcm=reverse:lwlo=on:nwc=1:sas=minisat:stl=30:sos=on:spl=off:sp=reverse_arity_2");
                    quick.push("dis+11_7_3");
                    quick.push("dis+1010_5:1_cond=fast:ep=RSTC:er=known:fde=unused:nm=0:nwc=2:spl=off_10");
                    quick.push("dis+11_5_fde=none:nwc=1:sas=minisat:sd=1:ss=axioms:st=5.0:sos=all:sdd=large:sser=off:sfr=on:ssfp=100000:ssfq=2.0:ssnc=none_9");
                    quick.push("dis+1003_8:1_bd=off:bs=unit_only:cond=fast:fsr=off:fde=none:gsp=input_only:lcm=reverse:nwc=1:sas=minisat:sos=all:ssac=none:sscc=on:sdd=off:sfr=on:smm=sco:ssnc=none:sp=reverse_arity_7");
                    quick.push("dis+11_8_bs=unit_only:nwc=1:sd=10:ss=axioms:st=1.5:spl=off:sp=occurrence:updr=off_5");
                    quick.push("dis+1002_3_cond=fast:er=known:gs=on:gsaa=from_current:gsem=on:gsssp=full:nwc=1:sas=minisat:ssfp=1000:ssfq=1.4:ssnc=all_dependent:sp=occurrence_1");
                    quick.push("lrs+1002_2:3_bsr=unit_only:er=known:fde=none:gs=on:gsem=on:nwc=1:sas=minisat:stl=30:sd=1:ss=axioms:st=1.5:sdd=large:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=none:sp=reverse_arity_9");
                    quick.push("lrs+1002_4_cond=on:er=filter:fde=unused:gsp=input_only:gs=on:gsssp=full:nwc=10:sas=minisat:stl=30:spl=off:sp=occurrence_5");
                    quick.push("dis+1010_2_bd=off:bsr=unit_only:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:nwc=1:sas=minisat:sos=on:sac=on:sscc=on:sfr=on:ssfp=4000:ssfq=1.2:smm=sco:ssnc=none:sp=occurrence:urr=ec_only:updr=off_12");
                    quick.push("lrs+1002_7_ccuc=first:cond=on:fde=none:gs=on:gsssp=full:nwc=1:sas=minisat:stl=90:sd=3:ss=axioms:sscc=model:sser=off:ssfp=1000:ssfq=2.0:ssnc=none:sp=reverse_arity_56");
                    quick.push("ins+11_3_bsr=unit_only:fde=none:gs=on:gsem=off:igrr=1/16:igrpq=1.5:igs=1004:igwr=on:lcm=reverse:nm=0:nwc=1:sos=all:spl=off:updr=off:dm=on_27");
                    quick.push("dis+2_2:1_cond=on:er=filter:fde=none:gs=on:gsem=on:nwc=1:sac=on:sdd=large:ssfp=10000:ssfq=1.2:smm=off:sp=occurrence_24");
                    quick.push("lrs+10_4_ccuc=first:cond=on:gs=on:gsssp=full:nwc=1:stl=90:sd=2:ss=axioms:st=1.5:sos=on:sscc=on:sser=off:ssfp=40000:ssfq=1.2:ssnc=none:sp=reverse_arity:updr=off_34");
                    quick.push("ott+1011_3_bd=off:fde=unused:nwc=1.5:spl=off:sp=occurrence:updr=off_80");
                    quick.push("ott+1002_5_bsr=on:fsr=off:fde=none:gs=on:gsem=off:lwlo=on:nwc=1:sscc=on:sser=off:ssfp=100000:ssfq=1.1:sp=occurrence_291");
                    quick.push("lrs+1010_1_bs=unit_only:cond=fast:gs=on:gsem=off:nwc=1:stl=30:sos=all:spl=off_143");
                    quick.push("lrs+1002_3_bd=off:bs=on:bsr=unit_only:cond=fast:fsr=off:lcm=predicate:nwc=1.5:stl=30:sos=on:sdd=off:sser=off:sfr=on:sp=reverse_arity_141");
                    quick.push("lrs+4_3:1_bs=on:bsr=unit_only:ccuc=small_ones:cond=fast:er=filter:fsr=off:lcm=predicate:nm=1024:nwc=1:sas=minisat:stl=30:sos=on:sac=on:sscc=on:ssfp=1000:ssfq=1.2:smm=sco:ssnc=all_dependent:sp=reverse_arity:updr=off_271");
                    quick.push("lrs+1011_8_br=off:cond=fast:fsr=off:fde=none:nwc=1:sas=minisat:stl=30:sd=2:ss=axioms:sos=all:spl=off:urr=on_148");
                    quick.push("dis+1010_4:1_cond=fast:fsr=off:nm=0:nwc=1:sas=minisat:sac=on:sdd=large:sfr=on:ssfp=40000:ssfq=2.0:smm=sco:ssnc=none:sp=occurrence:urr=ec_only_298");
                    quick.push("dis+1010_3:1_cond=fast:fde=unused:gs=on:nwc=1:sd=2:ss=axioms:sos=on:sdd=large:sser=off:sfr=on:ssfp=100000:ssfq=1.2:updr=off_18");
                    quick.push("ott+11_8:1_cond=fast:gs=on:gsem=off:nwc=1:nicw=on:sd=2:ss=axioms:st=1.2:sos=all:sscc=on:sfr=on:ssfp=100000:ssfq=1.0:smm=sco:ssnc=none:urr=on_19");
                    quick.push("dis+1011_1_cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:nm=0:nwc=1:sas=minisat:sd=3:ss=axioms:sos=on:ssac=none:sfr=on:ssfp=100000:ssfq=1.2:smm=sco:ssnc=none:sp=occurrence_27");
                    quick.push("lrs+10_1_bd=off:fde=none:gsp=input_only:lcm=predicate:nm=0:nwc=1:stl=30:sos=on:spl=off:updr=off_30");
                }
            }
            else if (prop == 131075) {
                quick.push("ott+2_2_cond=fast:fsr=off:gs=on:nwc=1:sd=1:ss=axioms:st=2.0:sos=on:sac=on:sdd=large:sser=off:sfr=on:ssfp=4000:ssfq=1.4:ssnc=none:sp=reverse_arity:urr=on:updr=off_3");
                quick.push("lrs+1011_3_bsr=unit_only:cond=on:fsr=off:lwlo=on:nwc=1:stl=30:sd=3:ss=axioms:st=3.0:spl=off_20");
                quick.push("lrs+4_2:1_ep=R:fde=unused:gs=on:nwc=1:stl=30:sos=all:sac=on:ssac=none:sser=off:sfr=on:ssfp=10000:ssfq=1.2:ssnc=none:sp=occurrence:updr=off_2");
                quick.push("dis+1010_4:1_cond=fast:fsr=off:nm=0:nwc=1:sas=minisat:sac=on:sdd=large:sfr=on:ssfp=40000:ssfq=2.0:smm=sco:ssnc=none:sp=occurrence:urr=ec_only_15");
                quick.push("lrs+4_5_cond=fast:fsr=off:fde=none:gs=on:gsaa=from_current:nwc=1:stl=90:sd=5:ss=axioms:st=1.2:sac=on:sdd=off:sser=off:sfr=on:ssfp=4000:ssfq=2.0:ssnc=none:sp=occurrence_2");
                quick.push("lrs+10_2:3_bsr=on:fsr=off:fde=unused:nwc=1:sas=minisat:stl=30:sos=all:sac=on:sdd=off:sfr=on:ssfp=1000:ssfq=1.0:smm=sco:ssnc=none:urr=on:updr=off_3");
                quick.push("dis+1010_2_bd=off:bsr=unit_only:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:nwc=1:sas=minisat:sos=on:sac=on:sscc=on:sfr=on:ssfp=4000:ssfq=1.2:smm=sco:ssnc=none:sp=occurrence:urr=ec_only:updr=off_3");
                quick.push("ott+1011_3_bd=off:fde=unused:nwc=1.5:spl=off:sp=occurrence:updr=off_43");
                quick.push("lrs+10_2_bsr=unit_only:cond=fast:gsp=input_only:gs=on:gsssp=full:lcm=reverse:lwlo=on:nwc=1:sas=minisat:stl=30:sos=on:spl=off:sp=reverse_arity_37");
                quick.push("lrs+3_5:1_bd=off:bs=unit_only:bsr=unit_only:br=off:ccuc=small_ones:er=known:fsr=off:fde=unused:gs=on:nm=0:nwc=1.1:stl=30:sd=3:ss=axioms:sos=on:sscc=model:sdd=off:sser=off:ssfp=4000:ssfq=1.4:sp=occurrence:urr=on:updr=off_1");
                quick.push("lrs-3_2:1_bsr=unit_only:fde=none:gs=on:gsssp=full:nm=0:nwc=1.5:sas=minisat:stl=30:sos=all:sac=on:smm=sco:ssnc=none:sp=occurrence_22");
                quick.push("dis+4_3:1_gs=on:nwc=1:sd=1:ss=axioms:sos=all:spl=off:updr=off_51");
                quick.push("ott+11_8:1_cond=fast:gs=on:gsem=off:nwc=1:nicw=on:sd=2:ss=axioms:st=1.2:sos=all:sscc=on:sfr=on:ssfp=100000:ssfq=1.0:smm=sco:ssnc=none:urr=on_43");
                quick.push("ott+1_3:1_cond=fast:gs=on:gsem=off:nwc=1:sas=minisat:sos=all:ssfp=10000:ssfq=1.1:smm=sco:ssnc=none:sp=occurrence:urr=on:updr=off_17");
                quick.push("dis-4_3:2_cond=fast:fsr=off:fde=none:gsp=input_only:lcm=predicate:nwc=1:sos=on:spl=off:urr=ec_only_13");
                quick.push("dis+1002_6_ccuc=first:cond=fast:gsp=input_only:gs=on:gsaa=from_current:gsem=on:gsssp=full:nm=64:nwc=2.5:nicw=on:sas=minisat:sos=on:ssac=none:sscc=on:sdd=large:sfr=on:ssfp=100000:ssfq=1.2:smm=off:sp=occurrence:urr=ec_only:updr=off_222");
                quick.push("lrs+10_5:4_bsr=unit_only:fde=none:lcm=reverse:nm=64:nwc=10:stl=30:spl=off:sp=occurrence:updr=off_24");
                quick.push("lrs-1_2:1_bd=preordered:bsr=on:br=off:cond=on:gs=on:lcm=reverse:nwc=1:stl=30:sd=2:ss=axioms:sos=on:sdd=large:sser=off:ssfp=100000:ssfq=2.0:ssnc=none:sp=occurrence:urr=on:updr=off_2");
                quick.push("lrs+11_2:3_bd=off:fsr=off:gsp=input_only:lcm=predicate:lwlo=on:nwc=1:stl=30:spl=off:sp=occurrence:urr=ec_only_59");
                quick.push("lrs-1_4_cond=fast:ep=RST:fde=unused:gs=on:gsem=on:gsssp=full:lwlo=on:nwc=1:sas=minisat:stl=30:spl=off:urr=ec_only_26");
                quick.push("lrs+10_2_bd=off:bsr=unit_only:ccuc=first:cond=fast:fsr=off:fde=none:gs=on:gsem=on:nwc=1.5:nicw=on:stl=240:sos=all:sac=on:ssac=none:sscc=model:sfr=on:ssfp=10000:ssfq=2.0:smm=off:ssnc=none:sp=occurrence:updr=off_22");
                quick.push("dis+11_4:1_br=off:ccuc=first:fsr=off:fde=none:nm=0:nwc=1:sos=all:sscc=model:sdd=off:sser=off:ssfp=10000:ssfq=1.1:ssnc=all_dependent:sp=occurrence:urr=on:updr=off_29");
                quick.push("lrs+1002_6_ccuc=first:cond=on:fsr=off:nwc=4:nicw=on:sas=minisat:stl=30:sscc=on:sfr=on:ssfp=40000:ssfq=1.0:smm=sco:ssnc=all_dependent:sp=reverse_arity:urr=ec_only_246");
                quick.push("dis+1010_5:1_bs=unit_only:ccuc=small_ones:cond=on:fsr=off:fde=none:gs=on:gsem=off:nm=0:nwc=3:sos=on:sac=on:sscc=on:ssfp=40000:ssfq=1.2:smm=sco:ssnc=all_dependent:sp=occurrence:urr=ec_only_66");
                quick.push("lrs+1002_2:3_br=off:fde=unused:gs=on:gsaa=from_current:gsem=on:gsssp=full:nwc=1:sas=minisat:stl=30:sac=on:sser=off:sfr=on:ssfp=100000:ssfq=2.0:ssnc=none:sp=reverse_arity:urr=on_79");
                quick.push("dis+1010_8_bd=off:bsr=on:ccuc=first:cond=fast:er=known:fsr=off:gs=on:gsssp=full:lcm=reverse:nm=0:nwc=1:sas=minisat:sd=2:ss=axioms:st=5.0:sscc=on:sdd=off:ssfp=100000:ssfq=1.1:urr=ec_only:updr=off_276");
                quick.push("lrs+3_5_bd=preordered:bsr=unit_only:gsp=input_only:gs=on:gsem=on:gsssp=full:lwlo=on:nm=64:nwc=1:sas=minisat:stl=90:spl=off:sp=occurrence:urr=ec_only:updr=off_646");
                quick.push("ins+11_5_fde=unused:igpr=on:igrr=1/16:igrp=200:igrpq=1.1:igs=1010:igwr=on:nwc=1:sos=all:spl=off_767");
                quick.push("dis+1003_3_bs=unit_only:cond=fast:gs=on:gsaa=full_model:lwlo=on:nwc=1.5:sas=minisat:sd=1:ss=axioms:st=2.0:sac=on:sdd=large:sfr=on:ssfp=100000:ssfq=1.2:ssnc=none:sp=reverse_arity:updr=off_4");
                quick.push("dis+1002_5_cond=fast:ep=RST:fsr=off:fde=none:gsp=input_only:nwc=1:sd=2:ss=axioms:spl=off:urr=ec_only:updr=off_8");
                quick.push("lrs+11_3:2_cond=fast:fsr=off:fde=none:gs=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:st=2.0:spl=off:urr=on_28");
            }
            else if (prop == 131087) {
                if (atoms > 50000) {
                    quick.push("ott+1011_10_cond=fast:fde=none:gsp=input_only:gs=on:gsssp=full:nwc=1:sas=minisat:sd=3:ss=axioms:sos=all:spl=off:sp=occurrence:updr=off_10");
                    quick.push("lrs-2_5_cond=on:fde=none:lcm=predicate:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=on:sdd=off:ssfp=100000:ssfq=1.4:ssnc=none_19");
                    quick.push("lrs+1011_5_bd=off:br=off:ccuc=small_ones:fde=none:gs=on:gsem=off:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sscc=model:ssfp=100000:ssfq=1.4:smm=off:ssnc=none:sp=occurrence:urr=on_6");
                    quick.push("dis+1010_1_fde=none:gs=on:gsem=off:gsssp=full:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:sfr=on:smm=off:ssnc=all:sp=reverse_arity:updr=off_6");
                    quick.push("dis-2_4_cond=fast:ep=RST:er=filter:fde=unused:gs=on:gsem=on:lcm=reverse:nwc=1:sd=3:ss=axioms:sos=on:spl=off:updr=off_14");
                    quick.push("ins+11_4_cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:gsem=on:igbrr=0.3:igpr=on:igrr=1/8:igrp=100:igrpq=1.5:igwr=on:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:spl=off:dm=on_49");
                    quick.push("lrs+10_4_ccuc=first:cond=on:gs=on:gsssp=full:nwc=1:stl=90:sd=2:ss=axioms:st=1.5:sos=on:sscc=on:sser=off:ssfp=40000:ssfq=1.2:ssnc=none:sp=reverse_arity:updr=off_15");
                    quick.push("lrs-1_2:1_bd=preordered:bsr=on:br=off:cond=on:gs=on:lcm=reverse:nwc=1:stl=30:sd=2:ss=axioms:sos=on:sdd=large:sser=off:ssfp=100000:ssfq=2.0:ssnc=none:sp=occurrence:urr=on:updr=off_65");
                    quick.push("lrs+1002_3_ep=RST:er=known:fsr=off:gs=on:gsaa=from_current:nwc=1:sas=minisat:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sfr=on:ssfp=100000:ssfq=1.4:smm=sco:ssnc=none:sp=occurrence_75");
                    quick.push("dis+1011_1_cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:nm=0:nwc=1:sas=minisat:sd=3:ss=axioms:sos=on:ssac=none:sfr=on:ssfp=100000:ssfq=1.2:smm=sco:ssnc=none:sp=occurrence_17");
                    quick.push("dis+4_3:1_gs=on:nwc=1:sd=1:ss=axioms:sos=all:spl=off:updr=off_12");
                    quick.push("lrs+1010_4:1_cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=0:nwc=1:sas=minisat:stl=30:sd=2:ss=axioms:st=1.5:sos=on:sac=on:sdd=off:sser=off:sfr=on:ssfp=100000:ssfq=1.4:ssnc=none:sp=occurrence_74");
                    quick.push("lrs+11_5:4_br=off:cond=on:fde=none:gs=on:gsem=on:gsssp=full:nwc=1:sas=minisat:stl=30:sd=3:ss=axioms:st=3.0:sos=all:sac=on:sser=off:sfr=on:ssfp=1000:ssfq=1.4:ssnc=all:sp=reverse_arity:urr=on:updr=off_18");
                    quick.push("dis+1002_4_cond=fast:fde=unused:gsp=input_only:gs=on:gsem=on:nm=64:nwc=1:sas=minisat:sos=on:sscc=model:sser=off:sfr=on:ssfp=4000:ssfq=1.4:ssnc=none:updr=off_46");
                    quick.push("ott+1_2_cond=fast:er=filter:fsr=off:fde=none:gs=on:gsem=off:gsssp=full:nwc=1:sas=minisat:sd=1:ss=axioms:st=1.2:sac=on:sdd=large:sfr=on:ssfp=40000:ssfq=1.0:smm=sco:ssnc=none_13");
                    quick.push("dis-4_2_cond=on:fde=unused:lcm=reverse:nwc=1:sos=on:spl=off:sp=reverse_arity:updr=off_40");
                    quick.push("dis+1003_3_bs=unit_only:cond=fast:gs=on:gsaa=full_model:lwlo=on:nwc=1.5:sas=minisat:sd=1:ss=axioms:st=2.0:sac=on:sdd=large:sfr=on:ssfp=100000:ssfq=1.2:ssnc=none:sp=reverse_arity:updr=off_8");
                    quick.push("dis+2_5:4_fde=none:nwc=1:sd=2:ss=axioms:sos=on:ssfp=40000:ssfq=2.0_131");
                    quick.push("ott+11_8:1_cond=fast:gs=on:gsem=off:nwc=1:nicw=on:sd=2:ss=axioms:st=1.2:sos=all:sscc=on:sfr=on:ssfp=100000:ssfq=1.0:smm=sco:ssnc=none:urr=on_95");
                    quick.push("dis+11_2_fde=none:gsp=input_only:gs=on:gsem=on:nwc=1:sd=2:ss=axioms:st=1.2:sos=all:spl=off:sp=reverse_arity:urr=on:updr=off_241");
                    quick.push("ins+11_3_cond=fast:fde=none:igbrr=0.8:igrr=1/16:igrp=200:igrpq=1.05:igs=1003:igwr=on:nm=64:nwc=1:sas=minisat:sd=2:ss=axioms:st=3.0:sos=on:spl=off:updr=off_285");
                    quick.push("lrs+11_3:2_cond=fast:fsr=off:fde=none:gs=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:st=2.0:spl=off:urr=on_234");
                    quick.push("lrs+1011_8_br=off:cond=fast:fsr=off:fde=none:nwc=1:sas=minisat:stl=30:sd=2:ss=axioms:sos=all:spl=off:urr=on_13");
                    quick.push("lrs+10_1_bd=off:fde=none:gsp=input_only:lcm=predicate:nm=0:nwc=1:stl=30:sos=on:spl=off:updr=off_75");
                }
                else {
                    quick.push("lrs+1010_4_fde=unused:gs=on:gsem=off:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on:sac=on:ssfp=40000:ssfq=1.2:smm=sco:ssnc=none:sp=reverse_arity:urr=on:updr=off_12");
                    quick.push("lrs+1011_2:1_br=off:cond=fast:fde=none:gs=on:gsssp=full:nwc=1:stl=30:sos=all:sac=on:sdd=off:ssfp=1000:ssfq=2.0:smm=sco:ssnc=none:urr=on_5");
                    quick.push("lrs+10_4_ccuc=first:cond=on:gs=on:gsssp=full:nwc=1:stl=90:sd=2:ss=axioms:st=1.5:sos=on:sscc=on:sser=off:ssfp=40000:ssfq=1.2:ssnc=none:sp=reverse_arity:updr=off_4");
                    quick.push("lrs+1011_4_cond=fast:gs=on:gsaa=from_current:gsem=off:gsssp=full:nm=0:nwc=1:sas=minisat:stl=30:sd=3:ss=axioms:st=2.0:sdd=off:sfr=on:ssfp=100000:ssfq=1.2:smm=off:ssnc=none:sp=reverse_arity_58");
                    quick.push("ott+11_8:1_cond=fast:gs=on:gsem=off:nwc=1:nicw=on:sd=2:ss=axioms:st=1.2:sos=all:sscc=on:sfr=on:ssfp=100000:ssfq=1.0:smm=sco:ssnc=none:urr=on_27");
                    quick.push("dis-4_2_cond=on:fde=unused:lcm=reverse:nwc=1:sos=on:spl=off:sp=reverse_arity:updr=off_4");
                    quick.push("ott+11_5_nwc=1:sd=7:ss=axioms:st=2.0:sac=on:sfr=on:ssfp=40000:ssfq=1.2:ssnc=none_19");
                    quick.push("lrs+1011_5_bd=off:br=off:ccuc=small_ones:fde=none:gs=on:gsem=off:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sscc=model:ssfp=100000:ssfq=1.4:smm=off:ssnc=none:sp=occurrence:urr=on_4");
                    quick.push("dis+1002_4_cond=fast:fde=unused:gsp=input_only:gs=on:gsem=on:nm=64:nwc=1:sas=minisat:sos=on:sscc=model:sser=off:sfr=on:ssfp=4000:ssfq=1.4:ssnc=none:updr=off_19");
                    quick.push("ins+11_4_cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:gsem=on:igbrr=0.3:igpr=on:igrr=1/8:igrp=100:igrpq=1.5:igwr=on:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:spl=off:dm=on_9");
                    quick.push("lrs+11_5:4_br=off:cond=on:fde=none:gs=on:gsem=on:gsssp=full:nwc=1:sas=minisat:stl=30:sd=3:ss=axioms:st=3.0:sos=all:sac=on:sser=off:sfr=on:ssfp=1000:ssfq=1.4:ssnc=all:sp=reverse_arity:urr=on:updr=off_122");
                    quick.push("ott+1_2_cond=fast:er=filter:fsr=off:fde=none:gs=on:gsem=off:gsssp=full:nwc=1:sas=minisat:sd=1:ss=axioms:st=1.2:sac=on:sdd=large:sfr=on:ssfp=40000:ssfq=1.0:smm=sco:ssnc=none_5");
                    quick.push("dis+4_3:1_gs=on:nwc=1:sd=1:ss=axioms:sos=all:spl=off:updr=off_6");
                    quick.push("dis+1010_5:1_cond=fast:ep=RSTC:er=known:fde=unused:nm=0:nwc=2:spl=off_18");
                    quick.push("dis+1011_1_cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:nm=0:nwc=1:sas=minisat:sd=3:ss=axioms:sos=on:ssac=none:sfr=on:ssfp=100000:ssfq=1.2:smm=sco:ssnc=none:sp=occurrence_57");
                    quick.push("lrs-1_2:1_bd=preordered:bsr=on:br=off:cond=on:gs=on:lcm=reverse:nwc=1:stl=30:sd=2:ss=axioms:sos=on:sdd=large:sser=off:ssfp=100000:ssfq=2.0:ssnc=none:sp=occurrence:urr=on:updr=off_67");
                    quick.push("dis+1010_4:1_cond=fast:fsr=off:nm=0:nwc=1:sas=minisat:sac=on:sdd=large:sfr=on:ssfp=40000:ssfq=2.0:smm=sco:ssnc=none:sp=occurrence:urr=ec_only_17");
                    quick.push("lrs+4_2:1_ep=R:fde=unused:gs=on:nwc=1:stl=30:sos=all:sac=on:ssac=none:sser=off:sfr=on:ssfp=10000:ssfq=1.2:ssnc=none:sp=occurrence:updr=off_294");
                    quick.push("lrs+1003_7_cond=fast:nwc=1:stl=30:sd=4:ss=axioms:sos=all:spl=off:updr=off_129");
                    quick.push("ott+1011_3_bd=off:fde=unused:nwc=1.5:spl=off:sp=occurrence:updr=off_66");
                    quick.push("lrs+1011_8_br=off:cond=fast:fsr=off:fde=none:nwc=1:sas=minisat:stl=30:sd=2:ss=axioms:sos=all:spl=off:urr=on_34");
                    quick.push("lrs+1_3:1_cond=fast:gsp=input_only:gs=on:gsaa=from_current:gsem=off:nwc=1:stl=30:sd=2:ss=axioms:st=1.2:sos=on:sac=on:sdd=off:sfr=on:ssfp=100000:ssfq=1.2:smm=sco:ssnc=none:sp=reverse_arity_41");
                    quick.push("lrs+1002_2:3_bsr=unit_only:er=known:fde=none:gs=on:gsem=on:nwc=1:sas=minisat:stl=30:sd=1:ss=axioms:st=1.5:sdd=large:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=none:sp=reverse_arity_226");
                    quick.push("dis+11_2_fde=none:gsp=input_only:gs=on:gsem=on:nwc=1:sd=2:ss=axioms:st=1.2:sos=all:spl=off:sp=reverse_arity:urr=on:updr=off_275");
                    quick.push("ins+11_3_cond=fast:fde=none:igbrr=0.8:igrr=1/16:igrp=200:igrpq=1.05:igs=1003:igwr=on:nm=64:nwc=1:sas=minisat:sd=2:ss=axioms:st=3.0:sos=on:spl=off:updr=off_89");
                    quick.push("dis+1011_2_fde=unused:gs=on:nwc=1:sac=on:ssfp=40000:ssfq=1.1:smm=off:ssnc=none:sp=reverse_arity:urr=ec_only_116");
                    quick.push("dis+1003_8:1_bd=off:bs=unit_only:cond=fast:fsr=off:fde=none:gsp=input_only:lcm=reverse:nwc=1:sas=minisat:sos=all:ssac=none:sscc=on:sdd=off:sfr=on:smm=sco:ssnc=none:sp=reverse_arity_280");
                    quick.push("lrs+3_5:1_bd=off:bs=unit_only:bsr=unit_only:br=off:ccuc=small_ones:er=known:fsr=off:fde=unused:gs=on:nm=0:nwc=1.1:stl=30:sd=3:ss=axioms:sos=on:sscc=model:sdd=off:sser=off:ssfp=4000:ssfq=1.4:sp=occurrence:urr=on:updr=off_148");
                    quick.push("lrs+1002_3_ep=RST:er=known:fsr=off:gs=on:gsaa=from_current:nwc=1:sas=minisat:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sfr=on:ssfp=100000:ssfq=1.4:smm=sco:ssnc=none:sp=occurrence_231");
                    quick.push("ott+11_3:1_br=off:gs=on:gsem=on:nwc=1:sas=minisat:sos=all:spl=off:urr=on:updr=off_81");
                }
            }
            else if (prop & 67108864ul) {
                quick.push("dis+10_3_br=off:cond=fast:fde=none:gs=on:gsem=on:gsssp=full:inw=on:nwc=1:sas=minisat:sos=all:sac=on:sdd=large:ssfp=100000:ssfq=1.1:ssnc=none:sp=reverse_arity:urr=on_1");
                quick.push("dis+1010_5:1_fde=none:lwlo=on:nm=0:nwc=1:sas=minisat:sos=on:sdd=off:sfr=on:ssfp=1000:ssfq=1.1:ssnc=none:sp=reverse_arity:tha=off_12");
                quick.push("lrs+11_1_br=off:fde=unused:gs=on:gsem=off:inw=on:nwc=1:sas=minisat:stl=30:sac=on:sscc=model:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=on:updr=off_3");
                quick.push("lrs+11_2_bd=off:ccuc=first:cond=on:fde=unused:gs=on:gsem=off:nwc=1:stl=30:sos=all:sscc=model:sdd=large:sser=off:ssfp=4000:ssfq=1.1:ssnc=none:sp=occurrence:updr=off_3");
                quick.push("dis+10_5_bd=off:cond=fast:fsr=off:fde=unused:gsp=input_only:gs=on:gsem=off:nwc=1:sas=minisat:sos=on:sfr=on:ssfp=10000:ssfq=1.1:smm=off:ssnc=none:sp=occurrence:urr=ec_only:updr=off_2");
                quick.push("ott+11_6_cond=fast:fsr=off:fde=unused:gs=on:gsem=off:gsssp=full:inw=on:nwc=1.5:sas=minisat:spl=off:sp=occurrence:urr=on_27");
                quick.push("dis+1002_2_cond=on:gs=on:inw=on:nwc=1:sas=minisat:sos=on:sac=on:sdd=large:sser=off:sfr=on:ssfp=4000:ssfq=1.2:ssnc=none:sp=reverse_arity_1");
                quick.push("lrs+1010_2:1_bd=off:bsr=unit_only:cond=fast:fde=none:gs=on:gsem=off:nm=0:nwc=2.5:stl=30:sac=on:sscc=model:sdd=off:ssfp=100000:ssfq=1.4:smm=off:ssnc=none:sp=reverse_arity:urr=on:updr=off_28");
                quick.push("ins+11_32_br=off:ep=RSTC:inw=on:igbrr=0.9:igrr=1/32:igrp=100:igrpq=2.0:igs=1004:igwr=on:nwc=1:spl=off:urr=on:updr=off:dm=on_1");
                quick.push("dis+1003_3:2_bd=off:bsr=unit_only:nwc=1.3:sas=minisat:sac=on:sdd=large:sser=off:sfr=on:ssfp=1000:ssfq=1.2:ssnc=none:updr=off_23");
                quick.push("ott+11_2:1_cond=on:gs=on:gsssp=full:lwlo=on:nwc=1:sas=minisat:sos=all:spl=off:sp=occurrence:tha=off_12");
                quick.push("lrs+1011_8:1_gs=on:gsssp=full:inw=on:nwc=1:stl=30:sdd=off:sfr=on:ssfp=4000:ssfq=1.4:smm=off:ssnc=none_26");
                quick.push("lrs+2_8:1_cond=fast:er=filter:fde=unused:lcm=predicate:nwc=2.5:sas=minisat:stl=60:sdd=off:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=none:sp=occurrence:updr=off_9");
                quick.push("lrs+11_5:1_bd=off:gs=on:gsem=off:gsssp=full:nwc=1.3:sas=minisat:stl=30:sos=all:sac=on:ssac=none:sscc=model:sdd=large:ssfp=4000:ssfq=1.4:ssnc=none:sp=occurrence_203");
                quick.push("ott-11_4_br=off:cond=on:gs=on:gsem=off:gsssp=full:nwc=5:sas=minisat:sac=on:sdd=large:sfr=on:ssfp=4000:ssfq=2.0:ssnc=all:sp=occurrence:urr=on:updr=off_39");
                quick.push("lrs+11_8:1_br=off:cond=on:fsr=off:fde=none:gs=on:inw=on:lwlo=on:nwc=1.5:stl=30:sser=off:ssfp=10000:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=on_99");
                quick.push("ott+1010_3:1_cond=fast:fde=none:nwc=1:sos=all:spl=off_170");
                quick.push("ott+1011_4:1_bd=off:bsr=unit_only:cond=fast:fsr=off:fde=none:inw=on:nm=0:nwc=1.1:sas=minisat:sos=on:ssfp=10000:ssfq=1.2:ssnc=none:sp=occurrence_172");
                quick.push("dis+10_3_cond=fast:fsr=off:gs=on:gsaa=from_current:nwc=1:sas=minisat:sac=on:ssfp=10000:ssfq=1.0:smm=sco:ssnc=none:sp=occurrence:tha=off_206");
                quick.push("lrs+1010_2:1_bd=preordered:bs=on:cond=fast:fde=none:gs=on:inw=on:lwlo=on:nwc=1:sas=minisat:stl=60:sos=all:spl=off_216");
            }
            else {
                quick.push("lrs+11_5:1_bd=off:gs=on:gsem=off:gsssp=full:nwc=1.3:sas=minisat:stl=30:sos=all:sac=on:ssac=none:sscc=model:sdd=large:ssfp=4000:ssfq=1.4:ssnc=none:sp=occurrence_3");
                quick.push("lrs+1011_3:1_bsr=unit_only:cond=fast:er=known:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=off:nwc=1:sas=minisat:stl=30:sdd=large:sser=off:sfr=on:ssfp=100000:ssfq=2.0:updr=off_18");
                quick.push("dis+3_3:2_cond=on:fde=none:gs=on:gsem=on:nm=64:nwc=1:sos=on:sac=on:sdd=off:sfr=on:ssfp=10000:ssfq=1.2:smm=off:ssnc=none:sp=occurrence_8");
                quick.push("dis+10_1024_cond=fast:fde=none:gs=on:gsem=off:nwc=1:sd=7:ss=axioms:st=5.0:sos=all:spl=off:sp=reverse_arity_12");
                quick.push("lrs+4_2:1_ep=R:fde=unused:gs=on:nwc=1:stl=30:sos=all:sac=on:ssac=none:sser=off:sfr=on:ssfp=10000:ssfq=1.2:ssnc=none:sp=occurrence:updr=off_14");
                quick.push("dis+1002_6_ccuc=first:cond=fast:gsp=input_only:gs=on:gsaa=from_current:gsem=on:gsssp=full:nm=64:nwc=2.5:nicw=on:sas=minisat:sos=on:ssac=none:sscc=on:sdd=large:sfr=on:ssfp=100000:ssfq=1.2:smm=off:sp=occurrence:urr=ec_only:updr=off_3");
                quick.push("lrs+1002_4_cond=on:er=filter:fde=unused:gsp=input_only:gs=on:gsssp=full:nwc=10:sas=minisat:stl=30:spl=off:sp=occurrence_6");
                quick.push("lrs+1011_4_cond=fast:gs=on:gsaa=from_current:gsem=off:gsssp=full:nm=0:nwc=1:sas=minisat:stl=30:sd=3:ss=axioms:st=2.0:sdd=off:sfr=on:ssfp=100000:ssfq=1.2:smm=off:ssnc=none:sp=reverse_arity_8");
                quick.push("ins+10_1_spl=off_1");
                quick.push("lrs+1_3:1_cond=fast:gsp=input_only:gs=on:gsaa=from_current:gsem=off:nwc=1:stl=30:sd=2:ss=axioms:st=1.2:sos=on:sac=on:sdd=off:sfr=on:ssfp=100000:ssfq=1.2:smm=sco:ssnc=none:sp=reverse_arity_1");
                quick.push("lrs+11_5:4_br=off:cond=on:fde=none:gs=on:gsem=on:gsssp=full:nwc=1:sas=minisat:stl=30:sd=3:ss=axioms:st=3.0:sos=all:sac=on:sser=off:sfr=on:ssfp=1000:ssfq=1.4:ssnc=all:sp=reverse_arity:urr=on:updr=off_3");
                quick.push("dis+1011_1_cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:nm=0:nwc=1:sas=minisat:sd=3:ss=axioms:sos=on:ssac=none:sfr=on:ssfp=100000:ssfq=1.2:smm=sco:ssnc=none:sp=occurrence_2");
                quick.push("lrs+1010_1_bs=unit_only:cond=fast:gs=on:gsem=off:nwc=1:stl=30:sos=all:spl=off_34");
                quick.push("lrs-3_2:1_bsr=unit_only:fde=none:gs=on:gsssp=full:nm=0:nwc=1.5:sas=minisat:stl=30:sos=all:sac=on:smm=sco:ssnc=none:sp=occurrence_12");
                quick.push("lrs+1_5_cond=fast:er=known:fde=unused:gs=on:gsem=on:gsssp=full:nwc=3:sas=minisat:stl=90:sser=off:ssfp=1000:ssfq=1.1:ssnc=none:sp=reverse_arity:updr=off_6");
                quick.push("lrs+11_8:1_br=off:cond=on:fsr=off:fde=none:gs=on:inw=on:lwlo=on:nwc=1.5:stl=30:sser=off:ssfp=10000:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=on_54");
                quick.push("lrs+1002_2:3_br=off:fde=unused:gs=on:gsaa=from_current:gsem=on:gsssp=full:nwc=1:sas=minisat:stl=30:sac=on:sser=off:sfr=on:ssfp=100000:ssfq=2.0:ssnc=none:sp=reverse_arity:urr=on_6");
                quick.push("dis+1010_3:1_cond=fast:fde=unused:gs=on:nwc=1:sd=2:ss=axioms:sos=on:sdd=large:sser=off:sfr=on:ssfp=100000:ssfq=1.2:updr=off_4");
                quick.push("dis+11_5_fsr=off:fde=none:gs=on:gsem=off:gsssp=full:inw=on:inst=on:nwc=1:sser=off:sfr=on:ssfp=10000:ssfq=2.0:ssnc=none:sp=reverse_arity:tha=off_1");
                quick.push("lrs+10_5:4_bsr=unit_only:fde=none:lcm=reverse:nm=64:nwc=10:stl=30:spl=off:sp=occurrence:updr=off_5");
                quick.push("dis+11_7_fde=none:nm=0:nwc=1:sd=3:ss=axioms:st=2.0:spl=off:sp=occurrence:urr=on:updr=off_41");
                quick.push("lrs+1002_2:3_bsr=unit_only:er=known:fde=none:gs=on:gsem=on:nwc=1:sas=minisat:stl=30:sd=1:ss=axioms:st=1.5:sdd=large:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=none:sp=reverse_arity_1");
                quick.push("dis+1010_4:1_cond=fast:fsr=off:nm=0:nwc=1:sas=minisat:sac=on:sdd=large:sfr=on:ssfp=40000:ssfq=2.0:smm=sco:ssnc=none:sp=occurrence:urr=ec_only_11");
                quick.push("dis+11_1_cond=on:fsr=off:lcm=reverse:nwc=2.5:spl=off:sp=reverse_arity:updr=off_4");
                quick.push("ins+11_32_br=off:ep=RSTC:inw=on:igbrr=0.9:igrr=1/32:igrp=100:igrpq=2.0:igs=1004:igwr=on:nwc=1:spl=off:urr=on:updr=off:dm=on_163");
                quick.push("dis+11_3_cond=fast:fsr=off:gs=on:gsem=off:gsssp=full:inw=on:nwc=1.7:sas=minisat:sdd=off:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:sp=occurrence:urr=on:updr=off_7");
                quick.push("lrs+1002_7_ccuc=first:cond=on:fde=none:gs=on:gsssp=full:nwc=1:sas=minisat:stl=90:sd=3:ss=axioms:sscc=model:sser=off:ssfp=1000:ssfq=2.0:ssnc=none:sp=reverse_arity_41");
                quick.push("ott+2_2_cond=fast:fsr=off:gs=on:nwc=1:sd=1:ss=axioms:st=2.0:sos=on:sac=on:sdd=large:sser=off:sfr=on:ssfp=4000:ssfq=1.4:ssnc=none:sp=reverse_arity:urr=on:updr=off_29");
                quick.push("dis+11_4_fde=unused:gs=on:gsaa=from_current:nwc=2.5:sac=on:sdd=large:sser=off:ssfp=100000:ssfq=1.4:ssnc=none_1");
                quick.push("ins+11_5_fde=unused:igpr=on:igrr=1/16:igrp=200:igrpq=1.1:igs=1010:igwr=on:nwc=1:sos=all:spl=off_25");
                quick.push("dis+11_7_278");
                quick.push("ott+11_14_bd=preordered:fsr=off:gs=on:gsem=off:nwc=2:ssfp=4000:ssfq=1.2:smm=off:ssnc=none:sp=reverse_arity:updr=off_8");
                quick.push("dis+11_3_cond=on:ep=RS:er=filter:fsr=off:fde=unused:gs=on:gsem=on:nwc=1:sas=minisat:sd=1:ss=axioms:sac=on:ssfp=4000:ssfq=1.4:smm=off:ssnc=none:sp=occurrence:updr=off_1");
                quick.push("dis+11_5_bd=off:cond=fast:fde=unused:gs=on:gsem=on:lwlo=on:nwc=1:sos=on:sac=on:sdd=off:sser=off:sfr=on:ssfp=10000:ssfq=2.0:ssnc=none:sp=reverse_arity:urr=on_6");
                quick.push("lrs+10_1_bd=off:fde=none:gsp=input_only:lcm=predicate:nm=0:nwc=1:stl=30:sos=on:spl=off:updr=off_3");
                quick.push("lrs+1010_2:1_bd=preordered:bs=on:cond=fast:fde=none:gs=on:inw=on:lwlo=on:nwc=1:sas=minisat:stl=60:sos=all:spl=off_1");
                quick.push("dis+11_4_bsr=unit_only:cond=fast:fde=none:lwlo=on:nm=0:nwc=1.2:spl=off:sp=occurrence_1");
                quick.push("dis-3_10_bsr=unit_only:er=filter:fde=unused:lcm=predicate:nm=64:nwc=1:spl=off:sp=occurrence:updr=off_2");
                quick.push("dis+1011_2_fde=unused:gs=on:nwc=1:sac=on:ssfp=40000:ssfq=1.1:smm=off:ssnc=none:sp=reverse_arity:urr=ec_only_16");
                quick.push("lrs+1010_8:1_fsr=off:fde=none:gs=on:gsem=on:gsssp=full:nwc=1.1:sas=minisat:stl=30:sos=all:ssac=none:sfr=on:ssfp=100000:ssfq=1.0:smm=off:ssnc=all:sp=occurrence:updr=off_137");
                quick.push("ott+11_4:1_bd=off:bsr=unit_only:cond=on:fsr=off:lcm=reverse:nwc=1:sas=minisat:sos=on:spl=off:urr=on:updr=off_23");
                quick.push("dis+1011_4_fde=none:gs=on:nwc=1:sos=on:sdd=off:ssfp=10000:ssfq=1.4:smm=sco:ssnc=none:sp=reverse_arity:updr=off_115");
                quick.push("lrs+10_2_bsr=unit_only:cond=fast:gsp=input_only:gs=on:gsssp=full:lcm=reverse:lwlo=on:nwc=1:sas=minisat:stl=30:sos=on:spl=off:sp=reverse_arity_10");
                quick.push("ott+10_5_cond=fast:fde=none:nwc=1:sas=minisat:sos=all:spl=off:sp=occurrence:updr=off_84");
                quick.push("lrs+4_40_bsr=unit_only:cond=fast:fde=none:gs=on:gsem=on:lwlo=on:nwc=1.2:stl=60:sd=7:ss=axioms:st=5.0:ssac=none:sdd=off:sfr=on:ssfp=1000:ssfq=1.1:smm=sco:ssnc=all_dependent:sp=reverse_arity:tha=off_263");
                quick.push("ins+11_3_bsr=unit_only:fde=none:gs=on:gsem=off:igrr=1/16:igrpq=1.5:igs=1004:igwr=on:lcm=reverse:nm=0:nwc=1:sos=all:spl=off:updr=off:dm=on_126");
                quick.push("ott+1_3:1_cond=fast:gs=on:gsem=off:nwc=1:sas=minisat:sos=all:ssfp=10000:ssfq=1.1:smm=sco:ssnc=none:sp=occurrence:urr=on:updr=off_132");
                quick.push("ins+10_1_igbrr=0.6:igrpq=1.5:igs=1002:nwc=1:spl=off:sp=reverse_arity:tha=off:dm=on_562");
                quick.push("dis+1002_3_cond=fast:er=known:gs=on:gsaa=from_current:gsem=on:gsssp=full:nwc=1:sas=minisat:ssfp=1000:ssfq=1.4:ssnc=all_dependent:sp=occurrence_1");
                quick.push("lrs-11_2_cond=on:fde=unused:gs=on:nwc=3:stl=30:sdd=off:sfr=on:ssfp=100000:ssfq=1.4:smm=sco:ssnc=all_33");
                quick.push("ott+1002_5_bsr=on:fsr=off:fde=none:gs=on:gsem=off:lwlo=on:nwc=1:sscc=on:sser=off:ssfp=100000:ssfq=1.1:sp=occurrence_56");
                quick.push("dis+11_2_fde=none:gsp=input_only:gs=on:gsem=on:nwc=1:sd=2:ss=axioms:st=1.2:sos=all:spl=off:sp=reverse_arity:urr=on:updr=off_110");
                
            }
            break;
            
        case Property::FNE:
            if (atoms > 2000) {
                quick.push("dis+1011_40_bs=on:cond=on:gs=on:gsaa=from_current:nwc=1:sfr=on:ssfp=1000:ssfq=2.0:smm=sco:ssnc=none:updr=off_282");
                quick.push("lrs+1011_3_nwc=1:stl=90:sos=on:spl=off:sp=reverse_arity_133");
                quick.push("dis-10_5_cond=fast:gsp=input_only:gs=on:gsem=off:nwc=1:sas=minisat:sos=all:spl=off:sp=occurrence_190");
                quick.push("lrs+1011_5_cond=fast:gs=on:nwc=2.5:stl=30:sd=3:ss=axioms:sdd=off:sfr=on:ssfp=100000:ssfq=1.0:smm=sco:ssnc=none:sp=occurrence_278");
                quick.push("lrs-3_5:4_bs=on:bsr=on:cond=on:fsr=off:gsp=input_only:gs=on:gsaa=from_current:gsem=on:lcm=predicate:nwc=1.1:nicw=on:sas=minisat:stl=60:sd=3:ss=axioms:sac=on:ssac=none:sfr=on:ssfp=1000:ssfq=1.0:ssnc=all:sp=reverse_arity:urr=ec_only:updr=off_480");
            }
            else if (atoms > 1200) {
                quick.push("lrs+1011_5_cond=fast:gs=on:nwc=2.5:stl=30:sd=3:ss=axioms:sdd=off:sfr=on:ssfp=100000:ssfq=1.0:smm=sco:ssnc=none:sp=occurrence_2");
                quick.push("dis+1011_8_bsr=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:nm=0:nwc=1:sas=minisat:sos=all:sfr=on:ssfp=4000:ssfq=1.1:smm=off:sp=reverse_arity_859");
                quick.push("dis+11_7_gs=on:gsaa=full_model:lcm=predicate:nwc=1.1:sas=minisat:ssac=none:ssfp=1000:ssfq=1.0:smm=sco:sp=reverse_arity:urr=ec_only_878");
                quick.push("ins+11_5_br=off:gs=on:gsem=off:igbrr=0.9:igrr=1/64:igrp=1400:igrpq=1.1:igs=1003:igwr=on:lcm=reverse:nwc=1:spl=off:urr=on:updr=off_1192");
            }
            else {
                quick.push("dis+11_7_16");
                quick.push("dis+1011_5:4_gs=on:gsssp=full:nwc=1.5:sas=minisat:ssac=none:sdd=off:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=all:sp=reverse_arity:updr=off_2");
                quick.push("dis+1011_40_bs=on:cond=on:gs=on:gsaa=from_current:nwc=1:sfr=on:ssfp=1000:ssfq=2.0:smm=sco:ssnc=none:updr=off_14");
                quick.push("dis+11_3_cond=fast:fsr=off:gs=on:gsssp=full:nm=0:nwc=1:sas=minisat:sac=on:sdd=large:ssfp=10000:ssfq=1.2:smm=sco:ssnc=none:sp=occurrence:urr=ec_only_1");
                quick.push("ott-11_4_br=off:cond=on:gs=on:gsem=off:gsssp=full:nwc=5:sas=minisat:sac=on:sdd=large:sfr=on:ssfp=4000:ssfq=2.0:ssnc=all:sp=occurrence:urr=on:updr=off_48");
                quick.push("ott+11_5_bs=on:bsr=on:gs=on:gsem=on:gsssp=full:nwc=1:sdd=off:sfr=on:ssfp=1000:ssfq=2.0:smm=off:ssnc=all:sp=reverse_arity:urr=on:updr=off_19");
                quick.push("lrs+11_8:1_br=off:cond=on:fsr=off:fde=none:gs=on:inw=on:lwlo=on:nwc=1.5:stl=30:sser=off:ssfp=10000:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=on_47");
                quick.push("dis+11_5_cond=fast:fsr=off:gs=on:gsem=on:gsssp=full:nwc=1:sac=on:ssfp=100000:ssfq=1.2:smm=sco:ssnc=none:sp=occurrence:thf=on_1");
                quick.push("lrs+11_2_bd=off:ccuc=first:cond=on:fde=unused:gs=on:gsem=off:nwc=1:stl=30:sos=all:sscc=model:sdd=large:sser=off:ssfp=4000:ssfq=1.1:ssnc=none:sp=occurrence:updr=off_4");
                quick.push("lrs+11_5:1_bd=off:gs=on:gsem=off:gsssp=full:nwc=1.3:sas=minisat:stl=30:sos=all:sac=on:ssac=none:sscc=model:sdd=large:ssfp=4000:ssfq=1.4:ssnc=none:sp=occurrence_12");
                quick.push("dis-10_5_cond=fast:gsp=input_only:gs=on:gsem=off:nwc=1:sas=minisat:sos=all:spl=off:sp=occurrence_7");
                quick.push("dis+11_1_cond=on:fsr=off:lcm=reverse:nwc=2.5:spl=off:sp=reverse_arity:updr=off_74");
                quick.push("dis+1002_128_bs=on:cond=on:gs=on:gsem=on:nm=0:nwc=1:sos=all:spl=off:updr=off_151");
                quick.push("ins+11_5_br=off:gs=on:gsem=off:igbrr=0.9:igrr=1/64:igrp=1400:igrpq=1.1:igs=1003:igwr=on:lcm=reverse:nwc=1:spl=off:urr=on:updr=off_283");
                quick.push("ott+2_8_lcm=reverse:nm=0:nwc=2.5:sser=off:ssfp=4000:ssfq=1.1:ssnc=none:sp=occurrence_775");
                quick.push("dis+1010_28_nwc=1.3:sos=on:spl=off:sp=reverse_arity:updr=off_456");
                quick.push("dis+10_4_cond=fast:fsr=off:nwc=1:sas=minisat:sac=on:sdd=large:ssfp=10000:ssfq=1.1:ssnc=none:sp=occurrence_829");
                quick.push("lrs-10_40_bsr=unit_only:br=off:cond=on:fsr=off:gs=on:gsaa=full_model:inw=on:lcm=reverse:lwlo=on:nwc=2.5:stl=30:sac=on:sdd=large:ssfp=4000:ssfq=1.0:smm=off:ssnc=none:sp=occurrence:urr=on:updr=off_19");
                quick.push("dis+1011_3_cond=on:gs=on:gsssp=full:nwc=1:sas=minisat:spl=off:sp=occurrence_36");
                quick.push("dis+1011_5:1_cond=on:fsr=off:gs=on:gsssp=full:nwc=1:sas=minisat:sac=on:sdd=large:sfr=on:ssfp=40000:ssfq=1.1:ssnc=none:updr=off_177");
            }
            break;
            
        case Property::EPR:
            if (prop == 131072) {
                quick.push("fmb+10_1_sas=minisat_17");
                quick.push("ins+1_1024_bd=preordered:br=off:cond=on:igbrr=0.9:igrr=1/16:igrp=2000:igrpq=2.0:igs=1010:igwr=on:nwc=1:spl=off:sp=occurrence:urr=on:dm=on_154");
                quick.push("ott+2_5_cond=fast:er=filter:fde=none:nwc=1.5:nicw=on:sas=minisat:ssac=none:sdd=large:sfr=on:ssfp=100000:ssfq=2.0:smm=off:sp=reverse_arity:updr=off_215");
                quick.push("ott-11_3:2_bd=off:bs=unit_only:cond=fast:lcm=predicate:nwc=3:spl=off:sp=occurrence_312");
                quick.push("ins+11_1024_bd=off:br=off:cond=fast:fsr=off:fde=none:igbrr=0.9:igpr=on:igrr=1/16:igrp=4000:igrpq=2.0:igs=1004:igwr=on:nwc=1:spl=off:urr=on:dm=on_141");
                quick.push("dis+1003_3_cond=on:fsr=off:nwc=1.7:spl=off:sp=occurrence:updr=off_506");
                quick.push("ins+10_1_fde=none:igbrr=0.7:igrp=4000:igrpq=1.3:igs=1:lcm=reverse:nwc=1.2:spl=off:sp=reverse_arity:dm=on_488");
            }
            else if (prop == 131073) {
                quick.push("ott+2_5_cond=fast:er=filter:fde=none:nwc=1.5:nicw=on:sas=minisat:ssac=none:sdd=large:sfr=on:ssfp=100000:ssfq=2.0:smm=off:sp=reverse_arity:updr=off_225");
                quick.push("ins+11_1024_bd=off:br=off:cond=fast:fsr=off:fde=none:igbrr=0.9:igpr=on:igrr=1/16:igrp=4000:igrpq=2.0:igs=1004:igwr=on:nwc=1:spl=off:urr=on:dm=on_1");
                quick.push("ott+3_5:1_ccuc=small_ones:fsr=off:lcm=predicate:nwc=1.1:sas=minisat:sscc=on:sdd=off:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=ec_only:updr=off_200");
            }
            else if (atoms > 1300) {
                quick.push("dis-1_4_bd=preordered:cond=fast:fde=none:gs=on:gsssp=full:nwc=1:sas=minisat:sac=on:sdd=large:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:sp=reverse_arity:updr=off_46");
                quick.push("fmb+10_1_fmbsr=1.3:nm=0:sas=minisat_81");
                quick.push("dis+1011_128_bd=preordered:br=off:cond=on:nwc=1:sas=minisat:sfr=on:ssfp=40000:ssfq=1.2:ssnc=none:urr=on:updr=off_18");
                quick.push("dis-11_8:1_bd=off:bs=unit_only:cond=fast:gs=on:gsem=off:nwc=1:ssac=none:sscc=on:sdd=large:sfr=on:ssfp=10000:ssfq=1.2:smm=off:ssnc=all_dependent_47");
                quick.push("ins+11_1024_bd=off:br=off:cond=fast:fsr=off:fde=none:igbrr=0.9:igpr=on:igrr=1/16:igrp=4000:igrpq=2.0:igs=1004:igwr=on:nwc=1:spl=off:urr=on:dm=on_250");
                quick.push("ott-11_24_cond=fast:fde=none:gs=on:lcm=predicate:nwc=1:sas=minisat:spl=off:sp=occurrence_19");
                quick.push("dis+10_3:1_bd=preordered:bsr=unit_only:fsr=off:fde=unused:gs=on:nwc=1:sdd=off:ssfp=100000:ssfq=1.2:smm=off:ssnc=none_272");
                quick.push("dis+1_28_bd=preordered:bs=unit_only:br=off:ccuc=small_ones:fsr=off:fde=none:gs=on:gsem=on:nwc=1:sas=minisat:sac=on:sscc=model:sser=off:sfr=on:ssfp=100000:ssfq=1.0:ssnc=all_dependent:sp=reverse_arity:urr=on_76");
                quick.push("dis+10_4:1_bd=off:ccuc=first:fde=none:gs=on:gsem=off:nwc=1:nicw=on:ssac=none:sscc=model:sdd=large:sser=off:sfr=on:ssfp=4000:ssfq=2.0:urr=on:updr=off_97");
                quick.push("dis-4_8_bd=off:fde=unused:gs=on:nwc=1.2:sac=on:sdd=off:sfr=on:ssfp=100000:ssfq=2.0:smm=sco:ssnc=all:urr=ec_only:updr=off_197");
                quick.push("ins+10_40_bd=off:br=off:fde=none:gsp=input_only:igbrr=1.0:igpr=on:igrr=1/32:igrp=1400:igrpq=1.05:igs=1:igwr=on:lcm=reverse:nwc=2.5:spl=off:sp=occurrence:urr=on_331");
                quick.push("dis+2_1_bs=on:bsr=unit_only:ccuc=small_ones:fsr=off:gs=on:gsem=off:gsssp=full:nwc=1:sas=minisat:sac=on:sscc=model:sdd=large:ssnc=none:urr=ec_only_352");
                quick.push("ott+11_5_bd=preordered:bsr=unit_only:cond=fast:fde=none:nwc=1:sas=minisat:ssfp=10000:ssfq=1.2:smm=sco:ssnc=all_dependent:sp=occurrence:updr=off_160");
            }
            else if (atoms > 430) {
                quick.push("dis+11_7_63");
                quick.push("ott+10_3_bd=preordered:bs=on:bsr=unit_only:cond=fast:fde=none:gs=on:lcm=predicate:nwc=2:sas=minisat:spl=off:sp=reverse_arity:urr=on:updr=off_129");
                quick.push("ins+11_14_br=off:cond=on:fsr=off:igbrr=0.9:igrr=1/128:igrp=100:igrpq=1.05:igwr=on:lcm=predicate:nwc=1.7:spl=off:urr=on_536");
                quick.push("ins+10_1_igbrr=0.4:igrp=400:igrpq=2.0:igs=1003:nwc=1.5:spl=off:updr=off:dm=on_854");
                quick.push("ins+10_1_fde=unused:gs=on:igbrr=1.0:igrp=200:igrpq=2.0:igs=1002:lcm=predicate:nwc=3:spl=off:sp=reverse_arity:dm=on_632");
                quick.push("ott+2_5_cond=fast:er=filter:fde=none:nwc=1.5:nicw=on:sas=minisat:ssac=none:sdd=large:sfr=on:ssfp=100000:ssfq=2.0:smm=off:sp=reverse_arity:updr=off_34");
            }
            else {
                quick.push("ott+11_4_bd=preordered:cond=on:fsr=off:nwc=1:sas=minisat:ssnc=none:sp=occurrence:updr=off_1323");
                quick.push("ins+11_50_bd=preordered:br=off:fsr=off:fde=none:gs=on:gsem=off:igbrr=0.5:igpr=on:igrr=1/128:igrp=200:igs=1:igwr=on:nwc=1:spl=off:urr=on:dm=on_444");
                quick.push("ins+10_1_igbrr=0.4:igrp=400:igrpq=2.0:igs=1003:nwc=1.5:spl=off:updr=off:dm=on_549");
            }
            break;
            
        case Property::UEQ:
            if (prop == 2) {
                quick.push("ott+10_40_fde=none:ins=3:nwc=1:spl=off:sp=reverse_arity_147");
                quick.push("lrs+10_4:1_bd=preordered:ins=3:nwc=1:stl=60:spl=off_61");
                quick.push("ott+10_14_ins=3:nwc=2:spl=off:sp=occurrence_475");
                quick.push("lrs+10_24_ins=3:nwc=1:stl=120:spl=off:sp=reverse_arity_773");
                quick.push("ott+10_2_bd=preordered:fde=none:ins=3:nwc=2:spl=off:sp=reverse_arity_219");
                quick.push("ott+10_3:1_fde=none:ins=3:nwc=3:spl=off_243");
                quick.push("ott+10_12_bd=off:ins=3:nwc=1:spl=off:sp=reverse_arity_421");
                quick.push("lrs+10_5:4_ins=3:lwlo=on:nwc=1:stl=90:spl=off:sp=occurrence_678");
                quick.push("dis+10_28_fde=none:ins=3:nwc=4:spl=off_259");
            }
            else if (prop != 0) {
                quick.push("dis+10_128_fde=unused:ins=3:nwc=2.5:spl=off:sp=occurrence_15");
                quick.push("lrs+10_8:1_bd=off:fde=unused:ins=3:nwc=2.5:stl=120:spl=off_146");
                quick.push("lrs+10_10_bd=preordered:fde=unused:ins=3:lwlo=on:nwc=5:stl=60:spl=off:sp=occurrence_128");
                quick.push("ott+10_128_bd=off:ins=3:nwc=1:spl=off:sp=reverse_arity_42");
                quick.push("ott+10_3_bd=off:ins=3:nwc=1:spl=off:sp=reverse_arity_310");
            }
            else if (atoms > 10) {
                quick.push("ott+10_2_bd=preordered:fde=none:ins=3:nwc=2:spl=off:sp=reverse_arity_521");
                quick.push("ott+10_64_bd=off:fde=none:ins=3:nwc=1:spl=off:sp=reverse_arity_889");
                quick.push("lrs+10_4:1_bd=preordered:ins=3:nwc=1:stl=60:spl=off_238");
                quick.push("ott+10_40_fde=none:ins=3:nwc=1:spl=off:sp=reverse_arity_554");
                quick.push("ott+10_8_bd=preordered:ins=3:nwc=1.5:spl=off:sp=occurrence_520");
            }
            else {
                quick.push("lrs+10_5:4_ins=3:lwlo=on:nwc=1:stl=90:spl=off:sp=occurrence_162");
                quick.push("lrs+10_64_fde=none:ins=3:lwlo=on:nwc=1:stl=120:spl=off:sp=occurrence_657");
                quick.push("ott+10_3:1_bd=preordered:ins=3:nwc=5:spl=off_159");
                quick.push("ott+10_5:4_fde=none:ins=3:nwc=1.7:spl=off:sp=occurrence_188");
                quick.push("lrs+10_5:1_fde=unused:ins=3:nwc=1.3:stl=120:spl=off:sp=occurrence_462");
                quick.push("lrs+10_24_ins=3:nwc=1:stl=120:spl=off:sp=reverse_arity_960");
            }
            break;
    }
    
    switch (cat) {
        case Property::HEQ:
        case Property::PEQ:
        case Property::NEQ:
        case Property::HNE:
        case Property::NNE:
            fallback.push("dis+11_7_300");
            fallback.push("lrs-11_3:1_bd=off:ccuc=small_ones:cond=fast:gs=on:gsaa=from_current:nwc=1:sas=minisat:sos=all:sscc=on:sdd=large:sser=off:ssfp=40000:ssfq=1.0:ssnc=none:sp=reverse_arity:updr=off_300");
            fallback.push("dis+11_4_fde=unused:gs=on:gsem=on:gsssp=full:igrpq=1.0:lcm=reverse:lwlo=on:nwc=4:sas=minisat:sdd=off:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=none:sp=reverse_arity_300");
            fallback.push("dis+2_5_cond=fast:igrpq=1.0:nwc=1:sos=all:spl=off:sp=occurrence:updr=off_300");
            fallback.push("lrs+11_1_bsr=unit_only:cond=on:fsr=off:gs=on:gsem=on:lwlo=on:nwc=2:sas=minisat:spl=off_900");
            fallback.push("lrs+2_4:1_fsr=off:fde=none:gsp=input_only:lcm=predicate:lwlo=on:nwc=1.2:spl=off:sp=occurrence:urr=ec_only:updr=off_900");
            fallback.push("ins+11_4_cond=fast:fsr=off:igbrr=0.8:igpr=on:igrr=1/8:igrp=200:igrpq=1.5:igs=1003:igwr=on:nwc=10:spl=off:sp=occurrence:updr=off_300");
            fallback.push("lrs+11_5:4_bd=off:cond=on:fde=unused:nwc=3:spl=off:sp=occurrence:updr=off_300");
            fallback.push("lrs+10_3:1_bs=on:bsr=unit_only:gs=on:gsem=off:gsssp=full:lwlo=on:nwc=1:sas=minisat:spl=off:sp=reverse_arity:updr=off_2400");
            fallback.push("lrs+1010_10_bd=off:fsr=off:fde=none:nwc=4:sas=minisat:ssac=none:sdd=off:sser=off:ssfp=4000:ssfq=1.4:sp=occurrence:urr=ec_only:updr=off_300");
            fallback.push("lrs+11_3:1_bd=off:fde=none:gs=on:lwlo=on:nwc=2:sas=minisat:sac=on:sdd=off:sfr=on:ssfp=4000:ssfq=1.4:smm=sco:ssnc=none:sp=occurrence_900");
            fallback.push("dis+11_5_gs=on:gsem=on:nwc=1:sd=1:ss=axioms:st=3.0:sac=on:sdd=large:ssfp=1000:ssfq=2.0:smm=sco:ssnc=none:sp=occurrence_300");
            fallback.push("dis+11_2:3_cond=on:er=known:gs=on:igrpq=1.0:nwc=1.5:sdd=off:sfr=on:ssfp=4000:ssfq=2.0:ssnc=none_300");
            fallback.push("lrs+1002_3:1_bs=unit_only:cond=on:gsp=input_only:igrpq=1.0:nwc=10:sas=minisat:sac=on:ssac=none:sfr=on:ssfp=4000:ssfq=1.0:smm=off:ssnc=none:sp=occurrence_300");
            fallback.push("lrs+11_2:1_bs=unit_only:bsr=unit_only:fsr=off:fde=none:gsp=input_only:lcm=reverse:lwlo=on:nwc=1:sos=on:spl=off:urr=ec_only_600");
            fallback.push("lrs+1011_10_cond=on:gsp=input_only:igrpq=1.0:nwc=1.5:spl=off:sp=occurrence:updr=off_300");
            fallback.push("dis+11_5_cond=on:gs=on:gsem=on:igrpq=1.0:nwc=1:sos=on:sac=on:sdd=large:ssfp=4000:ssfq=1.1:smm=sco:ssnc=none:sp=occurrence:updr=off_300");
            fallback.push("dis+11_3:2_bs=unit_only:cond=on:fde=unused:lcm=reverse:nwc=1:sos=all:spl=off_300");
            fallback.push("ins+11_3_cond=on:igbrr=0.5:igrr=1/16:igrp=4000:igrpq=1.1:igs=1:igwr=on:nwc=4:spl=off:sp=reverse_arity:dm=on_300");
            fallback.push("dis+1003_50_cond=fast:igrpq=1.0:nwc=1:sos=on:spl=off:sp=occurrence_300");
            fallback.push("dis+1002_3_bsr=unit_only:cond=on:nwc=1.2:nicw=on:sos=all:sdd=large:sser=off:sp=occurrence:updr=off_300");
            fallback.push("ins+4_3_bsr=unit_only:fde=unused:igrr=1/2:igrp=2000:igrpq=2.0:igs=1002:igwr=on:lcm=predicate:nwc=1:sd=7:ss=axioms:st=1.2:sos=all:spl=off:sp=reverse_arity:dm=on_300");
            fallback.push("dis+11_64_fsr=off:gsp=input_only:nwc=1.1:sos=all:spl=off:sp=occurrence:updr=off_300");
            fallback.push("ott+1011_2_er=known:fde=none:nwc=1:spl=off:sp=occurrence_300");
            fallback.push("dis+1011_2_cond=on:ep=RST:gs=on:gsem=on:igrpq=1.0:nwc=1:sac=on:ssfp=100000:ssfq=1.1:smm=off:ssnc=none:urr=ec_only_300");
            fallback.push("ott+1004_5:1_bd=off:bsr=unit_only:cond=fast:fsr=off:nwc=1:sos=all:spl=off_300");
            fallback.push("lrs+11_14_bs=unit_only:bsr=unit_only:cond=on:igrpq=1.0:nwc=1:sas=minisat:sdd=off:sser=off:ssfp=1000:ssfq=1.1:ssnc=none:sp=occurrence_300");
            fallback.push("dis+1_64_gsp=input_only:nwc=1.2:sos=all:spl=off:sp=occurrence:updr=off_300");
            fallback.push("ott+11_24_bd=off:bsr=unit_only:fsr=off:gs=on:gsaa=full_model:gsem=off:gsssp=full:nwc=3:sdd=off:sfr=on:ssfp=4000:ssfq=1.1:ssnc=none:sp=occurrence_300");
            fallback.push("ins+10_4_cond=on:fsr=off:fde=none:igbrr=0.6:igrr=1/32:igrp=2000:igrpq=1.05:igs=1002:igwr=on:nwc=5:spl=off:sp=occurrence:updr=off:dm=on_300");
            fallback.push("lrs+11_2:3_cond=on:gs=on:gsem=on:igrpq=1.0:lwlo=on:nwc=1.7:sas=minisat:spl=off:updr=off_300");
            fallback.push("dis+1011_2_nwc=1:sas=minisat:sos=on:spl=off:sp=occurrence_300");
            fallback.push("ott+1003_3:1_bsr=unit_only:fsr=off:fde=unused:gs=on:gsem=on:igrpq=1.0:nwc=10:sac=on:sdd=large:sfr=on:ssfp=40000:ssfq=1.0:smm=sco:ssnc=none:urr=on_300");
            fallback.push("lrs+10_10_er=known:fde=none:gs=on:gsem=on:igrpq=1.0:nwc=1.7:spl=off:updr=off_300");
            fallback.push("dis+1010_4_bs=unit_only:cond=fast:fsr=off:fde=unused:nwc=1:sos=on:sdd=off:sfr=on:ssfp=10000:ssfq=2.0:sp=reverse_arity:updr=off_300");
            fallback.push("lrs+2_7_bs=unit_only:bsr=unit_only:cond=on:fsr=off:gs=on:nwc=1.7:sas=minisat:sos=on:sac=on:sfr=on:ssfp=100000:ssfq=1.0:smm=off:ssnc=all_dependent_300");
            fallback.push("lrs+1011_128_bsr=unit_only:cond=fast:lwlo=on:nwc=2:sos=all:spl=off:urr=on:updr=off_300");
            fallback.push("lrs+1_20_bs=on:cond=fast:gs=on:gsem=on:nwc=1.1:sdd=off:sser=off:sfr=on:ssfp=100000:ssfq=2.0:ssnc=none:sp=reverse_arity:updr=off_600");
            fallback.push("ins+11_5_ep=RST:fsr=off:fde=none:gs=on:gsem=on:igbrr=0.8:igpr=on:igrr=1/32:igrp=200:igrpq=1.5:igs=1010:igwr=on:nwc=1:sas=minisat:sos=on:spl=off:dm=on_300");
            fallback.push("dis+11_5:4_cond=fast:fsr=off:igrpq=1.0:nwc=10:spl=off_300");
            fallback.push("ins+11_5_cond=fast:gsp=input_only:igbrr=0.7:igrr=1/4:igs=1003:igwr=on:lcm=reverse:nwc=1:sos=all:spl=off:urr=ec_only_300");
            fallback.push("lrs+11_2_bd=off:fsr=off:gs=on:gsaa=full_model:gsem=off:gsssp=full:igrpq=1.0:lcm=reverse:nwc=1:sas=minisat:sos=on:sdd=large:sfr=on:ssfp=4000:ssfq=2.0:smm=sco:ssnc=none:updr=off_300");
            fallback.push("lrs+1011_8_bd=preordered:cond=on:fsr=off:fde=none:gs=on:gsssp=full:igrpq=1.0:lcm=reverse:nwc=1.7:sas=minisat:spl=off:sp=reverse_arity:urr=ec_only_300");
            fallback.push("dis+10_4_bsr=unit_only:gs=on:gsssp=full:nwc=1.5:nicw=on:sas=minisat:sfr=on:ssfp=4000:ssfq=1.2:smm=off:sp=reverse_arity:updr=off_300");
            fallback.push("lrs+11_5:4_bsr=unit_only:ccuc=small_ones:cond=on:fsr=off:igrpq=1.0:nwc=1:sas=minisat:sac=on:sscc=on:sdd=off:ssfp=40000:ssfq=2.0:ssnc=none:sp=reverse_arity_300");
            fallback.push("dis+11_4_cond=fast:ep=R:gs=on:gsaa=from_current:gsem=on:igrpq=1.0:nwc=1:sas=minisat:ssfp=1000:ssfq=1.4:smm=sco:ssnc=none:sp=occurrence:updr=off_300");
            fallback.push("dis-2_5_cond=on:igrpq=1.0:nwc=1:sas=minisat:spl=off:sp=occurrence_300");
            fallback.push("dis+11_5:4_fsr=off:fde=none:gs=on:gsem=off:nwc=1:sac=on:sdd=off:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=none:urr=on_300");
            fallback.push("dis+11_8:1_br=off:cond=fast:fsr=off:igrpq=1.0:nwc=1:sos=all:sdd=off:sser=off:sfr=on:ssfp=40000:ssfq=1.1:ssnc=none:sp=occurrence:urr=on:updr=off_300");
            fallback.push("dis+1010_24_cond=fast:ep=RS:fde=unused:lwlo=on:nwc=1.5:sas=minisat:sser=off:sfr=on:ssfp=1000:ssfq=1.1:ssnc=none_300");
            fallback.push("lrs+1011_3_cond=on:fsr=off:fde=none:gs=on:gsssp=full:igrpq=1.0:nwc=1:sos=all:spl=off:sp=reverse_arity:updr=off_300");
            fallback.push("dis+1011_2_bs=unit_only:cond=fast:er=filter:fsr=off:fde=unused:nwc=2.5:ssac=none:ssfp=4000:ssfq=1.0:smm=off:sp=occurrence:updr=off_300");
            fallback.push("dis+3_64_cond=fast:igrpq=1.0:lcm=reverse:nwc=1.1:sos=on:spl=off:updr=off_300");
            fallback.push("lrs+11_1024_bd=off:fsr=off:gs=on:gsem=on:nwc=1:spl=off:sp=occurrence:urr=on_300");
            fallback.push("ott+10_8_bsr=unit_only:gs=on:gsaa=from_current:gsem=on:nwc=4:sas=minisat:sfr=on:ssfp=4000:ssfq=1.4:smm=off:ssnc=all_600");
            fallback.push("lrs+1004_28_nwc=1.1:sos=all:spl=off_600");
            fallback.push("lrs+11_10_gs=on:gsem=on:igrpq=1.0:lcm=reverse:nwc=1:sac=on:sfr=on:ssfp=10000:ssfq=1.0:ssnc=none:updr=off_300");
            fallback.push("dis+1010_6_bd=off:bsr=unit_only:ccuc=first:cond=fast:fsr=off:fde=unused:igrpq=1.0:lwlo=on:nwc=1:sas=minisat:sos=on:sac=on:sscc=model:sdd=large:sser=off:ssfp=1000:ssfq=1.1:ssnc=all_dependent_300");
            fallback.push("dis+10_2:3_fde=unused:igrpq=1.0:lcm=predicate:nwc=1:sas=minisat:sos=all:sac=on:sdd=off:sfr=on:ssfp=100000:ssfq=1.0:smm=off:ssnc=none:sp=reverse_arity_300");
            fallback.push("dis+11_2_cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:igrpq=1.0:nwc=5:sac=on:ssac=none:sfr=on:ssfp=4000:ssfq=1.4:smm=off:ssnc=none:sp=reverse_arity_300");
            fallback.push("dis+11_4_fsr=off:fde=none:gs=on:gsaa=from_current:igrpq=1.0:nwc=1:sfr=on:ssfp=1000:ssfq=2.0:ssnc=none:urr=on:updr=off_300");
            fallback.push("dis+1002_10_bsr=unit_only:cond=fast:nwc=1:sos=all:spl=off:sp=occurrence_300");
            fallback.push("lrs+11_5:4_bd=off:gsp=input_only:gs=on:gsem=on:lcm=predicate:nwc=1:sas=minisat:sos=all:spl=off:sp=occurrence:urr=on_300");
            fallback.push("lrs+11_1_bs=on:nwc=1.1:spl=off:sp=occurrence:urr=ec_only:updr=off_300");
            fallback.push("ins+4_4_fsr=off:fde=none:igbrr=0.8:igpr=on:igrr=1/8:igrpq=1.0:igs=1002:igwr=on:nwc=1:sos=all:spl=off:sp=reverse_arity:urr=ec_only:dm=on_300");
            fallback.push("ott+11_5:4_cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=off:nwc=1:sos=all:sdd=large:sfr=on:ssfp=10000:ssfq=2.0:ssnc=none:sp=occurrence:updr=off_300");
            fallback.push("dis+1011_2:1_cond=fast:gsp=input_only:gs=on:nwc=1:sas=minisat:sos=all:spl=off_300");
            fallback.push("lrs+11_3_fsr=off:gs=on:gsssp=full:nwc=2:spl=off:sp=occurrence:urr=on:updr=off_600");
            fallback.push("lrs-1_3_fsr=off:gs=on:gsaa=from_current:gsem=on:lwlo=on:nwc=1.2:sas=minisat:sac=on:sdd=off:sfr=on:ssfp=4000:ssfq=2.0:smm=sco:ssnc=none:sp=reverse_arity_300");
            fallback.push("dis+1004_3_fsr=off:fde=none:nwc=1:sas=minisat:sd=1:ss=axioms:st=1.5:sos=all:spl=off:sp=reverse_arity_300");
            fallback.push("dis+1_20_bs=unit_only:fsr=off:gs=on:gsem=on:gsssp=full:nwc=1.7:sas=minisat:spl=off:sp=occurrence_300");
            fallback.push("dis+10_3_gs=on:gsem=on:gsssp=full:igrpq=1.0:nwc=1:sas=minisat:sd=3:ss=axioms:sos=all:sdd=off:sfr=on:ssfp=4000:ssfq=1.0:smm=sco:ssnc=none:updr=off_300");
            fallback.push("lrs+11_4_bs=unit_only:cond=fast:fde=none:gs=on:igrpq=1.0:lwlo=on:nwc=1:ssfp=1000:ssfq=1.2:ssnc=none:sp=occurrence_300");
            fallback.push("dis+10_24_gs=on:igrpq=1.0:nwc=1:sas=minisat:sd=3:ss=axioms:sos=on:spl=off:sp=reverse_arity:updr=off_300");
            fallback.push("dis+2_12_fsr=off:lcm=reverse:nwc=3:spl=off:sp=reverse_arity:updr=off_300");
            fallback.push("lrs+1002_3:1_bd=off:bsr=unit_only:fde=none:gs=on:gsem=on:nwc=1:sd=1:ss=axioms:spl=off:sp=occurrence_300");
            fallback.push("lrs+11_5_cond=fast:er=filter:igrpq=1.0:nwc=1:sos=all:spl=off:urr=ec_only_300");
            fallback.push("dis+11_64_bs=unit_only:cond=on:fde=none:igrpq=1.0:nwc=2:spl=off:updr=off_300");
            fallback.push("lrs+10_5_bd=preordered:cond=on:fde=none:igrpq=1.0:lcm=reverse:lwlo=on:nwc=1.7:spl=off:sp=occurrence_300");
            fallback.push("dis+11_5_fsr=off:gs=on:gsem=off:igrpq=1.0:lwlo=on:nwc=1:sos=all:spl=off:sp=reverse_arity_300");
            fallback.push("lrs+10_4_cond=fast:nwc=1:nicw=on:sas=minisat:sfr=on:ssfp=10000:ssfq=1.2:smm=off_600");
            fallback.push("lrs+1003_5_bd=off:bsr=on:cond=on:fsr=off:fde=none:gsp=input_only:lwlo=on:nwc=1:sos=all:spl=off:sp=reverse_arity_300");
            fallback.push("lrs+2_50_bs=unit_only:bsr=unit_only:cond=fast:fsr=off:igrpq=1.0:nwc=1:spl=off:sp=occurrence_300");
            fallback.push("dis+1_3_cond=on:fsr=off:nwc=1.1:sas=minisat:spl=off:sp=reverse_arity:urr=ec_only:updr=off_300");
            fallback.push("dis+1002_3_fsr=off:gs=on:gsaa=from_current:gsem=on:igrpq=1.0:nwc=1:sos=on:sac=on:sfr=on:ssfp=1000:ssfq=1.2:smm=off:ssnc=none:updr=off_300");
            fallback.push("lrs+11_128_bs=unit_only:fde=unused:gs=on:gsem=off:gsssp=full:igrpq=1.0:nwc=1:nicw=on:sas=minisat:sos=on:sac=on:ssac=none:sdd=large:sfr=on:ssfp=40000:ssfq=1.1:smm=sco:ssnc=all_1200");
            fallback.push("dis+1_64_bs=unit_only:cond=fast:fde=none:gs=on:gsaa=from_current:gsem=off:igrpq=1.0:nwc=3:nicw=on:sas=minisat:sos=on:sac=on:sdd=large:sfr=on:ssfp=40000:ssfq=1.4:smm=off:ssnc=all_dependent:sp=reverse_arity:updr=off_600");
            break;
            
        case Property::EPR:
            fallback.push("ott+11_5_bd=preordered:bsr=unit_only:cond=fast:fde=none:igrpq=1.0:nwc=1:sas=minisat:ssfp=10000:ssfq=1.2:smm=sco:ssnc=all_dependent:sp=occurrence:updr=off_300");
            fallback.push("ins+1_1024_bd=preordered:br=off:cond=on:igbrr=0.9:igrr=1/16:igrp=2000:igrpq=2.0:igs=1010:igwr=on:nwc=1:spl=off:sp=occurrence:urr=on:dm=on_300");
            fallback.push("fmb+10_1_sas=minisat_3000");
            fallback.push("dis+10_2:1_bd=preordered:fsr=off:gs=on:gsem=off:igrpq=1.0:nwc=1.1:sas=minisat:ssac=none:sdd=large:sfr=on:ssfp=40000:ssfq=2.0:sp=reverse_arity:urr=ec_only:updr=off_300");
            fallback.push("ott+2_5_cond=fast:er=filter:fde=none:igrpq=1.0:nwc=1.5:nicw=on:sas=minisat:ssac=none:sdd=large:sfr=on:ssfp=100000:ssfq=2.0:smm=off:sp=reverse_arity:updr=off_300");
            fallback.push("ott+11_4_bd=preordered:cond=on:fsr=off:igrpq=1.0:nwc=1:sas=minisat:ssnc=none:sp=occurrence:updr=off_1500");
            fallback.push("ott+10_3_bd=preordered:bs=on:bsr=unit_only:cond=fast:fde=none:gs=on:igrpq=1.0:lcm=predicate:nwc=2:sas=minisat:spl=off:sp=reverse_arity:urr=on:updr=off_300");
            fallback.push("dis+1003_3_cond=on:fsr=off:igrpq=1.0:nwc=1.7:spl=off:sp=occurrence:updr=off_600");
            fallback.push("ins+10_1_igbrr=0.4:igrp=400:igrpq=2.0:igs=1003:nwc=1.5:spl=off:updr=off:dm=on_1200");
            fallback.push("ins+10_40_bd=off:br=off:fde=none:gsp=input_only:igbrr=1.0:igpr=on:igrr=1/32:igrp=1400:igrpq=1.05:igs=1:igwr=on:lcm=reverse:nwc=2.5:spl=off:sp=occurrence:urr=on_600");
            fallback.push("ott-11_24_cond=fast:fde=none:gs=on:igrpq=1.0:lcm=predicate:nwc=1:sas=minisat:spl=off:sp=occurrence_300");
            fallback.push("dis-11_8:1_bd=off:bs=unit_only:cond=fast:gs=on:gsem=off:igrpq=1.0:nwc=1:ssac=none:sscc=on:sdd=large:sfr=on:ssfp=10000:ssfq=1.2:smm=off:ssnc=all_dependent_300");
            fallback.push("dis-1_4_bd=preordered:cond=fast:fde=none:gs=on:gsssp=full:igrpq=1.0:nwc=1:sas=minisat:sac=on:sdd=large:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:sp=reverse_arity:updr=off_300");
            fallback.push("dis-4_8_bd=off:fde=unused:gs=on:igrpq=1.0:nwc=1.2:sac=on:sdd=off:sfr=on:ssfp=100000:ssfq=2.0:smm=sco:ssnc=all:urr=ec_only:updr=off_300");
            fallback.push("ins+11_1024_bd=preordered:br=off:cond=fast:gs=on:igbrr=1.0:igpr=on:igrr=1/64:igrp=700:igrpq=2.0:igs=1:igwr=on:lcm=predicate:nwc=1.7:spl=off:sp=occurrence:urr=on:updr=off_300");
            fallback.push("dis+1011_128_bd=preordered:br=off:cond=on:igrpq=1.0:nwc=1:sas=minisat:sfr=on:ssfp=40000:ssfq=1.2:ssnc=none:urr=on:updr=off_300");
            fallback.push("dis+10_4:1_bd=off:ccuc=first:fde=none:gs=on:gsem=off:nwc=1:nicw=on:ssac=none:sscc=model:sdd=large:sser=off:sfr=on:ssfp=4000:ssfq=2.0:urr=on:updr=off_300");
            fallback.push("dis+10_3:1_bd=preordered:bsr=unit_only:fsr=off:fde=unused:gs=on:igrpq=1.0:nwc=1:sdd=off:ssfp=100000:ssfq=1.2:smm=off:ssnc=none_300");
            fallback.push("ins+11_1024_bd=off:br=off:cond=fast:fsr=off:fde=none:igbrr=0.9:igpr=on:igrr=1/16:igrp=4000:igrpq=2.0:igs=1004:igwr=on:nwc=1:spl=off:urr=on:dm=on_300");
            fallback.push("ins+11_14_br=off:cond=on:fsr=off:igbrr=0.9:igrr=1/128:igrp=100:igrpq=1.05:igwr=on:lcm=predicate:nwc=1.7:spl=off:urr=on_600");
            fallback.push("ins+11_50_bd=preordered:br=off:fsr=off:fde=none:gs=on:gsem=off:igbrr=0.5:igpr=on:igrr=1/128:igrp=200:igrpq=1.0:igs=1:igwr=on:nwc=1:spl=off:urr=on:dm=on_600");
            fallback.push("dis+2_1_bs=on:bsr=unit_only:ccuc=small_ones:fsr=off:gs=on:gsem=off:gsssp=full:igrpq=1.0:nwc=1:sas=minisat:sac=on:sscc=model:sdd=large:ssnc=none:urr=ec_only_600");
            fallback.push("ott-11_3:2_bd=off:bs=unit_only:cond=fast:igrpq=1.0:lcm=predicate:nwc=3:spl=off:sp=occurrence_600");
            fallback.push("ins+10_1_fde=unused:gs=on:igbrr=1.0:igrp=200:igrpq=2.0:igs=1002:lcm=predicate:nwc=3:spl=off:sp=reverse_arity:dm=on_900");
            break;
            
        case Property::UEQ:
            fallback.push("lrs+10_5:4_ins=3:igrpq=1.0:lwlo=on:nwc=1:spl=off:sp=occurrence_900");
            fallback.push("lrs+10_14_fde=none:ins=3:igrpq=1.0:nwc=3:spl=off:sp=reverse_arity_900");
            fallback.push("ott+10_14_ins=3:nwc=2:spl=off:sp=occurrence_600");
            fallback.push("ott+10_64_bd=off:fde=none:ins=3:nwc=1:spl=off:sp=reverse_arity_900");
            fallback.push("lrs+10_10_bd=preordered:fde=unused:ins=3:igrpq=1.0:lwlo=on:nwc=5:spl=off:sp=occurrence_600");
            fallback.push("lrs+10_4:1_bd=preordered:ins=3:igrpq=1.0:nwc=1:spl=off_600");
            fallback.push("ott+10_2_bd=preordered:fde=none:ins=3:nwc=2:spl=off:sp=reverse_arity_600");
            fallback.push("ott+10_40_fde=none:ins=3:nwc=1:spl=off:sp=reverse_arity_600");
            fallback.push("ott+10_4_bd=preordered:ins=3:nwc=5:spl=off:sp=occurrence_600");
            fallback.push("lrs+10_24_ins=3:igrpq=1.0:nwc=1:spl=off:sp=reverse_arity_1200");
            fallback.push("ott+10_3:1_fde=none:ins=3:nwc=3:spl=off_300");
            fallback.push("ott+10_5:4_fde=none:ins=3:nwc=1.7:spl=off:sp=occurrence_300");
            fallback.push("lrs+10_8:1_bd=off:fde=unused:ins=3:nwc=2.5:spl=off_1200");
            fallback.push("lrs+10_5:1_fde=unused:ins=3:nwc=1.3:spl=off:sp=occurrence_1200");
            fallback.push("ott+10_12_bd=off:ins=3:igrpq=1.0:nwc=1:spl=off:sp=reverse_arity_600");
            fallback.push("ott+10_8_bd=preordered:ins=3:nwc=1.5:spl=off:sp=occurrence_600");
            fallback.push("lrs+10_64_fde=none:ins=3:lwlo=on:nwc=1:spl=off:sp=occurrence_1200");
            break;
            
        case Property::FEQ:
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
            break;
            
        case Property::FNE:
            fallback.push("dis+11_7_300");
            fallback.push("dis+1011_40_bs=on:cond=on:gs=on:gsaa=from_current:igrpq=1.0:nwc=1:sfr=on:ssfp=1000:ssfq=2.0:smm=sco:ssnc=none:updr=off_600");
            fallback.push("lrs+11_8:1_br=off:cond=on:fsr=off:fde=none:gs=on:inw=on:igrpq=1.0:lwlo=on:nwc=1.5:sser=off:ssfp=10000:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=on_300");
            fallback.push("dis+1011_5:4_gs=on:gsssp=full:igrpq=1.0:nwc=1.5:sas=minisat:ssac=none:sdd=off:sfr=on:ssfp=40000:ssfq=1.4:smm=sco:ssnc=all:sp=reverse_arity:updr=off_300");
            fallback.push("dis-10_5_cond=fast:gsp=input_only:gs=on:gsem=off:igrpq=1.0:nwc=1:sas=minisat:sos=all:spl=off:sp=occurrence_300");
            fallback.push("lrs+11_5:1_bd=off:gs=on:gsem=off:gsssp=full:nwc=1.3:sas=minisat:sos=all:sac=on:ssac=none:sscc=model:sdd=large:ssfp=4000:ssfq=1.4:ssnc=none:sp=occurrence_300");
            fallback.push("ins+11_5_br=off:gs=on:gsem=off:igbrr=0.9:igrr=1/64:igrp=1400:igrpq=1.1:igs=1003:igwr=on:lcm=reverse:nwc=1:spl=off:urr=on:updr=off_1200");
            fallback.push("ott+2_8_lcm=reverse:nm=0:nwc=2.5:sser=off:ssfp=4000:ssfq=1.1:ssnc=none:sp=occurrence_900");
            fallback.push("ott+11_5_bs=on:bsr=on:gs=on:gsem=on:gsssp=full:igrpq=1.0:nwc=1:sdd=off:sfr=on:ssfp=1000:ssfq=2.0:smm=off:ssnc=all:sp=reverse_arity:urr=on:updr=off_300");
            fallback.push("dis+11_5_cond=fast:fsr=off:gs=on:gsem=on:gsssp=full:nwc=1:sac=on:ssfp=100000:ssfq=1.2:smm=sco:ssnc=none:sp=occurrence:thf=on_300");
            fallback.push("dis+11_1_cond=on:fsr=off:igrpq=1.0:lcm=reverse:nwc=2.5:spl=off:sp=reverse_arity:updr=off_300");
            fallback.push("lrs+1011_3_igrpq=1.0:nwc=1:sos=on:spl=off:sp=reverse_arity_900");
            fallback.push("dis+1002_128_bs=on:cond=on:gs=on:gsem=on:igrpq=1.0:nm=0:nwc=1:sos=all:spl=off:updr=off_300");
            fallback.push("lrs+1011_5_cond=fast:gs=on:igrpq=1.0:nwc=2.5:sd=3:ss=axioms:sdd=off:sfr=on:ssfp=100000:ssfq=1.0:smm=sco:ssnc=none:sp=occurrence_300");
            fallback.push("ott-11_4_br=off:cond=on:gs=on:gsem=off:gsssp=full:igrpq=1.0:nwc=5:sas=minisat:sac=on:sdd=large:sfr=on:ssfp=4000:ssfq=2.0:ssnc=all:sp=occurrence:urr=on:updr=off_300");
            fallback.push("dis+1010_28_nwc=1.3:sos=on:spl=off:sp=reverse_arity:updr=off_600");
            fallback.push("lrs-3_5:4_bs=on:bsr=on:cond=on:fsr=off:gsp=input_only:gs=on:gsaa=from_current:gsem=on:lcm=predicate:nwc=1.1:nicw=on:sas=minisat:sd=3:ss=axioms:sac=on:ssac=none:sfr=on:ssfp=1000:ssfq=1.0:ssnc=all:sp=reverse_arity:urr=ec_only:updr=off_600");
            fallback.push("dis+1011_8_bsr=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:nm=0:nwc=1:sas=minisat:sos=all:sfr=on:ssfp=4000:ssfq=1.1:smm=off:sp=reverse_arity_1200");
            fallback.push("dis+10_4_cond=fast:fsr=off:igrpq=1.0:nwc=1:sas=minisat:sac=on:sdd=large:ssfp=10000:ssfq=1.1:ssnc=none:sp=occurrence_900");
            fallback.push("dis+11_7_gs=on:gsaa=full_model:lcm=predicate:nwc=1.1:sas=minisat:ssac=none:ssfp=1000:ssfq=1.0:smm=sco:sp=reverse_arity:urr=ec_only_1200");
            break;
    }
    
    // add very long final fallback strategy
    fallback.push("dis+11_1_3600");
    
} // getSchedule


#endif //!COMPILER_MSVC
