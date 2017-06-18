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
    time=10;
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
    case SMT_UFNIA:
      quick.push("lrs+11_5:4_av=off:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=32:newcnf=on:nwc=1.3:stl=30:sp=reverse_arity:updr=off_72");
      quick.push("dis+1010_1_afr=on:afp=40000:afq=2.0:amm=off:anc=none:gs=on:ile=on:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off_10");
      quick.push("lrs+1011_3:1_add=off:afr=on:afp=4000:afq=2.0:amm=off:anc=none:bce=on:ep=RS:gs=on:ile=on:lma=on:nm=64:newcnf=on:nwc=1.2:stl=30:sp=occurrence:tha=off_8");
      quick.push("dis+11_2_afp=40000:afq=2.0:amm=off:anc=none:cond=on:fsr=off:gs=on:gsem=off:inw=on:nm=64:newcnf=on:nwc=1:sas=z3:sp=occurrence:updr=off_12");
      quick.push("lrs+2_8:1_add=off:afp=40000:afq=1.0:anc=none:fde=unused:gs=on:ile=on:irw=on:lcm=reverse:nm=64:nwc=3:sas=z3:stl=30:sp=occurrence:urr=on:uhcvi=on_13");
      quick.push("dis+1011_8_av=off:bd=off:bsr=on:bce=on:cond=on:fsr=off:fde=unused:ile=on:nm=64:nwc=1.1:sd=10:ss=axioms:st=1.5:sos=all:sp=reverse_arity:tha=off_569");
      quick.push("dis+1010_2:1_afp=40000:afq=1.1:anc=none:gsp=input_only:ile=on:irw=on:nm=6:nwc=1:sac=on:tha=off:updr=off_9");
      quick.push("lrs+1002_8_afp=10000:afq=2.0:amm=sco:anc=none:bs=on:cond=on:fsr=off:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1.3:sas=z3:stl=30:sp=reverse_arity:urr=on_37");
      quick.push("lrs+1002_1_av=off:bd=off:bsr=on:cond=on:ile=on:lma=on:nm=64:nwc=1:stl=30:sos=on:sp=reverse_arity_7");
      quick.push("dis+10_3_add=large:afp=4000:afq=1.4:amm=off:anc=none:cond=on:ep=RS:gs=on:gsaa=from_current:inw=on:ile=on:lma=on:nm=2:newcnf=on:nwc=1:sac=on:tha=off:updr=off_3");
      quick.push("ott+1010_7_av=off:fsr=off:fde=none:lma=on:nm=2:newcnf=on:nwc=1.3:sos=on:sp=reverse_arity:uhcvi=on_183");
      quick.push("lrs-11_4:1_aac=none:add=off:afp=10000:afq=1.2:anc=none:fsr=off:ile=on:lma=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:urr=on:updr=off_16");
      quick.push("ott+1002_5:1_add=large:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:br=off:cond=on:fsr=off:gs=on:inw=on:irw=on:lma=on:nm=0:newcnf=on:nwc=1:nicw=on:sos=all:tha=off:urr=on_74");
      quick.push("lrs+1010_1_add=off:afp=40000:afq=1.1:amm=off:anc=none:bd=off:fsr=off:inw=on:ile=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30:sp=occurrence_158");
      quick.push("lrs+1004_5:1_av=off:cond=on:fde=none:irw=on:lcm=reverse:lwlo=on:nm=64:newcnf=on:nwc=1:stl=60:sos=on:sp=reverse_arity:updr=off:uhcvi=on_215");
      quick.push("lrs+1010_1_av=off:fde=unused:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_128");
      quick.push("dis+1003_28_acc=model:add=large:afp=10000:afq=1.1:amm=off:anc=none:bd=off:ccuc=first:fsr=off:gs=on:gsaa=from_current:ile=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence:tha=off:uwa=ground:uhcvi=on_90");
      quick.push("lrs+4_3_av=off:bd=preordered:fde=none:inw=on:ile=on:nm=64:newcnf=on:nwc=1:stl=30:tha=off:thf=on:updr=off:uhcvi=on_8");
      quick.push("lrs-11_5:4_afp=4000:afq=1.4:amm=sco:anc=none:bd=off:br=off:gs=on:gsem=off:inw=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sos=all:sp=occurrence:urr=on_1");
      quick.push("lrs+11_5:1_afr=on:afp=10000:afq=1.2:amm=off:anc=none:fsr=off:gs=on:inw=on:ile=on:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off_165");
      quick.push("dis+1003_4:1_add=large:afp=10000:afq=1.4:amm=off:anc=none:bd=off:cond=fast:fsr=off:fde=none:gs=on:ile=on:lma=on:nm=64:nwc=1.2:sas=z3:sp=reverse_arity:tha=off:urr=ec_only_19");
      quick.push("dis+1002_1_av=off:bd=off:br=off:cond=on:fsr=off:fde=unused:newcnf=on:nwc=1:sd=5:ss=axioms:st=1.2:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_8");
      quick.push("ott+1010_2_add=off:amm=sco:bd=off:bce=on:cond=fast:fsr=off:fde=unused:ile=on:nm=64:nwc=1.1:sos=all:sac=on:sp=reverse_arity_8");
      quick.push("ott-11_16_av=off:cond=fast:er=filter:fde=none:gsp=input_only:ile=on:irw=on:lcm=predicate:nm=16:nwc=1.2:sos=all:sp=reverse_arity:tha=off:thi=full:updr=off_1");
      quick.push("lrs+11_8_av=off:bs=unit_only:bsr=on:cond=on:er=filter:fsr=off:fde=unused:gsp=input_only:ile=on:nm=6:nwc=1.1:stl=30:sos=all:tha=off:uhcvi=on_2");
      quick.push("dis+10_2_add=off:amm=off:anc=none:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:ile=on:irw=on:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off:updr=off:uhcvi=on_75");
      quick.push("dis+11_5:1_av=off:br=off:cond=on:fsr=off:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=0:newcnf=on:nwc=1:tha=off:urr=on_45");
      quick.push("dis+1010_1_av=off:lma=on:newcnf=on:nwc=1:sd=4:ss=axioms:sos=on:sp=reverse_arity_197");
      quick.push("lrs+1011_3:2_add=off:afr=on:afp=10000:afq=1.2:amm=off:anc=all:bd=off:bsr=on:br=off:fde=unused:gs=on:inw=on:irw=on:nm=64:newcnf=on:nwc=1:stl=30:sp=reverse_arity:tha=off:uwa=interpreted_only:urr=on_6");
      quick.push("lrs+1002_1_av=off:bd=off:fsr=off:fde=none:nm=2:newcnf=on:nwc=1:stl=30:sp=reverse_arity:uhcvi=on_27");
      quick.push("lrs+4_5:4_av=off:bd=off:cond=on:fsr=off:irw=on:lwlo=on:nm=0:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_152");
      quick.push("lrs-4_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:cond=on:fde=unused:gs=on:gsem=off:inw=on:ile=on:irw=on:lcm=reverse:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sos=all:sp=occurrence:uwa=ground:urr=on:updr=off:uhcvi=on_132");
      quick.push("ott+1_10_av=off:ep=RSTC:fsr=off:ile=on:lma=on:newcnf=on:nwc=1:sos=on:tha=off:updr=off_268");
      quick.push("dis+2_2_afr=on:afp=100000:afq=1.2:amm=off:anc=none:bsr=on:cond=on:gs=on:gsem=on:inw=on:ile=on:irw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=1.1:sas=z3:sac=on:tha=off:updr=off_58");
      quick.push("dis+1002_2:3_av=off:bs=on:bce=on:cond=fast:ile=on:nm=2:newcnf=on:nwc=1:sp=occurrence:tha=off:thi=strong_79");
      quick.push("lrs+1002_5:4_add=large:afr=on:afp=40000:afq=2.0:anc=none:cond=on:inw=on:ile=on:nm=64:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:tha=off:updr=off_109");
      quick.push("lrs+10_50_av=off:cond=fast:fde=none:lcm=reverse:nm=64:newcnf=on:nwc=1:stl=30:sp=occurrence:tha=off:uhcvi=on_264");
      quick.push("lrs+1002_32_av=off:cond=on:fsr=off:gsp=input_only:ile=on:nm=64:newcnf=on:nwc=4:stl=30:sp=reverse_arity_1");
      quick.push("lrs+11_2:1_afp=1000:afq=1.4:amm=off:anc=none:inw=on:ile=on:irw=on:nm=64:nwc=1:stl=30:sac=on:tha=off:urr=on_73");
      quick.push("lrs+1011_2:3_av=off:bsr=on:cond=fast:fsr=off:gsp=input_only:ile=on:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1:stl=30:tha=off:updr=off_86");
      quick.push("lrs+11_1_afr=on:afp=4000:afq=1.2:amm=sco:anc=none:fsr=off:gs=on:gsem=on:ile=on:irw=on:nm=2:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:tha=off:thf=on:uwa=interpreted_only:urr=on:updr=off_53");
      quick.push("dis+11_3_afr=on:afp=40000:afq=2.0:amm=off:anc=none:bd=off:cond=fast:fsr=off:fde=unused:ile=on:lma=on:nm=64:nwc=1:sos=all:sac=on:sp=reverse_arity:tha=off_1");
      quick.push("ott+1011_4_afp=4000:afq=1.1:amm=off:anc=none:bs=unit_only:cond=fast:fsr=off:fde=none:gsp=input_only:ile=on:irw=on:nm=32:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off_45");
      quick.push("dis+11_3_av=off:cond=on:fsr=off:ile=on:irw=on:nm=64:newcnf=on:nwc=1:sp=reverse_arity:tha=off:updr=off:uhcvi=on_117");
      quick.push("ott+11_5:4_aac=none:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:bce=on:cond=on:fsr=off:fde=unused:ile=on:irw=on:lma=on:nm=6:newcnf=on:nwc=1:nicw=on:sas=z3:tha=off:updr=off_32");
      quick.push("dis-1_128_av=off:bs=on:fde=unused:ile=on:irw=on:nm=32:nwc=1.1:sos=all:tha=off:thi=full:uwa=one_side_constant:uhcvi=on_355");
      quick.push("ott+11_3:1_av=off:cond=on:er=filter:fsr=off:ile=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=all:tha=off:uhcvi=on_3");
      quick.push("ott+11_2_av=off:inw=on:ile=on:irw=on:lcm=reverse:lma=on:nm=6:nwc=1.5:sp=occurrence:updr=off_158");
      quick.push("ott+1_5:1_av=off:bs=unit_only:br=off:gs=on:gsem=off:inw=on:ile=on:nm=64:newcnf=on:nwc=1:sd=4:ss=axioms:st=1.5:sp=occurrence:tha=off:urr=on:uhcvi=on_173");
      quick.push("ott-1_3:1_av=off:bsr=on:br=off:bce=on:cond=on:fsr=off:fde=unused:irw=on:nm=2:newcnf=on:nwc=2.5:sos=on:sp=occurrence:tha=off:thi=overlap:urr=on:updr=off:uhcvi=on_148");
      quick.push("lrs-1_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:lcm=reverse:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sp=reverse_arity:tha=off:thf=on:urr=on_210");
      quick.push("lrs+10_5:4_av=off:bd=off:fsr=off:fde=none:lcm=reverse:lma=on:newcnf=on:nwc=1:stl=30:tha=off:urr=on:updr=off_173");
      quick.push("dis+1010_6_av=off:cond=on:er=filter:fsr=off:nm=64:newcnf=on:nwc=1.3:sp=reverse_arity_223");
      quick.push("dis+1_4:1_acc=on:add=large:afp=4000:afq=1.2:amm=sco:anc=none:ccuc=small_ones:ile=on:lwlo=on:nm=64:nwc=1:tha=off:urr=ec_only:updr=off_228");
      quick.push("lrs+1003_4:1_av=off:bd=preordered:cond=on:fde=unused:gs=on:ile=on:irw=on:nm=64:nwc=1.2:stl=90:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_322");
      quick.push("lrs+4_3:1_add=off:afp=1000:afq=2.0:anc=none:gs=on:gsem=on:ile=on:lma=on:nm=2:nwc=5:sas=z3:stl=30:sac=on:sp=occurrence:updr=off_8");
      quick.push("dis+10_28_av=off:cond=on:fsr=off:gsp=input_only:gs=on:ile=on:lma=on:nm=64:nwc=1:sos=all:sp=occurrence:tha=off:thf=on:updr=off_17");
      quick.push("lrs+1002_5_av=off:cond=fast:fsr=off:fde=unused:gs=on:ile=on:lma=on:lwlo=on:nm=64:nwc=1.7:stl=30:sp=reverse_arity_36");
      quick.push("lrs+11_1_av=off:bd=off:bsr=on:cond=on:fsr=off:ile=on:nm=64:newcnf=on:nwc=1:stl=30:tha=off:updr=off_197");
      return;

    case SMT_ALIA:
      return;
    case SMT_ALL:
      return;
    case SMT_AUFDTLIA:
      return;
    case SMT_AUFLIA:
      return;
    case SMT_AUFLIRA:
      return;
    case SMT_AUFNIRA:
      return;
    case SMT_BV:
      return;
    case SMT_LIA:
      return;
    case SMT_LRA:
      return;
    case SMT_NIA:
      return;
    case SMT_NRA:
      return;
    case SMT_UF:
      return;
    case SMT_UFBV:
      return;
    case SMT_UFDT:
      return;
    case SMT_UFDTLIA:
      return;
    case SMT_UFIDL:
      return;
    case SMT_UFLIA:
      return;
    case SMT_UFLRA:
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

    case SMT_UNDEFINED:
      throw UserErrorException("This version cannot be used with this logic!");
    }

} // getSchedule


#endif //!COMPILER_MSVC
