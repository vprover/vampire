/**
 * @file CASCMultiMode.cpp
 * Implements class CASCMultiMode.
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

#include "CASCMode.hpp"

#include "CASCMultiMode.hpp"

#define SLOWNESS 1.15

using namespace CASC;
using namespace std;
using namespace Lib;
using namespace Lib::Sys;
using namespace Saturation;

/**
 * The function that does all the job: reads the input files and runs
 * Vampires to solve problems.
 */
bool CASCMultiMode::perform()
{
  CALL("CASCMultiMode::perform");

  //TODO needed?
  // to prevent from terminating by time limit
  env.options->setTimeLimitInSeconds(100000);

  UIHelper::szsOutput = true;
  env.options->setProof(Options::Proof::TPTP);
  env.options->setStatistics(Options::Statistics::NONE);

  CASCMultiMode casc;

  bool resValue;
  try {
      resValue = casc.searchForProof();
  } catch (Exception& exc) {
      cerr << "% Exception at proof search level" << endl;
      exc.cry(cerr);
      System::terminateImmediately(1); //we didn't find the proof, so we return nonzero status code
  }

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

  return resValue;
} 

vstring CASCMultiMode::problemFinishedString = "##Problem finished##vn;3-d-ca-12=1;'";


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
bool CASCMultiMode::performStrategy(Shell::Property* property)
{
  CALL("CASCMultiMode::performStrategy");
  cout << "% Hi Geoff, go and have some cold beer while I am trying to solve this very hard problem!\n";

  Schedule quick;
  Schedule fallback;

  CASC::CASCMode::getSchedules(*property,quick,fallback);

  int terminationTime = env.remainingTime()/100; 
  if(terminationTime <= 0){ return false; }

  StrategySet usedSlices;
  if (runSchedule(quick,usedSlices,false,terminationTime)) {
    return true;
  }
  terminationTime = env.remainingTime()/100;
  if(terminationTime <= 0){ return false; }
  return runSchedule(fallback,usedSlices,true,terminationTime);
} // CASCMultiMode::performStrategy

/**
 * This function solves a single problem. It parses the problem, spawns a
 * writer process for output and creates a pipe to communicate with it.
 * Then it calls performStrategy(terminationTime) that performs the
 * actual proof search.
 */
bool CASCMultiMode::searchForProof()
{
  CALL("CASCMultiMode::searchForProof");

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

  UIHelper::szsOutput=true;

  return performStrategy(property);
} // CASCMultiMode::perform

static unsigned milliToDeci(unsigned timeInMiliseconds) {
  return timeInMiliseconds/100;
}

/**
 * Run a schedule. 
 * Return true if a proof was found, otherwise return false. 
 * It spawns processes by calling runSlice()
 */
bool CASCMultiMode::runSchedule(Schedule& schedule,StrategySet& used,bool fallback,int terminationTime)
{
  CALL("CASCMultiMode::runSchedule");

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
      CASCMultiMode::coutLineOutput() << "Slices left: " << slices-- << endl;
      CASCMultiMode::coutLineOutput() << "Processes available: " << processesLeft << endl << flush;
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
          cerr << "% Exception at run slice level" << endl;
          exc.cry(cerr);
          System::terminateImmediately(1); //we didn't find the proof, so we return nonzero status code
        }
        ASSERTION_VIOLATION; //the runSlice function should never return
      }
      Timer::syncClock();
      ASS(childIds.insert(childId));
      CASCMultiMode::coutLineOutput() << "slice pid "<< childId << " slice: " << sliceCode
				 << " time: " << (sliceTime/100)/10.0 << endl << flush;
      processesLeft--;
      if (!it.hasNext()) {
	break;
      }
    }

    CASCMultiMode::coutLineOutput() << "No processes available: " << endl << flush;
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
} // CASCMultiMode::runSchedule

/**
 * Wait for termination of a child 
 * return true if a proof was found
 */
bool CASCMultiMode::waitForChildAndCheckIfProofFound()
{
  CALL("CASCMultiMode::waitForChildAndCheckIfProofFound");
  ASS(!childIds.isEmpty());

  int resValue;
  pid_t finishedChild = Multiprocessing::instance()->waitForChildTermination(resValue);
#if VDEBUG
  ALWAYS(childIds.remove(finishedChild));
#endif
  if (!resValue) {
    // we have found the proof. It has been already written down by the writter child,
    CASCMultiMode::coutLineOutput() << "terminated slice pid " << finishedChild << " (success)" << endl << flush;
    return true;
  }
  // proof not found
  CASCMultiMode::coutLineOutput() << "terminated slice pid " << finishedChild << " (fail)" << endl << flush;
  return false;
} // waitForChildAndExitWhenProofFound

ofstream* CASCMultiMode::writerFileStream = 0;

void CASCMultiMode::terminatingSignalHandler(int sigNum)
{
  try {
    if (writerFileStream) {
      writerFileStream->close();
    }
  } catch (Lib::SystemFailException& ex) {
    cerr << "Process " << getpid() << " received SystemFailException in terminatingSignalHandler" << endl;
    ex.cry(cerr);
    cerr << " and will now die" << endl;
  }
  System::terminateImmediately(0);
}

/**
 * Run a slice given by its code using the specified time limit.
 */
void CASCMultiMode::runSlice(vstring sliceCode, unsigned timeLimitInMilliseconds)
{
  CALL("CASCMultiMode::runSlice");

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
void CASCMultiMode::runSlice(Options& strategyOpt)
{
  CALL("CASCMultiMode::runSlice(Option&)");

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

  env.beginOutput();
  CASCMultiMode::lineOutput() << opt.testId() << " on " << opt.problemName() << endl;
  env.endOutput();

  ProvingHelper::runVampire(*prb, opt);

  //set return value to zero if we were successful
  if (env.statistics->terminationReason == Statistics::REFUTATION) {
    resultValue=0;
  }

  System::ignoreSIGHUP(); // don't interrupt now, we need to finish printing the proof !

  env.beginOutput();
  CASCMultiMode::lineOutput() << " has result " << resultValue << endl;
  env.endOutput();
  bool outputResult = true;
  if (!resultValue) { 
    ScopedSemaphoreLocker locker(_syncSemaphore);
    locker.lock();
    if(_proofPrinted){ outputResult = false; }
    env.beginOutput();
    CASCMultiMode::lineOutput() << " outputResult is " << outputResult << " proofPrinted " << _proofPrinted << endl;
    env.endOutput();
    _proofPrinted = true; 
  }
    env.beginOutput();
    CASCMultiMode::lineOutput() << " outputResult is " << outputResult << " proofPrinted " << _proofPrinted << endl;
    env.endOutput();
  if(outputResult){
    env.beginOutput();
    UIHelper::outputResult(env.out());
    env.endOutput();
  }
  else{
    env.beginOutput();
    CASCMultiMode::lineOutput() << " found a proof after proof output" << endl;
    env.endOutput();
  }

  exit(resultValue);
} // CASCMultiMode::runSlice

/**
 * Return the intended slice time in milliseconds and assign the slice
 * vstring with chopped time limit to @b chopped.
 */
unsigned CASCMultiMode::getSliceTime(vstring sliceCode,vstring& chopped)
{
  CALL("CASCMode::getSliceTime");

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
ostream& CASCMultiMode::lineOutput()
{
  CALL("CASCMultiMode::lineOutput");
  return env.out() << "% (" << getpid() << ',' << (env.timer->elapsedMilliseconds()/100)/10.0 << ") ";
} // CASCMultiMode::lineOutput

/**
 * Start line output by writing the TPTP comment sign and the current
 * elapsed time in milliseconds to cout. Returns cout
 */
ostream& CASCMultiMode::coutLineOutput()
{
  CALL("CASCMultiMode::lineOutput");
  return cout << "% (" << getpid() << ',' << (env.timer->elapsedMilliseconds()/100)/10.0 << ") ";
} // CASCMultiMode::coutLineOutput

#endif //!COMPILER_MSVC
