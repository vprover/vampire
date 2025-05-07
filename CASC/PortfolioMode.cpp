/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

/**
 * @file PortfolioMode.cpp
 * Implements class PortfolioMode.
 */


#include "Debug/Assertion.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Portability.hpp"
#include "Lib/Stack.hpp"
#include "Lib/System.hpp"
#include "Lib/ScopedLet.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Sys/Multiprocessing.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"
#include "Shell/Normalisation.hpp"
#include "Shell/Shuffling.hpp"
#include "Shell/TheoryFinder.hpp"

#include <limits>
#include <unistd.h>
#include <signal.h>
#include <fstream>
#include <cstdio>
#include <random>
#include <filesystem>
//only for detecting number of cores, no threading here!
#include <thread>

#include "Saturation/ProvingHelper.hpp"

#include "Kernel/Problem.hpp"

#include "Schedules.hpp"

#include "PortfolioMode.hpp"

using namespace Lib;
using namespace CASC;
using Lib::Sys::Multiprocessing;
using std::cout;
using std::cerr;
using std::endl;
namespace fs = std::filesystem;

PortfolioMode::PortfolioMode(Problem* problem) : _prb(problem), _slowness(env.options->slowness()) {
  unsigned cores = std::thread::hardware_concurrency();
  cores = cores < 1 ? 1 : cores;
  _numWorkers = std::min(cores, env.options->multicore());
  if(!_numWorkers)
  {
    _numWorkers = cores >= 8 ? cores - 2 : cores;
  }

  auto pathGiven = env.options->printProofToFile();
  if(pathGiven.empty())
    // no collision as we can't have the same PID as another Vampire *simultaneously*
    _path = fs::temp_directory_path() / ("vampire-proof-" + Int::toString(getpid()));
  else
    _path = fs::path(pathGiven);

  // the first Vampire to succeed creates the file
  // therefore: remove it first
  try {
    fs::remove(_path);
  } catch(const fs::filesystem_error &remove_error) {
    // this is not good: we can't synchronise on _path
    // attempt to output to stdout instead
    std::cerr
      << "WARNING: could not synchronise on " << _path
      << " (will output to stdout, but proof may be garbled)\n"
      << remove_error.what()
      << std::endl;
    _path.clear();
  }
}

/**
 * The function that does all the job: reads the input files and runs
 * Vampires to solve problems.
 */
bool PortfolioMode::perform(Problem* problem)
{
  PortfolioMode pm(problem);

  bool resValue;
  try {
      resValue = pm.searchForProof();
  } catch (Exception& exc) {
      cerr << "% Exception at proof search level" << endl;
      exc.cry(cerr);
      System::terminateImmediately(1); //we didn't find the proof, so we return nonzero status code
  }

  if (outputAllowed()) {
    if (resValue) {
      addCommentSignForSZS(cout);
      cout<<"Success in time "<<Timer::msToSecondsString(Timer::elapsedMilliseconds())<<endl;
    }
    else {
      addCommentSignForSZS(cout);
      cout<<"Proof not found in time "<<Timer::msToSecondsString(Timer::elapsedMilliseconds())<<endl;
      if (env.remainingTime()/100>0) {
        addCommentSignForSZS(cout);
        cout<<"SZS status GaveUp for "<<env.options->problemName()<<endl;
      }
      else {
        //From time to time we may also be terminating in the timeLimitReached()
        //function in Lib/Timer.cpp in case the time runs out. We, however, output
        //the same string there as well.
        addCommentSignForSZS(cout);
        cout<<"SZS status Timeout for "<<env.options->problemName()<<endl;
      }
    }
#if VTIME_PROFILING
    if (env.options && env.options->timeStatistics()) {
      TimeTrace::instance().printPretty(cout);
    }
#endif // VTIME_PROFILING
  }

  return resValue;
}

bool PortfolioMode::searchForProof()
{
  /* CAREFUL: Make sure that the order
   * 1) getProperty, 2) normalise, 3) TheoryFinder::search
   * is the same as in profileMode (vampire.cpp)
   * also, cf. the beginning of Preprocessing::preprocess*/
  Shell::Property* property = _prb->getProperty();
  {
    TIME_TRACE(TimeTrace::PREPROCESSING);

    //we normalize now so that we don't have to do it in every child Vampire
    ScopedLet<ExecutionPhase> phaseLet(env.statistics->phase,ExecutionPhase::NORMALIZATION);

    if (env.options->normalize()) { // set explicitly by CASC(SAT) and SMTCOMP modes
      Normalisation().normalise(*_prb);
    }

    // note that this is shuffleInput for the master process (for exceptional/experimental use)
    // the usual way is to have strategies request shuffling explicitly in the schedule strings
    if (env.options->shuffleInput()) {
      Shuffling().shuffle(*_prb);
    }

    //TheoryFinder cannot cope with polymorphic input
    if(!env.getMainProblem()->hasPolymorphicSym()){
      TheoryFinder(_prb->units(),property).search();
    }
  }

  // now all the cpu usage will be in children, we'll just be waiting for them
  Timer::disableLimitEnforcement();

  return prepareScheduleAndPerform(*property);
}

bool PortfolioMode::prepareScheduleAndPerform(const Shell::Property& prop)
{
  // this is the one and only schedule that will leave this function
  // we fill it up in various ways
  Schedule schedule;

  // take the respective schedules from our "Tablets of Stone"
  Schedule main;
  Schedule fallback;
  getSchedules(prop,main,fallback);
  
  /** 
   * The idea next is to create extra schedules based on the just loaded ones
   * mainly by adding new options that are not yet included in the schedules
   * into a copy of an official schedule to be appended after it (so as not to disturb the original).
   * 
   * The expectation is that the code below will be updated before each competition submission
   * 
   * Note that the final schedule is longer and longer with each copy,
   * so consider carefully which selected options (and combinations) to "try on top" of it.
   */

  // a (temporary) helper lambda that will go away as soon as we have new schedules from spider
  auto additionsSinceTheLastSpiderings = [&prop](const Schedule& sOrig, Schedule& sWithExtras) {
    // Always try these
    addScheduleExtra(sOrig,sWithExtras,"si=on:rtra=on:rawr=on:rp=on"); // shuffling options
    addScheduleExtra(sOrig,sWithExtras,"sp=frequency");                // frequency sp; this is in casc19 but not smt18
    addScheduleExtra(sOrig,sWithExtras,"avsq=on:plsq=on");             // split queues
    addScheduleExtra(sOrig,sWithExtras,"av=on:atotf=0.5");             // turn AVATAR off

    if(!prop.higherOrder()){
      //these options are not currently HOL compatible
      addScheduleExtra(sOrig,sWithExtras,"bsd=on:fsd=on"); // subsumption demodulation
      addScheduleExtra(sOrig,sWithExtras,"to=lpo");        // lpo
    }

    // If contains integers, rationals and reals
    if(prop.props() & (Property::PR_HAS_INTEGERS | Property::PR_HAS_RATS | Property::PR_HAS_REALS)){
      addScheduleExtra(sOrig,sWithExtras,"gve=cautious:asg=cautious:canc=cautious:ev=cautious:pum=on"); // Sets a sensible set of Joe's arithmetic rules (TACAS-21)
      addScheduleExtra(sOrig,sWithExtras,"gve=force:asg=force:canc=force:ev=force:pum=on");             // More drastic set of rules
      addScheduleExtra(sOrig,sWithExtras,"sos=theory:sstl=5");  // theory sos with non-default limit
      addScheduleExtra(sOrig,sWithExtras,"thsq=on");            // theory split queues, default
      addScheduleExtra(sOrig,sWithExtras,"thsq=on:thsqd=16");   // theory split queues, other ratio
    }
    // If contains datatypes
    if(prop.props() & Property::PR_HAS_DT_CONSTRUCTORS){
      addScheduleExtra(sOrig,sWithExtras,"gtg=exists_all:ind=struct");
      addScheduleExtra(sOrig,sWithExtras,"ind=struct:sik=one:indgen=on:indoct=on:drc=off");
      addScheduleExtra(sOrig,sWithExtras,"ind=struct:sik=one:indgen=on");
      addScheduleExtra(sOrig,sWithExtras,"ind=struct:sik=one:indoct=on");
      addScheduleExtra(sOrig,sWithExtras,"ind=struct:sik=all:indmd=1");
    }

    // If in SMT-COMP mode try guessing the goal (and adding the twee trick!)
    if(env.options->schedule() == Options::Schedule::SMTCOMP){
      addScheduleExtra(sOrig,sWithExtras,"gtg=exists_all:tgt=full");
    }
    else
    {
      // Don't try this in SMT-COMP mode as it requires a goal
      addScheduleExtra(sOrig,sWithExtras,"slsq=on");
      addScheduleExtra(sOrig,sWithExtras,"tgt=full");
    }
  };

  // now various ways of creating schedule extension based on their "age and flavour"
  if (env.options->schedule() == Options::Schedule::CASC) {

    schedule.loadFromIterator(main.iterFifo());
    schedule.loadFromIterator(fallback.iterFifo());
    addScheduleExtra(main,schedule,"si=on:rtra=on");
    addScheduleExtra(fallback,schedule,"si=on:rtra=on");

  } else if (env.options->schedule() == Options::Schedule::CASC_SAT) {

    schedule.loadFromIterator(main.iterFifo());
    schedule.loadFromIterator(fallback.iterFifo());
    // randomize and use the new fmb option
    addScheduleExtra(main,schedule,"si=on:rtra=on");
    addScheduleExtra(fallback,schedule,"si=on:rtra=on");

  } else if (env.options->schedule() == Options::Schedule::SMTCOMP) {
    // Normally we do main fallback main_extra fallback_extra
    // However, in SMTCOMP mode the fallback is universal for all
    // logics e.g. it's not very strong. Therefore, in SMTCOMP
    // mode we do main main_extra fallback fallback_extra

    schedule.loadFromIterator(main.iterFifo());
    additionsSinceTheLastSpiderings(main,schedule);
    schedule.loadFromIterator(fallback.iterFifo());
    additionsSinceTheLastSpiderings(fallback,schedule);

  } else if (env.options->schedule() == Options::Schedule::SNAKE_TPTP_UNS) {
    ASS(fallback.isEmpty());

    schedule.loadFromIterator(main.iterFifo());
    addScheduleExtra(main,schedule,"rp=on:de=on"); // random polarities, demodulation encompassment

  } else if (env.options->schedule() == Options::Schedule::SNAKE_TPTP_SAT) {
    ASS(fallback.isEmpty());

    schedule.loadFromIterator(main.iterFifo());
    addScheduleExtra(main,schedule,"rp=on:fmbksg=on:de=on"); // random polarities, demodulation encompassment for saturation, fmbksg for the fmb's
  } else {
    // all other schedules just get loaded plain

    schedule.loadFromIterator(main.iterFifo());
    schedule.loadFromIterator(fallback.iterFifo());
  }

  if (schedule.isEmpty()) {
    USER_ERROR("The schedule is empty.");
  }

  return runScheduleAndRecoverProof(std::move(schedule));
};

/**
 * Take strategy strings from @param sOld, update their time (and intruction) limit, 
 * multiplying it by @param limit_multiplier and put the new strings into @param sNew.
 * 
 * @author Giles, Martin
 */
void PortfolioMode::rescaleScheduleLimits(const Schedule& sOld, Schedule& sNew, float limit_multiplier) 
{
  ASS(limit_multiplier >= 0)
  Schedule::BottomFirstIterator it(sOld);
  auto scale = [&](auto v) {
    unsigned newV = v * limit_multiplier;
    return limit_multiplier > 0 && newV < v
       ? /* overflow */ std::numeric_limits<unsigned>::max()
       : newV;
    };
  while(it.hasNext()){
    std::string s = it.next();

    // rescale the instruction limit, if present
    size_t bidx = s.rfind(":i=");
    if (bidx == std::string::npos) {
      bidx = s.rfind("_i=");
    }
    if (bidx != std::string::npos) {
      bidx += 3; // advance past the "[:_]i=" bit
      size_t eidx = s.find_first_of(":_",bidx); // find the end of the number there
      ASS_NEQ(eidx,std::string::npos);
      std::string instrStr = s.substr(bidx,eidx-bidx);
      unsigned oldInstr;
      ALWAYS(Int::stringToUnsignedInt(instrStr,oldInstr));
      s = s.substr(0,bidx) + Lib::Int::toString(scale(oldInstr)) + s.substr(eidx);
    }

    // do the analogous with the time limit suffix
    std::string ts = s.substr(s.find_last_of("_")+1,std::string::npos);
    unsigned oldTime;
    ALWAYS(Lib::Int::stringToUnsignedInt(ts,oldTime));
    std::string prefix = s.substr(0,s.find_last_of("_"));
    // Add a copy with increased time limit ...

    std::string new_time_suffix = Lib::Int::toString(scale(oldTime));

    sNew.push(prefix + "_" + new_time_suffix);
  }
}

/**
 * Take strategy strings from @param sOld and update them by adding @param extra 
 * as additional option settings, pushing the new strings into @param sNew.
 * 
 * @author Giles, Martin
 */
void PortfolioMode::addScheduleExtra(const Schedule& sOld, Schedule& sNew, std::string extra)
{
  Schedule::BottomFirstIterator it(sOld);
  while(it.hasNext()){
    std::string s = it.next();

    auto idx = s.find_last_of("_");

    std::string prefix = s.substr(0,idx);
    std::string suffix = s.substr(idx,std::string::npos);
    std::string new_s = prefix + ((prefix.back() != '_') ? ":" : "") + extra + suffix;

    sNew.push(new_s);
  }
}

void PortfolioMode::getSchedules(const Property& prop, Schedule& quick, Schedule& fallback)
{
  switch(env.options->schedule()) {
  case Options::Schedule::FILE:
    Schedules::getScheduleFromFile(env.options->scheduleFile(), quick);
    break;

  case Options::Schedule::SNAKE_TPTP_UNS:
    Schedules::getSnakeTptpUnsSchedule(prop,quick);
    break;
  case Options::Schedule::SNAKE_TPTP_SAT:
    Schedules::getSnakeTptpSatSchedule(prop,quick);
    break;

  case Options::Schedule::CASC_2024:
  case Options::Schedule::CASC:
    Schedules::getCasc2024Schedule(prop,quick,fallback);
    break;

  case Options::Schedule::CASC_SAT_2024:
  case Options::Schedule::CASC_SAT:
    Schedules::getCascSat2024Schedule(prop,quick,fallback);
    break;

  case Options::Schedule::SMTCOMP:
  case Options::Schedule::SMTCOMP_2018:
    Schedules::getSmtcomp2018Schedule(prop,quick,fallback, /*allowUndefinedLogic=*/env.options->ignoreUnrecognizedLogic());
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
  case Options::Schedule::INDUCTION:
    Schedules::getInductionSchedule(prop,quick,fallback);
    break;
  case Options::Schedule::INTEGER_INDUCTION:
    Schedules::getIntegerInductionSchedule(prop,quick,fallback);
    break;
  case Options::Schedule::INTIND_OEIS:
    Schedules::getIntindOeisSchedule(prop,quick,fallback);
    break;
  case Options::Schedule::STRUCT_INDUCTION:
    Schedules::getStructInductionSchedule(prop,quick,fallback);
    break;
  case Options::Schedule::STRUCT_INDUCTION_TIP:
    Schedules::getStructInductionTipSchedule(prop,quick,fallback);
    break;
  }
}

bool PortfolioMode::runSchedule(Schedule schedule) {
  TIME_TRACE("run schedule");

  Schedule::BottomFirstIterator it(schedule);
  Set<pid_t> processes;
  bool success = false;
  int remainingTime;
  while(remainingTime = env.remainingTime() / 100, remainingTime > 0)
  {
    // running under capacity, wake up more tasks
    while(processes.size() < _numWorkers)
    {
      // after exhaustion we replace the schedule
      // by copies with x2 time limits and do this forever
      if(!it.hasNext()) {
        Schedule next;
        rescaleScheduleLimits(schedule, next, 2.0);
        schedule = next;
        it = Schedule::BottomFirstIterator(schedule);
      }
      ALWAYS(it.hasNext());

      std::string code = it.next();
      pid_t process = Multiprocessing::instance()->fork();
      ASS_NEQ(process, -1);
      if(process == 0)
      {
        TIME_TRACE_NEW_ROOT("child process")
        runSlice(code, remainingTime);
        ASSERTION_VIOLATION; // should not return
      }
      ALWAYS(processes.insert(process));
    }

    bool exited, signalled;
    int code;
    // sleep until process changes state
    pid_t process = Multiprocessing::instance()->poll_children(exited, signalled, code);

    /*
    cout << "Child " << process
        << " exit " << exited
        << " sig " << signalled << " code " << code << endl;
        */

    // child died, remove it from the pool and check if succeeded
    if(exited)
    {
      ALWAYS(processes.remove(process));
      if(!code)
      {
        success = true;
        break;
      }
    } else if (signalled) {
      // killed by an external agency (could be e.g. a slurm cluster killing for too much memory allocated)
      Shell::addCommentSignForSZS(cout);
      cout<<"Child killed by signal " << code << endl;
      ALWAYS(processes.remove(process));
    }
  }

  // kill all running processes first
  decltype(processes)::Iterator killIt(processes);
  while(killIt.hasNext())
    Multiprocessing::instance()->killNoCheck(killIt.next(), SIGINT);

  return success;
}

/**
 * Run a schedule.
 * Return true if a proof was found, otherwise return false.
 */
bool PortfolioMode::runScheduleAndRecoverProof(Schedule schedule)
{
  if (schedule.size() == 0)
    return false;

  UIHelper::portfolioParent = true; // to report on overall-solving-ended in Timer.cpp

  bool result = runSchedule(std::move(schedule));

  //All children have been killed. Now safe to print proof
  if(result && env.options->printProofToFile().empty()){
    /*
     * the user didn't wish a proof in the file, so we printed it to the secret tmp file
     * now it's time to restore it.
     */
    std::ifstream input(_path);

    bool openSucceeded = !input.fail();

    if (openSucceeded) {
      cout << input.rdbuf();
    } else {
      if (outputAllowed()) {
        addCommentSignForSZS(cout) << "Failed to restore proof from tempfile " << _path << endl;
      }
    }

    //If for some reason, the proof could not be opened
    //we don't delete the proof file
    if(openSucceeded){
      fs::remove(_path);
    }
  }

  return result;
}

/**
 * Return the intended slice time in deciseconds
 */
unsigned PortfolioMode::getSliceTime(const std::string &sliceCode)
{
  unsigned pos = sliceCode.find_last_of('_');
  std::string sliceTimeStr = sliceCode.substr(pos+1);
  unsigned sliceTime;
  ALWAYS(Int::stringToUnsignedInt(sliceTimeStr,sliceTime));

  if (sliceTime == 0 && !Timer::instructionLimitingInPlace()) {
    if (outputAllowed()) {
      addCommentSignForSZS(cout);
      cout << "WARNING: time unlimited strategy and instruction limiting not in place - attempting to translate instructions to time" << endl;
    }

    size_t bidx = sliceCode.find(":i=");
    if (bidx == std::string::npos) {
      bidx = sliceCode.find("_i=");
      if (bidx == std::string::npos) {
        return 0; // run (essentially) forever
      }
    } // we have a valid begin index
    bidx += 3; // advance it past the "*i=" bit
    size_t eidx = sliceCode.find_first_of(":_",bidx); // find the end of the number there
    ASS_NEQ(eidx,std::string::npos);
    std::string sliceInstrStr = sliceCode.substr(bidx,eidx-bidx);
    unsigned sliceInstr;
    ALWAYS(Int::stringToUnsignedInt(sliceInstrStr,sliceInstr));

    // sliceTime is in deci second, we assume a roughly 2GHz CPU here
    sliceTime = 1 + sliceInstr / 200; // rather round up than down (and never return 0 here)
  }

  ASS(_slowness > 0)
  unsigned res = _slowness * sliceTime;
  return _slowness >= 1 && res < sliceTime
    ? /* overflow */ std::numeric_limits<unsigned>::max()
    : res;
} // getSliceTime

/**
 * Run a slice given by its code using the specified time limit.
 */
void PortfolioMode::runSlice(std::string sliceCode, int timeLimitInDeciseconds)
{
  TIME_TRACE("run slice");

  int sliceTime = getSliceTime(sliceCode);
  if (sliceTime > timeLimitInDeciseconds
    || !sliceTime) // no limit set, i.e. "infinity"
  {
    sliceTime = timeLimitInDeciseconds;
  }

  ASS_GE(sliceTime,0);
  try
  {
    Options& opt = *env.options;

    // opt.randomSeed() would normally be inherited from the parent
    // addCommentSignForSZS(cout) << "runSlice - seed before setting: " << opt.randomSeed() << endl;
    if (env.options->randomizeSeedForPortfolioWorkers()) {
      // but here we want each worker to have their own seed
      opt.setRandomSeed(std::random_device()());
      // ... unless a strategy sets a seed explicitly, just below
    }
    opt.readFromEncodedOptions(sliceCode);
    opt.setTimeLimitInDeciseconds(sliceTime);
    int stl = opt.simulatedTimeLimit();
    if (stl) {
      opt.setSimulatedTimeLimit(int(stl * _slowness));
    }
    runSlice(opt);
  }
  catch(Exception &e)
  {
    if(outputAllowed())
    {
      cerr << "% Exception at run slice level" << endl;
      e.cry(cerr);
    }
    System::terminateImmediately(1); // didn't find proof
  }
} // runSlice

/**
 * Run a slice given by its options
 */
void PortfolioMode::runSlice(Options& opt)
{
  System::registerForSIGHUPOnParentDeath();
  UIHelper::portfolioParent=false;

  //we have already performed the normalization (or don't care about it)
  opt.setNormalize(false);
  opt.setForcedOptionValues();
  opt.checkGlobalOptionConstraints();

  if (outputAllowed()) {
    addCommentSignForSZS(cout) << opt.testId() << " on " << opt.problemName() <<
      " for (" << opt.timeLimitInDeciseconds() << "ds"<<
#if VAMPIRE_PERF_EXISTS
      "/" << opt.instructionLimit() << "Mi" <<
#endif
      ")" << endl;
  }

  Timer::reinitialise(Timer::instructionLimitingInPlace()); // timer only when done talking (otherwise output may get mangled)

  Saturation::ProvingHelper::runVampire(*_prb, opt);

  bool succeeded =
    env.statistics->terminationReason == TerminationReason::REFUTATION ||
    env.statistics->terminationReason == TerminationReason::SATISFIABLE;

  if(!succeeded) {
    if(outputAllowed())
      UIHelper::outputResult(cout);
    exit(EXIT_FAILURE);
  }

  // whether this Vampire should print a proof or not
  bool outputResult = false;

  // FILE used to synchronise multiple Vampires
  FILE *checkExists;

  // fall back to stdout if we failed to agree on `_path` above
  if(_path.empty())
    outputResult = true;
  // output to file if we get a lock
  // NB "wx": if we succeed opening here we're the first Vampire
  else if((checkExists = std::fopen(_path.c_str(), "wx"))) {
    std::fclose(checkExists);
    outputResult = true;
  }
  // we're very likely the first but can't write a proof to file for some reason
  // fall back to stdout, two proofs better than none
  else if(errno != EEXIST) {
    std::cerr
      << "WARNING: could not open proof file << " << _path
      << " - printing to stdout." << std::endl;
    _path.clear();
    outputResult = true;
  }

  // can conclude we didn't get the lock
  if(!outputResult) {
    if (Lib::env.options && Lib::env.options->multicore() != 1)
      addCommentSignForSZS(cout) << "Also succeeded, but the first one will report." << endl;

    // we succeeded in some sense, but we failed to print a proof
    // (only because the other Vampire beat us to it)
    // NB: this really cannot be EXIT_SUCCESS
    // otherwise, the parent might kill the proof-printing Vampire!
    exit(EXIT_FAILURE);
  }

  // at this point, we should be go for launch
  ASS(succeeded && outputResult)
  if (outputAllowed() && env.options->multicore() != 1)
    addCommentSignForSZS(cout) << "First to succeed." << endl;

  if (_path.empty()) {
    // we already failed above in accesssing the file (let's not try opening or reporting the empty name)
    UIHelper::outputResult(cout);
  } else {
    std::ofstream output(_path);
    if(output.fail()) {
      // failed to open file, fallback to stdout
      addCommentSignForSZS(cout) << "Solution printing to a file '" << _path <<  "' failed. Outputting to stdout" << endl;
      UIHelper::outputResult(cout);
    } else {
      UIHelper::outputResult(output);
      if(outputAllowed())
        addCommentSignForSZS(cout) << "Solution written to " << _path << endl;
    }
  }

  // could be quick_exit if we flush output?
  exit(EXIT_SUCCESS);
} // runSlice
