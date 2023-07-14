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

#include <unistd.h>
#include <signal.h>
#include <fstream>
#include <stdio.h>
#include <cstdio>
#include <random>

#include "Saturation/ProvingHelper.hpp"

#include "Kernel/Problem.hpp"

#include "Schedules.hpp"

#include "PortfolioMode.hpp"

using namespace Lib;
using namespace CASC;

PortfolioMode::PortfolioMode() : _slowness(1.0), _syncSemaphore(2) {
  unsigned cores = System::getNumberOfCores();
  cores = cores < 1 ? 1 : cores;
  _numWorkers = min(cores, env.options->multicore());
  if(!_numWorkers)
  {
    _numWorkers = cores >= 8 ? cores - 2 : cores;
  }

  // We need the following two values because the way the semaphore class is currently implemented:
  // 1) dec is the only operation which is blocking
  // 2) dec is done in the mode SEM_UNDO, so is undone when a process terminates

  if(env.options->printProofToFile().empty()) {
    /* if the user does not ask for printing the proof to a file,
     * we generate a temp file name, in master,
     * to be filled up in the winning worker with the proof
     * and printed later by master to stdout
     * when all the workers have shut up reporting status
     * (not to get the status talking interrupt the proof printing)
     */
    _tmpFileNameForProof = tmpnam(NULL);
  }
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
#if VTIME_PROFILING
    if (env.options && env.options->timeStatistics()) {
      TimeTrace::instance().printPretty(env.out());
    }
#endif // VTIME_PROFILING
    env.endOutput();
  }

  return resValue;
}

bool PortfolioMode::searchForProof()
{
  CALL("PortfolioMode::searchForProof");

  _prb = UIHelper::getInputProblem(*env.options);

  /* CAREFUL: Make sure that the order
   * 1) getProperty, 2) normalise, 3) TheoryFinder::search
   * is the same as in profileMode (vampire.cpp)
   * also, cf. the beginning of Preprocessing::preprocess*/
  Shell::Property* property = _prb->getProperty();
  {
    TIME_TRACE(TimeTrace::PREPROCESSING);

    //we normalize now so that we don't have to do it in every child Vampire
    ScopedLet<Statistics::ExecutionPhase> phaseLet(env.statistics->phase,Statistics::NORMALIZATION);
    
    if (env.options->normalize()) { // set explicitly by CASC(SAT) and SMTCOMP modes
      Normalisation().normalise(*_prb);
    }

    // note that this is shuffleInput for the master process (for exceptional/experimental use)
    // the usual way is to have strategies request shuffling explicitly in the schedule strings
    if (env.options->shuffleInput()) {
      Shuffling().shuffle(*_prb);
    } 

    //TheoryFinder cannot cope with polymorphic input
    if(!env.property->hasPolymorphicSym()){
      TheoryFinder(_prb->units(),property).search();
    }
  }

  // now all the cpu usage will be in children, we'll just be waiting for them
  Timer::setLimitEnforcement(false);

  return prepareScheduleAndPerform(*property);
}

bool PortfolioMode::prepareScheduleAndPerform(const Shell::Property& prop)
{
  CALL("PortfolioMode::prepareScheduleAndPerform");

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
    CALL("PortfolioMode::prepareScheduleAndPerform-additionsSinceTheLastSpiderings");

    // Always try these
    addScheduleExtra(sOrig,sWithExtras,"si=on:rtra=on:rawr=on:rp=on"); // shuffling options
    addScheduleExtra(sOrig,sWithExtras,"sp=frequency");                // frequency sp; this is in casc19 but not smt18
    addScheduleExtra(sOrig,sWithExtras,"avsq=on:plsq=on");             // split queues
    addScheduleExtra(sOrig,sWithExtras,"av=on:atotf=0.5");             // turn AVATAR off

#if VHOL
    if(!prop.higherOrder()){
#endif      
      //these options are not currently HOL compatible
      addScheduleExtra(sOrig,sWithExtras,"bsd=on:fsd=on"); // subsumption demodulation
      addScheduleExtra(sOrig,sWithExtras,"to=lpo");        // lpo
#if VHOL      
    }
#endif
    // If contains integers, rationals and reals
    if(prop.props() & (Property::PR_HAS_INTEGERS | Property::PR_HAS_RATS | Property::PR_HAS_REALS)){
      addScheduleExtra(sOrig,sWithExtras,"hsm=on");             // Sets a sensible set of Joe's arithmetic rules (TACAS-21) 
      addScheduleExtra(sOrig,sWithExtras,"gve=force:asg=force:canc=force:ev=force:pum=on"); // More drastic set of rules
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
    additionsSinceTheLastSpiderings(main,schedule);
    additionsSinceTheLastSpiderings(fallback,schedule);

  } else if (env.options->schedule() == Options::Schedule::CASC_SAT) {

    schedule.loadFromIterator(main.iterFifo());
    schedule.loadFromIterator(fallback.iterFifo());
    // randomize and use the new fmb option
    addScheduleExtra(main,schedule,"si=on:rtra=on:rawr=on:rp=on:fmbksg=on");
    addScheduleExtra(fallback,schedule,"si=on:rtra=on:rawr=on:rp=on:fmbksg=on");

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
  CALL("PortfolioMode::rescaleScheduleLimits");

  Schedule::BottomFirstIterator it(sOld);
  while(it.hasNext()){
    vstring s = it.next();

    // rescale the instruction limit, if present
    size_t bidx = s.rfind(":i=");
    if (bidx == vstring::npos) {
      bidx = s.rfind("_i=");
    }
    if (bidx != vstring::npos) {
      bidx += 3; // advance past the "[:_]i=" bit
      size_t eidx = s.find_first_of(":_",bidx); // find the end of the number there
      ASS_NEQ(eidx,vstring::npos);
      vstring instrStr = s.substr(bidx,eidx-bidx);
      unsigned instr;
      ALWAYS(Int::stringToUnsignedInt(instrStr,instr));
      instr *= limit_multiplier;
      s = s.substr(0,bidx) + Lib::Int::toString(instr) + s.substr(eidx);
    }

    // do the analogous with the time limit suffix
    vstring ts = s.substr(s.find_last_of("_")+1,vstring::npos);
    unsigned time;
    ALWAYS(Lib::Int::stringToUnsignedInt(ts,time));
    vstring prefix = s.substr(0,s.find_last_of("_"));
    // Add a copy with increased time limit ...
    vstring new_time_suffix = Lib::Int::toString((int)(time*limit_multiplier));

    sNew.push(prefix + "_" + new_time_suffix);
  }
}

/**
 * Take strategy strings from @param sOld and update them by adding @param extra 
 * as additional option settings, pushing the new strings into @param sNew.
 * 
 * @author Giles, Martin
 */
void PortfolioMode::addScheduleExtra(const Schedule& sOld, Schedule& sNew, vstring extra)
{
  CALL("PortfolioMode::addScheduleExtra");

  Schedule::BottomFirstIterator it(sOld);
  while(it.hasNext()){
    vstring s = it.next();

    auto idx = s.find_last_of("_");

    vstring prefix = s.substr(0,idx); 
    vstring suffix = s.substr(idx,vstring::npos);
    vstring new_s = prefix + ((prefix.back() != '_') ? ":" : "") + extra + suffix;

    sNew.push(new_s);
  }
}

void PortfolioMode::getSchedules(const Property& prop, Schedule& quick, Schedule& fallback)
{
  CALL("PortfolioMode::getSchedules");

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

#if VHOL
  case Options::Schedule::SNAKE_TPTP_HOL:
    Schedules::getSnakeTptpHolSchedule(prop,quick);
    break;
  case Options::Schedule::SNAKE_SLH:
    Schedules::getSnakeSlhSchedule(prop,quick);
    break;
#endif

  case Options::Schedule::CASC_2019:
  case Options::Schedule::CASC:
    Schedules::getCasc2019Schedule(prop,quick,fallback);
    break;

  case Options::Schedule::CASC_SAT_2019:
  case Options::Schedule::CASC_SAT:
    Schedules::getCascSat2019Schedule(prop,quick,fallback);
    break;


  case Options::Schedule::SMTCOMP:
  case Options::Schedule::SMTCOMP_2018:
    Schedules::getSmtcomp2018Schedule(prop,quick,fallback);
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
  case Options::Schedule::STRUCT_INDUCTION:
    Schedules::getStructInductionSchedule(prop,quick,fallback);
    break;
  }
}

bool PortfolioMode::runSchedule(Schedule schedule) {
  CALL("PortfolioMode::runSchedule");
  TIME_TRACE("run schedule");

  Schedule::BottomFirstIterator it(schedule);
  Set<pid_t> processes;
  bool success = false;
  int remainingTime;
  while(Timer::syncClock(), remainingTime = env.remainingTime() / 100, remainingTime > 0)
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

      vstring code = it.next();
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
      env.beginOutput();
      Shell::addCommentSignForSZS(env.out());
      env.out()<<"Child killed by signal " << code << endl;
      env.endOutput();
      ALWAYS(processes.remove(process));
    }
  }

  // kill all running processes first
  decltype(processes)::Iterator killIt(processes);
  while(killIt.hasNext())
    Multiprocessing::instance()->killNoCheck(killIt.next(), SIGKILL);

  return success;
}

/**
 * Run a schedule.
 * Return true if a proof was found, otherwise return false.
 */
bool PortfolioMode::runScheduleAndRecoverProof(Schedule schedule)
{
  CALL("PortfolioMode::runScheduleAndRecoverProof");

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

    BYPASSING_ALLOCATOR; 
    
    ifstream input(_tmpFileNameForProof);

    bool openSucceeded = !input.fail();

    if (openSucceeded) {
      env.beginOutput();
      env.out() << input.rdbuf();
      env.endOutput();
    } else {
      if (outputAllowed()) {
        env.beginOutput();
        addCommentSignForSZS(env.out()) << "Failed to restore proof from tempfile " << _tmpFileNameForProof << endl;
        env.endOutput();
      }
    }

    //If for some reason, the proof could not be opened
    //we don't delete the proof file
    if(openSucceeded){
      remove(_tmpFileNameForProof); 
    }
  }

  return result;
}

/**
 * Return the intended slice time in deciseconds
 */
unsigned PortfolioMode::getSliceTime(const vstring &sliceCode)
{
  CALL("PortfolioMode::getSliceTime");

  unsigned pos = sliceCode.find_last_of('_');
  vstring sliceTimeStr = sliceCode.substr(pos+1);
  unsigned sliceTime;
  ALWAYS(Int::stringToUnsignedInt(sliceTimeStr,sliceTime));

  if (sliceTime == 0 && !Timer::instructionLimitingInPlace()) {
    if (outputAllowed()) {
      env.beginOutput();
      addCommentSignForSZS(env.out());
      env.out() << "WARNING: time unlimited strategy and instruction limiting not in place - attemping to translate instructions to time" << endl;
      env.endOutput();
    }

    size_t bidx = sliceCode.find(":i=");
    if (bidx == vstring::npos) {
      bidx = sliceCode.find("_i=");
      if (bidx == vstring::npos) {
        return 0; // run (essentially) forever
      }
    } // we have a valid begin index
    bidx += 3; // advance it past the "*i=" bit
    size_t eidx = sliceCode.find_first_of(":_",bidx); // find the end of the number there
    ASS_NEQ(eidx,vstring::npos);
    vstring sliceInstrStr = sliceCode.substr(bidx,eidx-bidx);
    unsigned sliceInstr;
    ALWAYS(Int::stringToUnsignedInt(sliceInstrStr,sliceInstr));
    
    // sliceTime is in deci second, we assume a roughly 2GHz CPU here
    sliceTime = sliceInstr / 200;
    if (sliceTime == 0) { sliceTime = 1; }
  }

  return _slowness * sliceTime;
} // getSliceTime

/**
 * Run a slice given by its code using the specified time limit.
 */
void PortfolioMode::runSlice(vstring sliceCode, int timeLimitInDeciseconds)
{
  CALL("PortfolioMode::runSlice");
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
    Options opt = *env.options;

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
      std::cerr << "% Exception at run slice level" << std::endl;
      e.cry(std::cerr);
    }
    System::terminateImmediately(1); // didn't find proof
  }
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

  Timer::resetInstructionMeasuring();
  Timer::setLimitEnforcement(true);

  Options opt = strategyOpt;
  //we have already performed the normalization (or don't care about it)
  opt.setNormalize(false);
  opt.setForcedOptionValues();
  opt.checkGlobalOptionConstraints();
  *env.options = opt; //just temporarily until we get rid of dependencies on env.options in solving

  if (outputAllowed()) {
    env.beginOutput();
    addCommentSignForSZS(env.out()) << opt.testId() << " on " << opt.problemName() << 
      " for (" << opt.timeLimitInDeciseconds() << "ds"<<
#ifdef __linux__
      "/" << opt.instructionLimit() << "Mi" <<
#endif
      ")" << endl;
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

  if(outputResult) { // this get only true for the first child to find a proof
    ASS(!resultValue);

    if (outputAllowed() && env.options->multicore() != 1) {
      env.beginOutput();
      addCommentSignForSZS(env.out()) << "First to succeed." << endl;
      env.endOutput();
    }

    // At the moment we only save one proof. We could potentially
    // allow multiple proofs
    vstring fname(env.options->printProofToFile());
    if (fname.empty()) {
      fname = _tmpFileNameForProof;
    }

    BYPASSING_ALLOCATOR; 
    
    ofstream output(fname.c_str());
    if (output.fail()) {
      // fallback to old printing method
      env.beginOutput();
      addCommentSignForSZS(env.out()) << "Solution printing to a file '" << fname <<  "' failed. Outputting to stdout" << endl;
      UIHelper::outputResult(env.out());
      env.endOutput();
    } else {
      UIHelper::outputResult(output);
      if (!env.options->printProofToFile().empty() && outputAllowed()) {
        env.beginOutput();
        addCommentSignForSZS(env.out()) << "Solution written to " << fname << endl;
        env.endOutput();
      }
    }
  } else if (outputAllowed()) {
    env.beginOutput();
    if (resultValue) {
      UIHelper::outputResult(env.out());
    } else if (Lib::env.options && Lib::env.options->multicore() != 1) {
      addCommentSignForSZS(env.out()) << "Also succeeded, but the first one will report." << endl;
    }
    env.endOutput();
  }

  if (outputResult) {
    _syncSemaphore.inc(SEM_LOCK); // would be also released after the processes' death, but we are polite and do it already here
  }

  STOP_CHECKING_FOR_ALLOCATOR_BYPASSES;

  exit(resultValue);
} // runSlice
