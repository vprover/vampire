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
 * @file Environment.cpp
 * Implements environment used by the current prover.
 *
 * @since 06/05/2007 Manchester
 */

#include "Debug/Tracer.hpp"

#include "Lib/Sys/SyncPipe.hpp"

#include "Indexing/TermSharing.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/OperatorType.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Timer.hpp"

#include "Environment.hpp"

namespace Lib
{

using namespace std;
using namespace Kernel;
using namespace Indexing;
using namespace Shell;

/**
 * @since 06/05/2007 Manchester
 */
Environment::Environment()
  : signature(0),
    sharing(0),
    property(0),
    maxSineLevel(1),
    predicateSineLevels(nullptr),
    colorUsed(false),
    _outputDepth(0),
    _priorityOutput(0),
    _pipe(0)
{
  START_CHECKING_FOR_ALLOCATOR_BYPASSES;

  options = new Options;
  statistics = new Statistics;  
  signature = new Signature;
  sharing = new TermSharing;
  property = new Property;

  //view comment in Signature.cpp
  signature->addEquality();
  // These functions are called here in order to ensure the order
  // of creation of these sorts. The order is VITAL. 
  //
  // A number of places in the code rely on the type constructor for
  // $i being 0, that for $o being 1 and so on.
  AtomicSort::defaultSort();
  AtomicSort::boolSort();
  AtomicSort::intSort();
  AtomicSort::realSort();
  AtomicSort::rationalSort();

  timer = Timer::instance();
  timer->start();
} // Environment::Environment

Environment::~Environment()
{
  CALL("Environment::~Environment");

  Timer::setLimitEnforcement(false);

  //in the usual cases the _outputDepth should be zero at this point, but in case of
  //thrown exceptions this might not be true.
//  ASS_EQ(_outputDepth,0);

  while(_outputDepth!=0) {
    endOutput();
  }

// #if CHECK_LEAKS
  delete sharing;
  delete signature;
  delete statistics;
  delete property;
  if (predicateSineLevels) delete predicateSineLevels;
  {
    BYPASSING_ALLOCATOR; // use of std::function in options
    delete options;
  }
// #endif
}

/**
 * If the global time limit reached set Statistics::terminationReason
 * to TIME_LIMIT and return true, otherwise return false.
 * @since 25/03/2008 Torrevieja
 */
bool Environment::timeLimitReached() const
{
  CALL("Environment::timeLimitReached");

  if (options->timeLimitInDeciseconds() &&
      timer->elapsedDeciseconds() > options->timeLimitInDeciseconds()) {
    statistics->terminationReason = Shell::Statistics::TIME_LIMIT;
    Timer::setLimitEnforcement(false);
    return true;
  }
  return false;
} // Environment::timeLimitReached

/**
 * Return remaining time in miliseconds.
 */
int Environment::remainingTime() const
{
  // If time limit is set to 0 then assume we always have a minute left
  if(options->timeLimitInDeciseconds() == 0){
    return 60000;
  }
  return options->timeLimitInDeciseconds()*100 - timer->elapsedMilliseconds();
}

/**
 * Acquire an output stream
 *
 * A process cannot hold an output stream during forking.
 */
void Environment::beginOutput()
{
  CALL("Environment::beginOutput");
  ASS_GE(_outputDepth,0);

  _outputDepth++;
  if(_outputDepth==1 && _pipe) {
    _pipe->acquireWrite();
  }
}

/**
 * Release the output stream
 */
void Environment::endOutput()
{
  CALL("Environment::endOutput");
  ASS_G(_outputDepth,0);

  _outputDepth--;
  if(_outputDepth==0) {
    if(_pipe) {
      cout.flush();
      _pipe->releaseWrite();
    }
    else {
      cout.flush();
    }
  }
}

/**
 * Return true if we have an output stream acquired
 */
bool Environment::haveOutput()
{
  CALL("Environment::haveOutput");

  return _outputDepth;
}

/**
 * Return the output stream if we have it acquired
 *
 * Process must have an output stream acquired in order to call
 * this function.
 */
ostream& Environment::out()
{
  CALL("Environment::out");
  ASS(_outputDepth);

  if(_priorityOutput) {
    return *_priorityOutput;
  }
  else if(_pipe) {
    return _pipe->out();
  }
  else {
    return cout;
  }
}

/**
 * Direct @b env.out() into @b pipe or to @b cout if @b pipe is zero
 *
 * This function cannot be called when an output is in progress.
 */
void Environment::setPipeOutput(SyncPipe* pipe)
{
  CALL("Environment::setPipeOutput");
  ASS(!haveOutput());

  _pipe=pipe;
}

void Environment::setPriorityOutput(ostream* stm)
{
  CALL("Environment::setPriorityOutput");
  ASS(!_priorityOutput || !stm);

  _priorityOutput=stm;

}

// global environment object, constructed before main() and used everywhere
Environment env;
}
