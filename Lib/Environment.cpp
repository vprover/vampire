
/*
 * File Environment.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
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
#include "Kernel/Sorts.hpp"

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
    clausePriorities(0),
    maxClausePriority(1),
    clauseSineLevels(nullptr),
    colorUsed(false),
    _outputDepth(0),
    _priorityOutput(0),
    _pipe(0)
{
  options = new Options;
  statistics = new Statistics;  
  sorts = new Sorts;
  signature = new Signature;
  sharing = new TermSharing;

  timer = Timer::instance();
  timer->start();
} // Environment::Environment

Environment::~Environment()
{
  CALL("Environment::~Environment");

  //in the usual cases the _outputDepth should be zero at this point, but in case of
  //thrown exceptions this might not be true.
//  ASS_EQ(_outputDepth,0);

  while(_outputDepth!=0) {
    endOutput();
  }

// #if CHECK_LEAKS
  delete sharing;
  delete signature;
  delete sorts;
  delete statistics;
  if(clausePriorities) delete clausePriorities; 
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
    return true;
  }
  return false;
} // Environment::timeLimitReached


/**
 * Return remaining time in miliseconds.
 */
int Environment::remainingTime() const
{
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

}
