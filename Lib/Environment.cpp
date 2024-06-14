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
    maxSineLevel(1),
    predicateSineLevels(nullptr),
    colorUsed(false),
    _problem(0)
{
  options = new Options;

  // statistics calls the timer
  timer = Timer::instance();

  statistics = new Statistics;
  signature = new Signature;
  sharing = new TermSharing;

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

  tracer = 0;
} // Environment::Environment

Environment::~Environment()
{
  Timer::setLimitEnforcement(false);

  delete sharing;
  delete signature;
  delete statistics;
  if (predicateSineLevels) delete predicateSineLevels;
  delete options;
}

/**
 * If the global time limit reached set Statistics::terminationReason
 * to TIME_LIMIT and return true, otherwise return false.
 * @since 25/03/2008 Torrevieja
 */
bool Environment::timeLimitReached() const
{
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
  // If time limit is set to 0 then assume we always have an hour left
  if(options->timeLimitInDeciseconds() == 0){
    return 3600000;
  }
  return options->timeLimitInDeciseconds()*100 - timer->elapsedMilliseconds();
}

// global environment object, constructed before main() and used everywhere
Environment env;
}
