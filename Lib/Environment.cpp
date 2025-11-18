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

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Timer.hpp"

#include "Environment.hpp"

namespace Lib
{

/**
 * @since 06/05/2007 Manchester
 */
Environment::Environment()
  : signature(nullptr),
    sharing(nullptr),
    maxSineLevel(1),
    predicateSineLevels(nullptr),
    colorUsed(false),
    _problem(nullptr),
    _higherOrder(false)
{
  options = new Options;

  statistics = new Statistics;
  signature = new Signature;
  sharing = new Indexing::TermSharing;

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
} // Environment::Environment

Environment::~Environment()
{
  delete sharing;
  delete signature;
  delete statistics;
  delete predicateSineLevels;
  delete options;
}

/**
 * Return remaining time in milliseconds.
 */
int Environment::remainingTime() const
{
  // If time limit is set to 0 then assume we always have an hour left
  if (options->timeLimitInDeciseconds() == 0) {
    return 3600000;
  }
  return options->timeLimitInDeciseconds()*100 - Timer::elapsedMilliseconds();
}

// global environment object, constructed before main() and used everywhere
Environment env;
}
