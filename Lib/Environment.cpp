/**
 * @file Environment.cpp
 * Implements environment used by the current prover.
 *
 * @since 06/05/2007 Manchester
 */

#include "../Debug/Tracer.hpp"

#include "Timer.hpp"
#include "Environment.hpp"

#include "../Shell/Options.hpp"
#include "../Shell/Statistics.hpp"

using namespace std;
using namespace Lib;

/**
 * @since 06/05/2007 Manchester
 */
Environment::Environment()
  : options(0),
    signature(0),
    out(std::cout),
    sharing(0),
    statistics(0),
    ordering(0)
{
} // Environment::Environment

/**
 * If the global time limit reached set Statistics::terminationReason
 * to TIME_LIMIT and return true, otherwise return false.
 * @since 25/03/2008 Torrevieja
 */
bool Environment::timeLimitReached() const
{
  CALL("ProofAttempt::timeLimitReached");

  if (timer->elapsedDeciseconds() >
      options->timeLimitInDeciseconds()) {
    statistics->terminationReason = Shell::Statistics::TIME_LIMIT;
    return true;
  }
  return false;
} // Environment::timeLimitReached

