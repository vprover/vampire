/**
 * @file Environment.cpp
 * Implements environment used by the current prover.
 *
 * @since 06/05/2007 Manchester
 */

#include "../Debug/Tracer.hpp"

#include "Timer.hpp"
#include "Exception.hpp"

#include "../Shell/Options.hpp"
#include "../Shell/Statistics.hpp"

#include "Environment.hpp"

using namespace std;
using namespace Lib;

#if COMPIT_GENERATOR
struct nullstream:
public std::ostream {
  struct nullbuf: public std::streambuf {
    int overflow(int c) { return traits_type::not_eof(c); }
  } m_sbuf;
  nullstream(): std::ios(&m_sbuf), std::ostream(&m_sbuf) {}
};
nullstream nullStream;
#endif

/**
 * @since 06/05/2007 Manchester
 */
Environment::Environment()
  : options(0),
    signature(0),
#if COMPIT_GENERATOR// && !VDEBUG
    out(nullStream),
#else
    out(std::cout),
#endif
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

void Environment::checkTimeSometime() const
{
  static int counter=0;
  counter++;
  if(counter==50000) {
    counter=0;
    if(timeLimitReached()) {
      throw TimeLimitExceededException();
    }
  }
}


/**
 * Return remaining time in miliseconds.
 */
int Environment::remainingTime() const
{
  return options->timeLimitInDeciseconds()*100 - timer->elapsedMilliseconds();
}
